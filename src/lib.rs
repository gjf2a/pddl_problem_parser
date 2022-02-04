use std::collections::{BTreeSet, BTreeMap};
use std::fmt::Display;
use std::io;
use fixed::types::I40F24;
use sexpr_parser::{errorize, Parser, SexprTree};
use sexpr_parser::SexprTree::{Sym, Sub};
use crate::Condition::{PosPred, NegPred, Ne, Lt, Gt, Le, Ge, Eq};
use crate::Effect::{AddPred, DelPred, Increase, Decrease};
use anyhop::Atom;

fn clean_python_name(s: &str) -> String {
    s.replace("-", "_")
}

#[derive(Clone,Debug,Ord,PartialOrd, PartialEq,Eq)]
pub struct Predicate {
    elements: Vec<String>
}

impl Predicate {
    pub fn new(tag: String) -> Self {
        Predicate { elements: vec![tag]}
    }

    pub fn add_arg(&mut self, arg: String) {
        self.elements.push(arg);
    }

    pub fn get_tag(&self) -> &str {
        self.elements[0].as_str()
    }

    pub fn num_args(&self) -> usize {
        self.elements.len() - 1
    }

    pub fn get_arg(&self, i: usize) -> &str {
        self.elements[i + 1].as_str()
    }

    pub fn make_python_dictionary_key(&self) -> String {
        if self.num_args() == 1 {
            format!("'{}'", self.get_arg(0))
        } else {
            let mut result = "(".to_string();
            for param in self.elements.iter().skip(1) {
                result.push('\'');
                result.push_str(param.as_str());
                result.push_str("',");
            }
            result.pop();
            result.push(')');
            result
        }
    }
}

#[derive(Clone,Debug)]
pub enum Metric {
    Minimize(Predicate),
    Maximize(Predicate)
}

#[derive(Clone,Debug)]
pub struct PddlProblem {
    pub name: String,
    pub domain: String,
    pub obj2type: BTreeMap<String,String>,
    pub bool_state: BTreeSet<Predicate>,
    pub i40f24_state: BTreeMap<Predicate,I40F24>,
    pub goals: BTreeSet<Predicate>,
    pub metric: Option<Metric>
}

impl PddlProblem {
    pub fn new() -> Self {
        PddlProblem {name: String::new(), domain: String::new(),
            obj2type: BTreeMap::new(), bool_state: BTreeSet::new(),
            i40f24_state: BTreeMap::new(), goals: BTreeSet::new(), metric: None}
    }

    pub fn make_python_state(&self, domain: &PddlDomain) -> String {
        let name = clean_python_name(format!("{}_state", self.name).as_str());
        let mut result = format!("{} = State('{}')\n", name, name);
        let preds_used = Self::add_python_predicates_to(name.as_str(), &mut result, &self.bool_state);
        Self::add_defaults(&mut result, name.as_str(), domain, &preds_used, &domain.predicates, "False");
        let funcs_used = Self::add_python_values_to(name.as_str(), &mut result, &self.i40f24_state);
        Self::add_defaults(&mut result, name.as_str(), domain, &funcs_used, &domain.functions, "0");
        result
    }

    fn add_defaults(result: &mut String, obj_name: &str, domain: &PddlDomain, names_used: &BTreeSet<String>, all: &BTreeMap<String,PredicateSpec>, default_value: &str) {
        for pred in all.values() {
            if !names_used.contains(pred.name.as_str()) {
                let value = if domain.num_params_for(pred.name.as_str()).unwrap() > 0 {"{}"} else {default_value};
                Self::add_state_assignment(result, obj_name, pred.name.as_str(), value);
            }
        }
    }

    pub fn make_python_goals(&self) -> String {
        let name = clean_python_name(format!("{}_goals", self.name).as_str());
        let mut result = format!("{} = State('{}')\n", name, name);
        Self::add_python_predicates_to(name.as_str(), &mut result, &self.goals);
        result
    }

    fn add_python_predicates_to(name: &str, result: &mut String, preds: &BTreeSet<Predicate>) -> BTreeSet<String> {
        let values = preds.iter().map(|p| (p.clone(), "True")).collect();
        Self::add_python_values_to(name, result, &values)
    }

    fn add_python_values_to<V: Display>(name: &str, result: &mut String, values: &BTreeMap<Predicate,V>) -> BTreeSet<String> {
        let mut names_used = BTreeSet::new();
        let pred_groups = Self::all_predicate_groups_from(values.keys());
        for (pred_family, group) in pred_groups.iter() {
            names_used.insert(pred_family.clone());
            if group.len() == 1 && group[0].num_args() == 0 {
                let value = values.get(&group[0]).unwrap();
                Self::add_state_assignment(result, name, group[0].get_tag(), value);
            } else {
                let mut dictionary = "{".to_string();
                for variant in group.iter() {
                    let value = values.get(variant).unwrap();
                    dictionary.push_str(format!("{}:{},", variant.make_python_dictionary_key(), value).as_str());
                }
                dictionary.pop();
                dictionary.push('}');
                Self::add_state_assignment(result, name, pred_family.as_str(), dictionary.as_str());
            }
        }
        names_used
    }

    fn add_state_assignment<V: Display>(target: &mut String, obj_name: &str, field_name: &str, value: V) {
        target.push_str(format!("{}.{} = {}\n", obj_name, clean_python_name(field_name), value).as_str());
    }

    fn all_predicate_groups_from<'a, I:Iterator<Item=&'a Predicate>>(preds: I) -> BTreeMap<String,Vec<Predicate>> {
        let mut result = BTreeMap::new();
        for pred in preds {
            match result.get_mut(pred.get_tag()) {
                None => {result.insert(pred.get_tag().to_string(), vec![pred.clone()]);}
                Some(entry) => {entry.push(pred.clone());}
            }
        }
        result
    }
}

pub struct PddlParser {
    parser: Parser,
    problem: PddlProblem
}

pub const UNTYPED: &str = "untyped";

impl PddlParser {
    pub fn parse(pddl: &str) -> io::Result<PddlProblem> {
        let mut parser = PddlParser {
            parser: Parser::new(pddl), problem: PddlProblem::new() };
        parser.define()?;
        Ok(parser.problem)
    }

    fn snag_predicate(&mut self) -> io::Result<Predicate> {
        let tokens = self.parser.snag_symbols()?;
        let mut result = Predicate::new(tokens[0].clone());
        for i in 1..tokens.len() {
            result.add_arg(tokens[i].clone());
        }
        Ok(result)
    }

    fn check(&mut self, s: &str) -> io::Result<()> {
        self.parser.check(s)
    }

    fn define(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check("define")?;
        self.problem()?;
        self.domain()?;
        self.objects()?;
        self.init()?;
        self.goal()?;
        self.metric()?;
        self.check(")")?;
        Ok(())
    }

    fn problem(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check("problem")?;
        self.problem.name = String::from(self.parser.snag()?);
        self.check(")")?;
        Ok(())
    }

    fn domain(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check(":domain")?;
        self.problem.domain = String::from(self.parser.snag()?);
        self.check(")")?;
        Ok(())
    }

    fn objects(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check(":objects")?;
        while !self.parser.at_close()? {
            let object_name = self.parser.snag()?;
            let object_type = if self.parser.token()? == "-" {
                self.parser.advance();
                self.parser.snag()?
            } else {
                String::from(UNTYPED)
            };
            self.problem.obj2type.insert(object_name, object_type);
        }
        self.check(")")?;
        Ok(())
    }

    fn init(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check(":init")?;
        while !self.parser.at_close()? {
            if self.parser.lookahead(1)? == "=" {
                self.check("(")?;
                self.check("=")?;
                let key = self.snag_predicate()?;
                let value = match self.parser.token()?.parse::<I40F24>() {
                    Ok(value) => value,
                    Err(e) => return errorize(format!("{:?}", e))
                };
                self.parser.advance();
                self.check(")")?;
                self.problem.i40f24_state.insert(key, value);
            } else {
                let pred = self.snag_predicate()?;
                self.problem.bool_state.insert(pred);
            }
        }
        self.check(")")?;
        Ok(())
    }

    fn goal(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check(":goal")?;
        if self.parser.token()? == "(" && self.parser.lookahead(1)? == "and" {
            self.parser.advance_by(2);
            while !self.parser.at_close()? {
                let pred = self.snag_predicate()?;
                self.problem.goals.insert(pred);
            }
            self.parser.advance();
        } else {
            let pred = self.snag_predicate()?;
            self.problem.goals.insert(pred);
        }
        self.check(")")?;
        Ok(())
    }

    fn metric(&mut self) -> io::Result<()> {
        if self.parser.token()? == "(" {
            self.parser.advance();
            self.check(":metric")?;
            let tag = self.parser.snag()?;
            let predicate = self.snag_predicate()?;
            self.problem.metric = Some(match tag.as_str() {
                "minimize" => Metric::Minimize(predicate),
                "maximize" => Metric::Maximize(predicate),
                _ => return errorize(format!("Unrecognized metric tag: {}", tag))
            });
            self.check(")")?;
        }
        Ok(())
    }
}

pub struct PddlDomainParser {
    domain: PddlDomain
}

impl PddlDomainParser {
    pub fn parse(pddl: &str) -> io::Result<PddlDomain> {
        let mut parser = PddlDomainParser { domain: PddlDomain::new() };
        parser.define(&Parser::build_parse_tree(pddl)?)?;
        Ok(parser.domain)
    }

    fn define(&mut self, tree: &SexprTree) -> io::Result<()> {
        match tree {
            Sub(syms)=> {
                check(&syms, 0, "define")?;
                for i in 1..syms.len() {
                    match syms[i].head() {
                        None => {},
                        Some(tag) => match tag.as_str() {
                            ":requirements" => {},
                            ":types" => {
                                let mut listing = syms[i].flatten();
                                listing.drain(1..).for_each(|t| self.domain.add_type(t));
                            },
                            ":predicates" => process_pred_list(":predicates", &syms[i], &mut self.domain.predicates)?,
                            ":functions" => process_pred_list(":functions", &syms[i], &mut self.domain.functions)?,
                            ":action" => self.process_action(&syms[i])?,
                            "domain" => match &syms[i] {
                                Sym(s) => return errorize(format!("Incorrect domain naming: {}", s)),
                                Sub(v) => self.domain.name = v[1].head().unwrap()
                            },
                            _ => return errorize(format!("Unrecognized tag: \"{}\"; i: {}", tag, i))
                        }
                    }
                }
            },
            Sym(sym)=> {
                return errorize(format!("\"{}\": No domain details defined.", sym))
            }
        }
        Ok(())
    }

    fn process_action(&mut self, symbols: &SexprTree) -> io::Result<()> {
        let name;
        let mut params = Option::None;
        let mut preconditions = Vec::new();
        let mut effects = Vec::new();
        match symbols {
            Sym(_) => return errorize(format!("Not a proper :action specification")),
            Sub(v) => {
                check(&v, 0, ":action")?;
                match v.get(1) {
                    None => return errorize(format!("Action has no name")),
                    Some(s) => match s.head() {
                        None => return errorize(format!("Action has a null name")),
                        Some(s) => name = s
                    }
                };
                for i in (2..v.len()).step_by(2) {
                    match &v[i] {
                        Sub(_) => return errorize(format!("No tag: {:?}", v[i])),
                        Sym(s) => match s.as_str() {
                            ":parameters" => {
                                match v.get(i+1) {
                                    None => return errorize(format!("No parameters declared")),
                                    Some(param_tree) =>
                                        params = Some(ParamSpec::new(&param_tree.flatten())?)
                                };
                            },
                            ":precondition" => compound_parse(&v, i+1, &mut preconditions, |t| Condition::from(t), "precondition")?,
                            ":effect" => compound_parse(&v, i+1, &mut effects, |t| Effect::from(t), "effect")?,
                            _ => return errorize(format!("Unrecognized tag: {}; i: {}", s, i))
                        }
                    }
                }
            }
        }
        match params {
            None => errorize(format!("No parameters supplied")),
            Some(params) => {
                let mut action = ActionSpec {name, params, preconditions, effects};
                action.propagate_param_types();
                self.domain.actions.insert(action.name.clone(), action);
                Ok(())
            }
        }
    }
}

fn check(parsed: &Vec<SexprTree>, i: usize, target: &str) -> io::Result<()> {
    match parsed.get(i).unwrap_or(&SexprTree::sym("")) {
        Sub(_) => errorize(format!("Expected symbol \"{}\", received a list", target)),
        Sym(parsed) => {
            if parsed.as_str() == target {
                Ok(())
            } else {
                errorize(format!("Symbol \"{}\" does not match expected symbol \"{}\"", parsed, target))
            }
        }
    }
}

fn process_pred_list(tag: &str, symbols: &SexprTree, storage: &mut BTreeMap<String,PredicateSpec>) -> io::Result<()> {
    match symbols {
        Sym(_) => return errorize(format!("Nothing here")),
        Sub(sym_list) => {
            check(&sym_list, 0, tag)?;
            for i in 1..sym_list.len() {
                let pred_spec = PredicateSpec::from_symbols(&sym_list[i].flatten())?;
                storage.insert(pred_spec.name.clone(), pred_spec);
            }
        }
    }
    Ok(())
}

fn compound_parse<T,F:Fn(&SexprTree)->io::Result<T>>(v: &Vec<SexprTree>, i: usize, repository: &mut Vec<T>, parser: F, tag: &str) -> io::Result<()> {
    match v.get(i) {
        None => return errorize(format!("No {}s declared", tag)),
        Some(precond_tree) =>
            match precond_tree {
                Sym(s) => return errorize(format!("{}: Not a {}", s, tag)),
                Sub(v) => if let Some(s) = v.get(0) {
                    if s.is("and") {
                        for p in 1..v.len() {
                            repository.push(parser(&v[p])?);
                        }
                    } else {
                        repository.push(parser(precond_tree)?);
                    }
                } else {
                    return errorize(format!("No {}s", tag));
                }
            }
    }
    Ok(())
}

fn decode_compound_subtree<T,F:Fn(&str,&SexprTree,Option<&SexprTree>,Option<&SexprTree>)->io::Result<T>>(tree: &SexprTree, parser: F) -> io::Result<T> {
    match tree {
        Sym(s) => errorize(format!("{}: Not a Condition", s)),
        Sub(v) => match v.get(0) {
            None => errorize(format!("No content to Condition")),
            Some(st) => match st {
                Sym(s) => parser(s.as_str(), tree, v.get(1), v.get(2)),
                Sub(_) => errorize(format!("Condition starts with a list"))
            }
        }
    }
}

#[derive(Clone,Debug)]
pub struct PredicateSpec {
    name: String,
    params: ParamSpec
}

impl PredicateSpec {
    pub fn from_symbols(symbols: &Vec<String>) -> io::Result<Self> {
        Ok(PredicateSpec {
            name: symbols[0].clone(), params: ParamSpec::new(&symbols[1..])?})
    }

    pub fn from_tree(tree: &SexprTree) -> io::Result<Self> {
        PredicateSpec::from_symbols(&tree.flatten())
    }

    pub fn propagate_types(&mut self, symbols2types: &BTreeMap<String,String>) {
        self.params.propagate_types(symbols2types);
    }

    pub fn make_python_getter(&self, if_not_present: &str) -> String {
        let mut python_symbol = format!("state.{}", clean_python_name(self.name.as_str()));
        match self.params.param_list.len() {
            2..=usize::MAX => {
                python_symbol.push_str(".get((");
                for param in self.params.param_list.iter() {
                    python_symbol.push_str(format!("{},", param).as_str());
                }
                python_symbol.pop();
                python_symbol.push_str(format!("), {})", if_not_present).as_str());
            }
            1 => {
                python_symbol.push_str(format!(".get({}, {})", self.params.param_list[0], if_not_present).as_str());
            }
            _ => {}
        }
        python_symbol
    }

    pub fn make_python_symbol(&self) -> String {
        let mut python_symbol = format!("state.{}", clean_python_name(self.name.as_str()));
        match self.params.param_list.len() {
            2..=usize::MAX => {
                python_symbol.push_str("[(");
                for param in self.params.param_list.iter() {
                    python_symbol.push_str(format!("{},", param).as_str());
                }
                python_symbol.pop();
                python_symbol.push_str(")]");
            }
            1 => {
                python_symbol.push_str(format!("[{}]", self.params.param_list[0]).as_str());
            }
            _ => {}
        }
        python_symbol
    }
}

#[derive(Clone,Debug)]
pub struct ParamSpec {
    symbol2type: BTreeMap<String,String>,
    param_list: Vec<String>
}

impl ParamSpec {
    pub fn type_of(&self, symbol: &str) -> Option<&String> {
        self.symbol2type.get(symbol)
    }

    pub fn propagate_types(&mut self, symbols2types: &BTreeMap<String,String>) {
        for (symbol, typ) in self.symbol2type.iter_mut() {
            match symbols2types.get(symbol) {
                None => {},
                Some(t) => *typ = t.clone()
            }
        }
    }

    pub fn new(params: &[String]) -> io::Result<Self> {
        let mut symbols = Vec::new();
        let mut types = Vec::new();
        let mut i = 0;
        while i < params.len() {
            let param = params[i].clone();
            let mut had_type = false;
            if let Some(next) = params.get(i+1) {
                if next == "-" {
                    match params.get(i+2) {
                        None => return errorize(format!("Error parsing parameters: \"-\" not followed by a type")),
                        Some(param_type) => {
                            types.push(param_type.clone());
                            i += 2;
                            had_type = true;
                        }
                    }
                }
            }
            symbols.push(param);
            i += 1;
            if !had_type {
                types.push(String::from(UNTYPED));
            }
        }

        let mut result = ParamSpec {symbol2type: BTreeMap::new(), param_list: symbols.clone()};
        result.resolve_duplicate_types(&symbols, &types);
        Ok(result)
    }

    pub fn python_param(&self) -> String {
        let mut result = String::new();
        for param in self.param_list.iter() {
            result.push_str(", ");
            result.push_str(param);
        }
        result
    }

    fn resolve_duplicate_types(&mut self, symbols: &Vec<String>, types: &Vec<String>) {
        match types.last() {
            None => {},
            Some(t) => {
                self.symbol2type.insert(symbols[symbols.len() - 1].clone(), t.clone());
                let mut trailing_type = t.clone();
                for i in (0..types.len() - 1).rev() {
                    self.symbol2type.insert(symbols[i].clone(), if types[i].as_str() == UNTYPED {
                        trailing_type.clone()
                    } else {
                        trailing_type = types[i].clone();
                        types[i].clone()
                    });
                }
            }
        }
    }
}

#[derive(Clone,Debug)]
pub struct ActionSpec {
    name: String,
    params: ParamSpec,
    preconditions: Vec<Condition>,
    effects: Vec<Effect>
}

impl ActionSpec {
    fn propagate_param_types(&mut self) {
        for c in self.preconditions.iter_mut() {
            c.propagate_types(&self.params.symbol2type);
        }

        for e in self.effects.iter_mut() {
            e.propagate_types(&self.params.symbol2type);
        }
    }

    pub fn make_python_function(&self) -> String {
        format!("def {}(state{}):\n    if {}:\n{}        return state\n",
                clean_python_name(self.name.as_str()), self.params.python_param(), self.make_python_preconditions(),
                self.make_python_effects())
    }

    fn make_python_preconditions(&self) -> String {
        if self.preconditions.is_empty() {
            String::from("True")
        } else {
            let mut result = self.preconditions[0].make_python_expression();
            for c in self.preconditions.iter().skip(1) {
                result.push_str(" and ");
                result.push_str(c.make_python_expression().as_str());
            }
            result
        }
    }

    fn make_python_effects(&self) -> String {
        let mut result = String::new();
        for e in self.effects.iter() {
            result.push_str("        ");
            result.push_str(e.make_python_effect().as_str());
            result.push('\n');
        }
        result
    }
}

#[derive(Clone,Debug)]
pub enum Condition {
    PosPred(PredicateSpec),
    NegPred(PredicateSpec),
    Eq(PredicateSpec,PredicateSpec),
    Ne(PredicateSpec,PredicateSpec),
    Lt(PredicateSpec,PredicateSpec),
    Gt(PredicateSpec,PredicateSpec),
    Le(PredicateSpec,PredicateSpec),
    Ge(PredicateSpec,PredicateSpec)
}

impl Condition {
    pub fn from(tree: &SexprTree) -> io::Result<Self> {
        decode_compound_subtree(tree, |s, v, a, b| Ok(match s {
            "not" => Condition::from(a.unwrap())?.flip(),
            "=" => Eq(PredicateSpec::from_tree(a.unwrap())?, PredicateSpec::from_tree(b.unwrap())?),
            ">=" => Ge(PredicateSpec::from_tree(a.unwrap())?, PredicateSpec::from_tree(b.unwrap())?),
            "<=" => Le(PredicateSpec::from_tree(a.unwrap())?, PredicateSpec::from_tree(b.unwrap())?),
            "<" => Lt(PredicateSpec::from_tree(a.unwrap())?, PredicateSpec::from_tree(b.unwrap())?),
            ">" => Gt(PredicateSpec::from_tree(a.unwrap())?, PredicateSpec::from_tree(b.unwrap())?),
            _ => PosPred(PredicateSpec::from_symbols(&v.flatten())?)
        }))
    }

    pub fn propagate_types(&mut self, symbols2types: &BTreeMap<String,String>) {
        match self {
            PosPred(s) => s.propagate_types(symbols2types),
            NegPred(s) => s.propagate_types(symbols2types),
            Eq(a,b) => {a.propagate_types(symbols2types); b.propagate_types(symbols2types);},
            Ne(a,b) => {a.propagate_types(symbols2types); b.propagate_types(symbols2types);},
            Lt(a,b) => {a.propagate_types(symbols2types); b.propagate_types(symbols2types);},
            Gt(a,b) => {a.propagate_types(symbols2types); b.propagate_types(symbols2types);},
            Le(a,b) => {a.propagate_types(symbols2types); b.propagate_types(symbols2types);},
            Ge(a,b) => {a.propagate_types(symbols2types); b.propagate_types(symbols2types);}
        }
    }

    pub fn flip(&self) -> Self {
        match self {
            PosPred(s) => NegPred(s.clone()),
            NegPred(s) => PosPred(s.clone()),
            Eq(a,b) => Ne(a.clone(), b.clone()),
            Ne(a,b) => Eq(a.clone(), b.clone()),
            Lt(a,b) => Ge(a.clone(), b.clone()),
            Gt(a,b) => Le(a.clone(), b.clone()),
            Le(a,b) => Gt(a.clone(), b.clone()),
            Ge(a,b) => Lt(a.clone(), b.clone())
        }
    }

    pub fn make_python_expression(&self) -> String {
        match self {
            PosPred(s) => s.make_python_getter("False"),
            NegPred(s) => format!("not {}", s.make_python_getter("False")),
            Eq(s1, s2) => format!("{} == {}", s1.make_python_symbol(), s2.make_python_symbol()),
            Ne(s1, s2) => format!("{} != {}", s1.make_python_symbol(), s2.make_python_symbol()),
            Lt(s1, s2) => format!("{} < {}", s1.make_python_symbol(), s2.make_python_symbol()),
            Gt(s1, s2) => format!("{} > {}", s1.make_python_symbol(), s2.make_python_symbol()),
            Le(s1, s2) => format!("{} <= {}", s1.make_python_symbol(), s2.make_python_symbol()),
            Ge(s1, s2) => format!("{} >= {}", s1.make_python_symbol(), s2.make_python_symbol())
        }
    }
}

#[derive(Clone,Debug)]
pub enum Effect {
    AddPred(PredicateSpec),
    DelPred(PredicateSpec),
    Increase(PredicateSpec,PredicateSpec),
    Decrease(PredicateSpec,PredicateSpec)
}

impl Effect {
    pub fn from(tree: &SexprTree) -> io::Result<Self> {
        decode_compound_subtree(tree, |s, v, a, b| Ok(match s {
            "not" => DelPred(PredicateSpec::from_tree(a.unwrap())?),
            "increase" => Increase(PredicateSpec::from_tree(a.unwrap())?, PredicateSpec::from_tree(b.unwrap())?),
            "decrease" => Decrease(PredicateSpec::from_tree(a.unwrap())?, PredicateSpec::from_tree(b.unwrap())?),
            _ => AddPred(PredicateSpec::from_symbols(&v.flatten())?)
        }))
    }

    pub fn propagate_types(&mut self, symbols2types: &BTreeMap<String,String>) {
        match self {
            AddPred(s) => s.propagate_types(symbols2types),
            DelPred(s) => s.propagate_types(symbols2types),
            Increase(a,b) => {a.propagate_types(symbols2types); b.propagate_types(symbols2types);},
            Decrease(a,b) => {a.propagate_types(symbols2types); b.propagate_types(symbols2types);}
        }
    }

    pub fn make_python_effect(&self) -> String {
        match self {
            AddPred(s) => format!("{} = True", s.make_python_symbol()),
            DelPred(s) => format!("{} = False", s.make_python_symbol()),
            Increase(s1, s2) => format!("{} += {}", s1.make_python_symbol(), s2.make_python_symbol()),
            Decrease(s1, s2) => format!("{} -= {}", s1.make_python_symbol(), s2.make_python_symbol())
        }
    }
}

#[derive(Clone,Debug)]
pub struct PddlDomain {
    name: String,
    types: BTreeSet<String>,
    predicates: BTreeMap<String,PredicateSpec>,
    functions: BTreeMap<String,PredicateSpec>,
    actions: BTreeMap<String,ActionSpec>
}

impl PddlDomain {
    pub fn new() -> Self {
        PddlDomain {name: String::new(), types: BTreeSet::new(), predicates: BTreeMap::new(),
            functions: BTreeMap::new(), actions: BTreeMap::new()}
    }

    pub fn name(&self) -> &str {
        self.name.as_str()
    }

    pub fn num_params_for(&self, predicate_name: &str) -> Option<usize> {
        self.predicates.get(predicate_name)
            .or(self.functions.get(predicate_name))
            .map(|p| p.params.param_list.len())
    }

    pub fn add_type(&mut self, t: String) {
        self.types.insert(t);
    }

    pub fn add_predicate(&mut self, p: PredicateSpec) {
        self.predicates.insert(p.name.clone(), p);
    }

    pub fn add_function(&mut self, f: PredicateSpec) {
        self.functions.insert(f.name.clone(), f);
    }

    pub fn add_action(&mut self, a: ActionSpec) {
        self.actions.insert(a.name.clone(), a);
    }

    pub fn make_python_domain(&self) -> String {
        let mut result = String::new();
        for action in self.actions.values() {
            result.push_str(action.make_python_function().as_str());
            result.push_str("\n\n");
        }
        result.replace("?", "")
    }
}
/*
pub struct DomainEncoderDecoder {
    obj2id: BTreeMap<String,usize>,
    pred2id: BTreeMap<String,usize>,
    func2id: BTreeMap<String,usize>,
    act2id: BTreeMap<String,(usize,usize)>
}

impl DomainEncoderDecoder {
    pub fn new(domain: &PddlDomain, problem: &PddlProblem) -> Self {
        let mut result = DomainEncoderDecoder {obj2id: BTreeMap::new(), pred2id: BTreeMap::new(),
            func2id: BTreeMap::new(), act2id: BTreeMap::new()};
        for obj in &problem.obj2type {
            result.obj2id.insert(obj.0.clone(), result.obj2id.len());
        }
        for pred in &domain.predicates {
            result.pred2id.insert(pred.0.clone(), result.pred2id.len());
        }
        for func in &domain.functions {
            result.func2id.insert(func.0.clone(), result.func2id.len());
        }
        for act in &domain.actions {
            result.act2id.insert(act.0.clone(), result.act2id.len());
        }
        result
    }
}

#[derive(Copy,Clone,Eq,PartialEq,Ord,PartialOrd)]
pub enum EncPred {
    OneArg(usize,usize),
    TwoArgs(usize,usize,usize),
    ThreeArgs(usize,usize,usize,usize),
    FourArgs(usize,usize,usize,usize,usize),
    FiveArgs(usize,usize,usize,usize,usize,usize)
}

pub struct EncodedState {
    true_preds: BTreeSet<EncPred>,
    func_values: BTreeMap<EncPred,I40F24>,
    op_preconds: Vec,
    op_effects: Vec
}

pub enum EncOp {
    OneArg(usize,usize),
    TwoArgs(usize,usize,usize),
    ThreeArgs(usize,usize,usize,usize),
    FourArgs(usize,usize,usize,usize,usize),
    FiveArgs(usize,usize,usize,usize,usize,usize)
}

impl Operator for EncOp {
    type S = EncodedState;

    fn attempt_update(&self, state: &mut Self::S) -> bool {
        unimplemented!()
    }
}
*/

#[cfg(test)]
mod tests {
    use crate::{PddlParser, PddlDomainParser};

    #[test]
    fn blocks_1() {
        let pddl = "(define (problem BLOCKS-2-0)
(:domain BLOCKS)
(:objects A B)
(:init (clear a) (clear b) (ontable a) (ontable b) (handempty))
(:goal (on a b)))";
        let parsed = PddlParser::parse(pddl).unwrap();
        assert_eq!(format!("{:?}", parsed), r#"PddlProblem { name: "blocks-2-0", domain: "blocks", obj2type: {"a": "untyped", "b": "untyped"}, bool_state: {Predicate { elements: ["clear", "a"] }, Predicate { elements: ["clear", "b"] }, Predicate { elements: ["handempty"] }, Predicate { elements: ["ontable", "a"] }, Predicate { elements: ["ontable", "b"] }}, i40f24_state: {}, goals: {Predicate { elements: ["on", "a", "b"] }}, metric: None }"#);
    }

    #[test]
    fn blocks_2() {
        let pddl = "(define (problem BLOCKS-4-2)
(:domain BLOCKS)
(:objects B D C A )
(:INIT (CLEAR A) (CLEAR C) (CLEAR D) (ONTABLE A) (ONTABLE B) (ONTABLE D)
 (ON C B) (HANDEMPTY))
(:goal (AND (ON A B) (ON B C) (ON C D)))
)";
        let parsed = PddlParser::parse(pddl).unwrap();
        assert_eq!(format!("{:?}", parsed), r#"PddlProblem { name: "blocks-4-2", domain: "blocks", obj2type: {"a": "untyped", "b": "untyped", "c": "untyped", "d": "untyped"}, bool_state: {Predicate { elements: ["clear", "a"] }, Predicate { elements: ["clear", "c"] }, Predicate { elements: ["clear", "d"] }, Predicate { elements: ["handempty"] }, Predicate { elements: ["on", "c", "b"] }, Predicate { elements: ["ontable", "a"] }, Predicate { elements: ["ontable", "b"] }, Predicate { elements: ["ontable", "d"] }}, i40f24_state: {}, goals: {Predicate { elements: ["on", "a", "b"] }, Predicate { elements: ["on", "b", "c"] }, Predicate { elements: ["on", "c", "d"] }}, metric: None }"#);
    }

    #[test]
    fn satellite_1() {
        let pddl = "(define (problem strips-sat-x-1)
(:domain satellite)
(:objects
	satellite0 - satellite
	instrument0 - instrument
	image1 - mode
	spectrograph2 - mode
	thermograph0 - mode
	Star0 - direction
	GroundStation1 - direction
	GroundStation2 - direction
	Phenomenon3 - direction
	Phenomenon4 - direction
	Star5 - direction
	Phenomenon6 - direction
)
(:init
	(supports instrument0 thermograph0)
	(calibration_target instrument0 GroundStation2)
	(on_board instrument0 satellite0)
	(power_avail satellite0)
	(pointing satellite0 Phenomenon6)
	(= (data_capacity satellite0) 1000)
	(= (fuel satellite0) 112)
	(= (data Phenomenon3 image1) 22)
	(= (data Phenomenon4 image1) 120)
	(= (data Star5 image1) 203)
	(= (data Phenomenon6 image1) 144)
	(= (data Phenomenon3 spectrograph2) 125)
	(= (data Phenomenon4 spectrograph2) 196)
	(= (data Star5 spectrograph2) 68)
	(= (data Phenomenon6 spectrograph2) 174)
	(= (data Phenomenon3 thermograph0) 136)
	(= (data Phenomenon4 thermograph0) 134)
	(= (data Star5 thermograph0) 273)
	(= (data Phenomenon6 thermograph0) 219)
	(= (slew_time GroundStation1 Star0) 18.17)
	(= (slew_time Star0 GroundStation1) 18.17)
	(= (slew_time GroundStation2 Star0) 38.61)
	(= (slew_time Star0 GroundStation2) 38.61)
	(= (slew_time GroundStation2 GroundStation1) 68.04)
	(= (slew_time GroundStation1 GroundStation2) 68.04)
	(= (slew_time Phenomenon3 Star0) 14.29)
	(= (slew_time Star0 Phenomenon3) 14.29)
	(= (slew_time Phenomenon3 GroundStation1) 89.48)
	(= (slew_time GroundStation1 Phenomenon3) 89.48)
	(= (slew_time Phenomenon3 GroundStation2) 33.94)
	(= (slew_time GroundStation2 Phenomenon3) 33.94)
	(= (slew_time Phenomenon4 Star0) 35.01)
	(= (slew_time Star0 Phenomenon4) 35.01)
	(= (slew_time Phenomenon4 GroundStation1) 31.79)
	(= (slew_time GroundStation1 Phenomenon4) 31.79)
	(= (slew_time Phenomenon4 GroundStation2) 39.73)
	(= (slew_time GroundStation2 Phenomenon4) 39.73)
	(= (slew_time Phenomenon4 Phenomenon3) 25.72)
	(= (slew_time Phenomenon3 Phenomenon4) 25.72)
	(= (slew_time Star5 Star0) 36.56)
	(= (slew_time Star0 Star5) 36.56)
	(= (slew_time Star5 GroundStation1) 8.59)
	(= (slew_time GroundStation1 Star5) 8.59)
	(= (slew_time Star5 GroundStation2) 62.86)
	(= (slew_time GroundStation2 Star5) 62.86)
	(= (slew_time Star5 Phenomenon3) 10.18)
	(= (slew_time Phenomenon3 Star5) 10.18)
	(= (slew_time Star5 Phenomenon4) 64.5)
	(= (slew_time Phenomenon4 Star5) 64.5)
	(= (slew_time Phenomenon6 Star0) 77.07)
	(= (slew_time Star0 Phenomenon6) 77.07)
	(= (slew_time Phenomenon6 GroundStation1) 17.63)
	(= (slew_time GroundStation1 Phenomenon6) 17.63)
	(= (slew_time Phenomenon6 GroundStation2) 50.73)
	(= (slew_time GroundStation2 Phenomenon6) 50.73)
	(= (slew_time Phenomenon6 Phenomenon3) 14.75)
	(= (slew_time Phenomenon3 Phenomenon6) 14.75)
	(= (slew_time Phenomenon6 Phenomenon4) 2.098)
	(= (slew_time Phenomenon4 Phenomenon6) 2.098)
	(= (slew_time Phenomenon6 Star5) 29.32)
	(= (slew_time Star5 Phenomenon6) 29.32)
	(= (data-stored) 0)
	(= (fuel-used) 0)
)
(:goal (and
	(have_image Phenomenon4 thermograph0)
	(have_image Star5 thermograph0)
	(have_image Phenomenon6 thermograph0)
))
(:metric minimize (fuel-used))

)";
        let parsed = PddlParser::parse(pddl).unwrap();
        assert_eq!(format!("{:?}", parsed), r#"PddlProblem { name: "strips-sat-x-1", domain: "satellite", obj2type: {"groundstation1": "direction", "groundstation2": "direction", "image1": "mode", "instrument0": "instrument", "phenomenon3": "direction", "phenomenon4": "direction", "phenomenon6": "direction", "satellite0": "satellite", "spectrograph2": "mode", "star0": "direction", "star5": "direction", "thermograph0": "mode"}, bool_state: {Predicate { elements: ["calibration_target", "instrument0", "groundstation2"] }, Predicate { elements: ["on_board", "instrument0", "satellite0"] }, Predicate { elements: ["pointing", "satellite0", "phenomenon6"] }, Predicate { elements: ["power_avail", "satellite0"] }, Predicate { elements: ["supports", "instrument0", "thermograph0"] }}, i40f24_state: {Predicate { elements: ["data", "phenomenon3", "image1"] }: 22, Predicate { elements: ["data", "phenomenon3", "spectrograph2"] }: 125, Predicate { elements: ["data", "phenomenon3", "thermograph0"] }: 136, Predicate { elements: ["data", "phenomenon4", "image1"] }: 120, Predicate { elements: ["data", "phenomenon4", "spectrograph2"] }: 196, Predicate { elements: ["data", "phenomenon4", "thermograph0"] }: 134, Predicate { elements: ["data", "phenomenon6", "image1"] }: 144, Predicate { elements: ["data", "phenomenon6", "spectrograph2"] }: 174, Predicate { elements: ["data", "phenomenon6", "thermograph0"] }: 219, Predicate { elements: ["data", "star5", "image1"] }: 203, Predicate { elements: ["data", "star5", "spectrograph2"] }: 68, Predicate { elements: ["data", "star5", "thermograph0"] }: 273, Predicate { elements: ["data-stored"] }: 0, Predicate { elements: ["data_capacity", "satellite0"] }: 1000, Predicate { elements: ["fuel", "satellite0"] }: 112, Predicate { elements: ["fuel-used"] }: 0, Predicate { elements: ["slew_time", "groundstation1", "groundstation2"] }: 68.04, Predicate { elements: ["slew_time", "groundstation1", "phenomenon3"] }: 89.48, Predicate { elements: ["slew_time", "groundstation1", "phenomenon4"] }: 31.79, Predicate { elements: ["slew_time", "groundstation1", "phenomenon6"] }: 17.63, Predicate { elements: ["slew_time", "groundstation1", "star0"] }: 18.17, Predicate { elements: ["slew_time", "groundstation1", "star5"] }: 8.59, Predicate { elements: ["slew_time", "groundstation2", "groundstation1"] }: 68.04, Predicate { elements: ["slew_time", "groundstation2", "phenomenon3"] }: 33.94, Predicate { elements: ["slew_time", "groundstation2", "phenomenon4"] }: 39.73, Predicate { elements: ["slew_time", "groundstation2", "phenomenon6"] }: 50.73, Predicate { elements: ["slew_time", "groundstation2", "star0"] }: 38.61, Predicate { elements: ["slew_time", "groundstation2", "star5"] }: 62.86, Predicate { elements: ["slew_time", "phenomenon3", "groundstation1"] }: 89.48, Predicate { elements: ["slew_time", "phenomenon3", "groundstation2"] }: 33.94, Predicate { elements: ["slew_time", "phenomenon3", "phenomenon4"] }: 25.72, Predicate { elements: ["slew_time", "phenomenon3", "phenomenon6"] }: 14.75, Predicate { elements: ["slew_time", "phenomenon3", "star0"] }: 14.29, Predicate { elements: ["slew_time", "phenomenon3", "star5"] }: 10.18, Predicate { elements: ["slew_time", "phenomenon4", "groundstation1"] }: 31.79, Predicate { elements: ["slew_time", "phenomenon4", "groundstation2"] }: 39.73, Predicate { elements: ["slew_time", "phenomenon4", "phenomenon3"] }: 25.72, Predicate { elements: ["slew_time", "phenomenon4", "phenomenon6"] }: 2.098, Predicate { elements: ["slew_time", "phenomenon4", "star0"] }: 35.01, Predicate { elements: ["slew_time", "phenomenon4", "star5"] }: 64.5, Predicate { elements: ["slew_time", "phenomenon6", "groundstation1"] }: 17.63, Predicate { elements: ["slew_time", "phenomenon6", "groundstation2"] }: 50.73, Predicate { elements: ["slew_time", "phenomenon6", "phenomenon3"] }: 14.75, Predicate { elements: ["slew_time", "phenomenon6", "phenomenon4"] }: 2.098, Predicate { elements: ["slew_time", "phenomenon6", "star0"] }: 77.07, Predicate { elements: ["slew_time", "phenomenon6", "star5"] }: 29.32, Predicate { elements: ["slew_time", "star0", "groundstation1"] }: 18.17, Predicate { elements: ["slew_time", "star0", "groundstation2"] }: 38.61, Predicate { elements: ["slew_time", "star0", "phenomenon3"] }: 14.29, Predicate { elements: ["slew_time", "star0", "phenomenon4"] }: 35.01, Predicate { elements: ["slew_time", "star0", "phenomenon6"] }: 77.07, Predicate { elements: ["slew_time", "star0", "star5"] }: 36.56, Predicate { elements: ["slew_time", "star5", "groundstation1"] }: 8.59, Predicate { elements: ["slew_time", "star5", "groundstation2"] }: 62.86, Predicate { elements: ["slew_time", "star5", "phenomenon3"] }: 10.18, Predicate { elements: ["slew_time", "star5", "phenomenon4"] }: 64.5, Predicate { elements: ["slew_time", "star5", "phenomenon6"] }: 29.32, Predicate { elements: ["slew_time", "star5", "star0"] }: 36.56}, goals: {Predicate { elements: ["have_image", "phenomenon4", "thermograph0"] }, Predicate { elements: ["have_image", "phenomenon6", "thermograph0"] }, Predicate { elements: ["have_image", "star5", "thermograph0"] }}, metric: Some(Minimize(Predicate { elements: ["fuel-used"] })) }"#);
    }

    #[test]
    fn blocks_domain() {
        let pddl = "(define (domain BLOCKS)
  (:requirements :strips)
  (:predicates (on ?x ?y)
	       (ontable ?x)
	       (clear ?x)
	       (handempty)
	       (holding ?x)
	       )

  (:action pick-up
	     :parameters (?x)
	     :precondition (and (clear ?x) (ontable ?x) (handempty))
	     :effect
	     (and (not (ontable ?x))
		   (not (clear ?x))
		   (not (handempty))
		   (holding ?x)))

  (:action put-down
	     :parameters (?x)
	     :precondition (holding ?x)
	     :effect
	     (and (not (holding ?x))
		   (clear ?x)
		   (handempty)
		   (ontable ?x)))
  (:action stack
	     :parameters (?x ?y)
	     :precondition (and (holding ?x) (clear ?y))
	     :effect
	     (and (not (holding ?x))
		   (not (clear ?y))
		   (clear ?x)
		   (handempty)
		   (on ?x ?y)))
  (:action unstack
	     :parameters (?x ?y)
	     :precondition (and (on ?x ?y) (clear ?x) (handempty))
	     :effect
	     (and (holding ?x)
		   (clear ?y)
		   (not (clear ?x))
		   (not (handempty))
		   (not (on ?x ?y)))))";
        let parsed = PddlDomainParser::parse(pddl).unwrap();
        assert_eq!(format!("{:?}", parsed), r#"PddlDomain { name: "blocks", types: {}, predicates: {"clear": PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }, "handempty": PredicateSpec { name: "handempty", params: ParamSpec { symbol2type: {}, param_list: [] } }, "holding": PredicateSpec { name: "holding", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }, "on": PredicateSpec { name: "on", params: ParamSpec { symbol2type: {"?x": "untyped", "?y": "untyped"}, param_list: ["?x", "?y"] } }, "ontable": PredicateSpec { name: "ontable", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }}, functions: {}, actions: {"pick-up": ActionSpec { name: "pick-up", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] }, preconditions: [PosPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), PosPred(PredicateSpec { name: "ontable", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), PosPred(PredicateSpec { name: "handempty", params: ParamSpec { symbol2type: {}, param_list: [] } })], effects: [DelPred(PredicateSpec { name: "ontable", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), DelPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), DelPred(PredicateSpec { name: "handempty", params: ParamSpec { symbol2type: {}, param_list: [] } }), AddPred(PredicateSpec { name: "holding", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } })] }, "put-down": ActionSpec { name: "put-down", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] }, preconditions: [PosPred(PredicateSpec { name: "holding", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } })], effects: [DelPred(PredicateSpec { name: "holding", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), AddPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), AddPred(PredicateSpec { name: "handempty", params: ParamSpec { symbol2type: {}, param_list: [] } }), AddPred(PredicateSpec { name: "ontable", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } })] }, "stack": ActionSpec { name: "stack", params: ParamSpec { symbol2type: {"?x": "untyped", "?y": "untyped"}, param_list: ["?x", "?y"] }, preconditions: [PosPred(PredicateSpec { name: "holding", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), PosPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?y": "untyped"}, param_list: ["?y"] } })], effects: [DelPred(PredicateSpec { name: "holding", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), DelPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?y": "untyped"}, param_list: ["?y"] } }), AddPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), AddPred(PredicateSpec { name: "handempty", params: ParamSpec { symbol2type: {}, param_list: [] } }), AddPred(PredicateSpec { name: "on", params: ParamSpec { symbol2type: {"?x": "untyped", "?y": "untyped"}, param_list: ["?x", "?y"] } })] }, "unstack": ActionSpec { name: "unstack", params: ParamSpec { symbol2type: {"?x": "untyped", "?y": "untyped"}, param_list: ["?x", "?y"] }, preconditions: [PosPred(PredicateSpec { name: "on", params: ParamSpec { symbol2type: {"?x": "untyped", "?y": "untyped"}, param_list: ["?x", "?y"] } }), PosPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), PosPred(PredicateSpec { name: "handempty", params: ParamSpec { symbol2type: {}, param_list: [] } })], effects: [AddPred(PredicateSpec { name: "holding", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), AddPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?y": "untyped"}, param_list: ["?y"] } }), DelPred(PredicateSpec { name: "clear", params: ParamSpec { symbol2type: {"?x": "untyped"}, param_list: ["?x"] } }), DelPred(PredicateSpec { name: "handempty", params: ParamSpec { symbol2type: {}, param_list: [] } }), DelPred(PredicateSpec { name: "on", params: ParamSpec { symbol2type: {"?x": "untyped", "?y": "untyped"}, param_list: ["?x", "?y"] } })] }} }"#);
        println!("{}", parsed.make_python_domain());
    }

    #[test]
    fn satellite_domain() {
        let pddl = "(define (domain satellite)
  (:requirements :typing :fluents :equality)
 (:types satellite direction instrument mode)
 (:predicates
               (on_board ?i - instrument ?s - satellite)
	       (supports ?i - instrument ?m - mode)
	       (pointing ?s - satellite ?d - direction)
	       (power_avail ?s - satellite)
	       (power_on ?i - instrument)
	       (calibrated ?i - instrument)
	       (have_image ?d - direction ?m - mode)
	       (calibration_target ?i - instrument ?d - direction))



  (:functions (data_capacity ?s - satellite)
	      (data ?d - direction ?m - mode)
		(slew_time ?a ?b - direction)
		(data-stored)
		(fuel ?s - satellite)
		(fuel-used)
  )

  (:action turn_to
   :parameters (?s - satellite ?d_new - direction ?d_prev - direction)
   :precondition (and (pointing ?s ?d_prev)
                   (not (= ?d_new ?d_prev))
		(>= (fuel ?s) (slew_time ?d_new ?d_prev))
              )
   :effect (and  (pointing ?s ?d_new)
                 (not (pointing ?s ?d_prev))
		(decrease (fuel ?s) (slew_time ?d_new ?d_prev))
		(increase (fuel-used) (slew_time ?d_new ?d_prev))
           )
  )


  (:action switch_on
   :parameters (?i - instrument ?s - satellite)

   :precondition (and (on_board ?i ?s)
                      (power_avail ?s)
                 )
   :effect (and (power_on ?i)
                (not (calibrated ?i))
                (not (power_avail ?s))
           )

  )


  (:action switch_off
   :parameters (?i - instrument ?s - satellite)

   :precondition (and (on_board ?i ?s)
                      (power_on ?i)
                  )
   :effect (and (not (power_on ?i))
                (power_avail ?s)
           )
  )

  (:action calibrate
   :parameters (?s - satellite ?i - instrument ?d - direction)
   :precondition (and (on_board ?i ?s)
		      (calibration_target ?i ?d)
                      (pointing ?s ?d)
                      (power_on ?i)
                  )
   :effect (calibrated ?i)
  )


  (:action take_image
   :parameters (?s - satellite ?d - direction ?i - instrument ?m - mode)
   :precondition (and (calibrated ?i)
                      (on_board ?i ?s)
                      (supports ?i ?m)
                      (power_on ?i)
                      (pointing ?s ?d)
                      (power_on ?i)
			  (>= (data_capacity ?s) (data ?d ?m))
               )
   :effect (and (decrease (data_capacity ?s) (data ?d ?m)) (have_image ?d ?m)
		(increase (data-stored) (data ?d ?m)))
  )
)

";
        let parsed = PddlDomainParser::parse(pddl).unwrap();
        assert_eq!(format!("{:?}", parsed), r#"PddlDomain { name: "satellite", types: {"direction", "instrument", "mode", "satellite"}, predicates: {"calibrated": PredicateSpec { name: "calibrated", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } }, "calibration_target": PredicateSpec { name: "calibration_target", params: ParamSpec { symbol2type: {"?d": "direction", "?i": "instrument"}, param_list: ["?i", "?d"] } }, "have_image": PredicateSpec { name: "have_image", params: ParamSpec { symbol2type: {"?d": "direction", "?m": "mode"}, param_list: ["?d", "?m"] } }, "on_board": PredicateSpec { name: "on_board", params: ParamSpec { symbol2type: {"?i": "instrument", "?s": "satellite"}, param_list: ["?i", "?s"] } }, "pointing": PredicateSpec { name: "pointing", params: ParamSpec { symbol2type: {"?d": "direction", "?s": "satellite"}, param_list: ["?s", "?d"] } }, "power_avail": PredicateSpec { name: "power_avail", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } }, "power_on": PredicateSpec { name: "power_on", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } }, "supports": PredicateSpec { name: "supports", params: ParamSpec { symbol2type: {"?i": "instrument", "?m": "mode"}, param_list: ["?i", "?m"] } }}, functions: {"data": PredicateSpec { name: "data", params: ParamSpec { symbol2type: {"?d": "direction", "?m": "mode"}, param_list: ["?d", "?m"] } }, "data-stored": PredicateSpec { name: "data-stored", params: ParamSpec { symbol2type: {}, param_list: [] } }, "data_capacity": PredicateSpec { name: "data_capacity", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } }, "fuel": PredicateSpec { name: "fuel", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } }, "fuel-used": PredicateSpec { name: "fuel-used", params: ParamSpec { symbol2type: {}, param_list: [] } }, "slew_time": PredicateSpec { name: "slew_time", params: ParamSpec { symbol2type: {"?a": "direction", "?b": "direction"}, param_list: ["?a", "?b"] } }}, actions: {"calibrate": ActionSpec { name: "calibrate", params: ParamSpec { symbol2type: {"?d": "direction", "?i": "instrument", "?s": "satellite"}, param_list: ["?s", "?i", "?d"] }, preconditions: [PosPred(PredicateSpec { name: "on_board", params: ParamSpec { symbol2type: {"?i": "instrument", "?s": "satellite"}, param_list: ["?i", "?s"] } }), PosPred(PredicateSpec { name: "calibration_target", params: ParamSpec { symbol2type: {"?d": "direction", "?i": "instrument"}, param_list: ["?i", "?d"] } }), PosPred(PredicateSpec { name: "pointing", params: ParamSpec { symbol2type: {"?d": "direction", "?s": "satellite"}, param_list: ["?s", "?d"] } }), PosPred(PredicateSpec { name: "power_on", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } })], effects: [AddPred(PredicateSpec { name: "calibrated", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } })] }, "switch_off": ActionSpec { name: "switch_off", params: ParamSpec { symbol2type: {"?i": "instrument", "?s": "satellite"}, param_list: ["?i", "?s"] }, preconditions: [PosPred(PredicateSpec { name: "on_board", params: ParamSpec { symbol2type: {"?i": "instrument", "?s": "satellite"}, param_list: ["?i", "?s"] } }), PosPred(PredicateSpec { name: "power_on", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } })], effects: [DelPred(PredicateSpec { name: "power_on", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } }), AddPred(PredicateSpec { name: "power_avail", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } })] }, "switch_on": ActionSpec { name: "switch_on", params: ParamSpec { symbol2type: {"?i": "instrument", "?s": "satellite"}, param_list: ["?i", "?s"] }, preconditions: [PosPred(PredicateSpec { name: "on_board", params: ParamSpec { symbol2type: {"?i": "instrument", "?s": "satellite"}, param_list: ["?i", "?s"] } }), PosPred(PredicateSpec { name: "power_avail", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } })], effects: [AddPred(PredicateSpec { name: "power_on", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } }), DelPred(PredicateSpec { name: "calibrated", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } }), DelPred(PredicateSpec { name: "power_avail", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } })] }, "take_image": ActionSpec { name: "take_image", params: ParamSpec { symbol2type: {"?d": "direction", "?i": "instrument", "?m": "mode", "?s": "satellite"}, param_list: ["?s", "?d", "?i", "?m"] }, preconditions: [PosPred(PredicateSpec { name: "calibrated", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } }), PosPred(PredicateSpec { name: "on_board", params: ParamSpec { symbol2type: {"?i": "instrument", "?s": "satellite"}, param_list: ["?i", "?s"] } }), PosPred(PredicateSpec { name: "supports", params: ParamSpec { symbol2type: {"?i": "instrument", "?m": "mode"}, param_list: ["?i", "?m"] } }), PosPred(PredicateSpec { name: "power_on", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } }), PosPred(PredicateSpec { name: "pointing", params: ParamSpec { symbol2type: {"?d": "direction", "?s": "satellite"}, param_list: ["?s", "?d"] } }), PosPred(PredicateSpec { name: "power_on", params: ParamSpec { symbol2type: {"?i": "instrument"}, param_list: ["?i"] } }), Ge(PredicateSpec { name: "data_capacity", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } }, PredicateSpec { name: "data", params: ParamSpec { symbol2type: {"?d": "direction", "?m": "mode"}, param_list: ["?d", "?m"] } })], effects: [Decrease(PredicateSpec { name: "data_capacity", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } }, PredicateSpec { name: "data", params: ParamSpec { symbol2type: {"?d": "direction", "?m": "mode"}, param_list: ["?d", "?m"] } }), AddPred(PredicateSpec { name: "have_image", params: ParamSpec { symbol2type: {"?d": "direction", "?m": "mode"}, param_list: ["?d", "?m"] } }), Increase(PredicateSpec { name: "data-stored", params: ParamSpec { symbol2type: {}, param_list: [] } }, PredicateSpec { name: "data", params: ParamSpec { symbol2type: {"?d": "direction", "?m": "mode"}, param_list: ["?d", "?m"] } })] }, "turn_to": ActionSpec { name: "turn_to", params: ParamSpec { symbol2type: {"?d_new": "direction", "?d_prev": "direction", "?s": "satellite"}, param_list: ["?s", "?d_new", "?d_prev"] }, preconditions: [PosPred(PredicateSpec { name: "pointing", params: ParamSpec { symbol2type: {"?d_prev": "direction", "?s": "satellite"}, param_list: ["?s", "?d_prev"] } }), Ne(PredicateSpec { name: "?d_new", params: ParamSpec { symbol2type: {}, param_list: [] } }, PredicateSpec { name: "?d_prev", params: ParamSpec { symbol2type: {}, param_list: [] } }), Ge(PredicateSpec { name: "fuel", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } }, PredicateSpec { name: "slew_time", params: ParamSpec { symbol2type: {"?d_new": "direction", "?d_prev": "direction"}, param_list: ["?d_new", "?d_prev"] } })], effects: [AddPred(PredicateSpec { name: "pointing", params: ParamSpec { symbol2type: {"?d_new": "direction", "?s": "satellite"}, param_list: ["?s", "?d_new"] } }), DelPred(PredicateSpec { name: "pointing", params: ParamSpec { symbol2type: {"?d_prev": "direction", "?s": "satellite"}, param_list: ["?s", "?d_prev"] } }), Decrease(PredicateSpec { name: "fuel", params: ParamSpec { symbol2type: {"?s": "satellite"}, param_list: ["?s"] } }, PredicateSpec { name: "slew_time", params: ParamSpec { symbol2type: {"?d_new": "direction", "?d_prev": "direction"}, param_list: ["?d_new", "?d_prev"] } }), Increase(PredicateSpec { name: "fuel-used", params: ParamSpec { symbol2type: {}, param_list: [] } }, PredicateSpec { name: "slew_time", params: ParamSpec { symbol2type: {"?d_new": "direction", "?d_prev": "direction"}, param_list: ["?d_new", "?d_prev"] } })] }} }"#);
        println!("{}", parsed.make_python_domain());
    }
}
