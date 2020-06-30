use std::collections::{BTreeSet, BTreeMap};
use std::io;
use std::io::{Error, ErrorKind};
use fixed::types::I40F24;

pub fn errorize<T>(msg: String) -> io::Result<T> {
    Err(Error::new(ErrorKind::Other, msg.as_str()))
}

struct Tokenizer {
    pending: String,
    symbols: BTreeSet<char>
}

impl Tokenizer {
    pub fn new(symbols: &str) -> Self {
        let mut result = Tokenizer {pending: String::new(), symbols: BTreeSet::new()};
        symbols.chars().for_each(|c| {result.symbols.insert(c);});
        result
    }

    pub fn tokenize(&mut self, text: &str) -> Vec<String> {
        let mut tokens = Vec::new();
        text.chars().for_each(|c| {
            if self.symbols.contains(&c) {
                self.add_pending(&mut tokens);
                let mut cstr = String::new();
                cstr.push(c);
                tokens.push(cstr);
            } else if c.is_whitespace() {
                self.add_pending(&mut tokens);
            } else {
                self.pending.push(c);
            }
        });
        self.add_pending(&mut tokens);
        tokens
    }

    fn add_pending(&mut self, tokens: &mut Vec<String>) {
        if self.pending.len() > 0 {
            tokens.push(self.pending.to_lowercase());
            self.pending = String::new();
        }
    }
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
}

pub struct PddlParser {
    tokens: Vec<String>,
    i: usize,
    problem: PddlProblem
}

impl PddlParser {
    pub fn parse(pddl: &str) -> io::Result<PddlProblem> {
        let mut parser = PddlParser {
            tokens: Tokenizer::new("()").tokenize(pddl),
            i: 0, problem: PddlProblem::new() };
        parser.define()?;
        Ok(parser.problem)
    }

    fn at_close(&self) -> io::Result<bool> {
        Ok(self.token()? == ")")
    }

    fn snag_predicate(&mut self) -> io::Result<Predicate> {
        self.check("(")?;
        let mut result = Predicate::new(self.snag()?);
        while !self.at_close()? {
            result.add_arg(self.snag()?);
        }
        self.check(")")?;
        Ok(result)
    }

    fn snag(&mut self) -> io::Result<String> {
        let token = self.token()?;
        let result = String::from(token);
        self.advance();
        Ok(result)
    }

    fn token(&self) -> io::Result<&str> {
        self.lookahead(0)
    }

    fn lookahead(&self, distance: usize) -> io::Result<&str> {
        let index = self.i + distance;
        match self.tokens.get(index) {
            Some(s) => Ok(s.as_str()),
            None => errorize(format!("Token index '{}'; {} tokens available", index, self.tokens.len()))
        }
    }

    fn check(&mut self, target_token: &str) -> io::Result<()> {
        let actual = self.token()?;
        if actual == target_token {
            self.advance();
            Ok(())
        } else {
            errorize(format!("Token '{}' expected, token '{}' encountered at position {}", target_token, actual, self.i))
        }
    }

    fn advance(&mut self) {
        self.advance_by(1);
    }

    fn advance_by(&mut self, distance: usize) {
        self.i += distance;
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
        self.problem.name = String::from(self.snag()?);
        self.check(")")?;
        Ok(())
    }

    fn domain(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check(":domain")?;
        self.problem.domain = String::from(self.snag()?);
        self.check(")")?;
        Ok(())
    }

    fn objects(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check(":objects")?;
        while !self.at_close()? {
            let object_name = self.snag()?;
            let object_type = if self.token()? == "-" {
                self.advance();
                self.snag()?
            } else {
                String::from("untyped")
            };
            self.problem.obj2type.insert(object_name, object_type);
        }
        self.check(")")?;
        Ok(())
    }

    fn init(&mut self) -> io::Result<()> {
        self.check("(")?;
        self.check(":init")?;
        while !self.at_close()? {
            if self.lookahead(1)? == "=" {
                self.check("(")?;
                self.check("=")?;
                let key = self.snag_predicate()?;
                let value = match self.token()?.parse::<I40F24>() {
                    Ok(value) => value,
                    Err(e) => return errorize(format!("{:?}", e))
                };
                self.advance();
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
        if self.token()? == "(" && self.lookahead(1)? == "and" {
            self.advance_by(2);
            while !self.at_close()? {
                let pred = self.snag_predicate()?;
                self.problem.goals.insert(pred);
            }
            self.advance();
        } else {
            let pred = self.snag_predicate()?;
            self.problem.goals.insert(pred);
        }
        self.check(")")?;
        Ok(())
    }

    fn metric(&mut self) -> io::Result<()> {
        if self.token()? == "(" {
            self.advance();
            self.check(":metric")?;
            let tag = self.snag()?;
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

#[cfg(test)]
mod tests {
    use crate::PddlParser;

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
}
