use std::env::args;
use std::fs::{read_dir, read_to_string, write};
use std::io;
use pddl_problem_parser::{PddlDomainParser, PddlParser};

fn main() -> io::Result<()> {
    let args = args().collect::<Vec<_>>();
    if args.len() != 2 {
        println!("Usage: pythonify domain_prob_directory");
    } else {
        let mut domains = Vec::new();
        let mut problems = Vec::new();
        for file in read_dir(args[1].as_str())? {
            let contents = read_to_string(file?.path())?;
            let tag = contents.split_whitespace().skip_while(|t| *t != "(define").skip(1).next().unwrap();
            match tag {
                "(domain" => {domains.push(contents);}
                "(problem" => {problems.push(contents);}
                wrong => println!("Not a PDDL input file; tag: {}", wrong)
            }
        }

        let domain = PddlDomainParser::parse(domains[0].as_str())?;
        let domain_filename = format!("{}.py", domain.name());
        write(domain_filename.as_str(), domain.make_python_domain())?;
        println!("Created domain operators: {}", domain_filename);

        for (i, problem) in problems.iter().enumerate() {
            let prob = PddlParser::parse(problem.as_str())?;
            let problem_filename = format!("{}_{}.py", prob.name, i);
            println!("Processing {}", problem_filename);
            write(problem_filename.as_str(), format!("from pyhop_anytime import *\n\n{}\n{}\n", prob.make_python_state(&domain), prob.make_python_goals()))?;
        }
    }
    Ok(())
}