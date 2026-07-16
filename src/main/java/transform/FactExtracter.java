package transform;

import java.io.File;
import java.io.InputStream;
import java.util.Arrays;
import java.util.LinkedHashSet;
import java.util.List;


import org.apache.jena.rdf.model.Model;
import org.apache.jena.rdf.model.ModelFactory;
import org.apache.jena.rdf.model.Statement;
import org.apache.jena.rdf.model.StmtIterator;
import org.apache.jena.riot.RDFDataMgr;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyCreationException;
import org.semanticweb.owlapi.model.OWLOntologyManager;

import data.Fact;
import data.Rule;


/**
 * Extract Datalog facts from RDF and OWL ontologies
 */
public class FactExtracter {

	public static void main(String[] args) {
		try {
			
			
			String testCase = "relations"; // "path"; // "sequence"; //  "dbpedia"; // "family"; // "lubm"; // claros";
										
			System.out.println("Test case: " + testCase);
			System.out.println();

			// read rules
			System.out.println("Read rules.");
			RuleReader rr = new RuleReader(new File("src/main/resources/" + testCase + "/" + testCase + ".dlog"));
			rr.ruleSizes.forEach((k, v) -> System.out.println("  Rule body size " + k + ": " + v));
			List<Rule> rules = rr.rules;
//			for (Rule r : rr.rules) {
//				System.out.println(r.toString());
//			}
			System.out.println();

			// transform Datalog rules into CHR programs
			System.out.println("Transform rules into CHR.");
//			DRedTransformer trf = new DRedTransformer(rules);
			BFTransformer trf = new BFTransformer(rules);
			String chrNoMark = trf.createCHRProgram(testCase, false);
			String chrMark = trf.createCHRProgram(testCase, true);
			System.out.println(chrNoMark);
			System.out.println(chrMark);
			

		} catch (Exception e) {
			e.printStackTrace();
		}


	}

	/**
	 * TODO
	 * 
	 * @param file
	 * @return
	 */
	public static LinkedHashSet<Fact> getFactsFromOWL(File file) {
		LinkedHashSet<Fact> facts = new LinkedHashSet<>();

		OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

		try {
			OWLOntology onto = manager.loadOntologyFromOntologyDocument(file);

			for (OWLAxiom a : onto.getAxioms()) {
				String s = a.toString();

				// facts are based on assertion axioms
				if (s.contains("Assertion")) {
					Object[] components = a.componentsWithoutAnnotations().toArray();
					// move predicate to the beginning
					Object tmp = components[1];
					components[1] = components[0];
					components[0] = tmp;

					for (int i = 0; i < components.length; i++) {
						// remove surrounding < .. >
						if (components[i].toString().startsWith("<")) {
							components[i] = components[i].toString().substring(1,
									components[i].toString().length() - 1);
						}
					}
					facts.add(new Fact(Arrays.toString(components)));
				}

			}

		} catch (OWLOntologyCreationException e) {
			e.printStackTrace();
		}

		return facts;
	}

	/**
	 * Extract facts from an RDF file
	 * 
	 * @param algorithmFile {@link File} where RDF triples are stored
	 * @param lang {@link String} that states what RDF language is used; options are
	 *             {@code "RDF/XML"}, {@code"N-TRIPLE"}, or {@code "TURTLE"}
	 * @return {@link LinkedHashSet} of {@link Fact} objects
	 */
	public static LinkedHashSet<Fact> getFactsFromRDF(File file, String lang) {
		LinkedHashSet<Fact> facts = new LinkedHashSet<>();

		Model model = ModelFactory.createDefaultModel();
		InputStream in = RDFDataMgr.open(file.getPath());
		if (in == null) {
			throw new IllegalArgumentException("File: " + file + " not found");
		}
		model.read(in, null, lang);

		StmtIterator iter = model.listStatements();
		while (iter.hasNext()) {
			Fact fact;

			Statement s = iter.next();

			String subURI = s.getSubject().getURI();
			String objURI = s.getObject().toString();
			// ignore statements with blank nodes
			if (subURI == null || objURI == null) {
				continue;
			}

			// extract predicate
			String predicate = model.shortForm(s.getPredicate().getURI());
			// extract arguments
			String subject = model.shortForm(subURI);
			String object = model.shortForm(objURI);
			// wrap literal in "..."
			if (s.getObject().isLiteral()) {
				if (!object.startsWith("\"")) {
					object = "\"" + object + "\"";
				}
			}
			// prevent that blank nodes are interpreted as variables
			if (subject.startsWith("_")) {
				subject = subject.substring(1);
			}
			if (object.startsWith("_")) {
				object = object.substring(1);
			}

			// special treatment for standard RDF properties
			if (predicate.equals("rdf:type")) {
				// subject is argument for object (class)
				fact = new Fact(object, List.of(subject));
			} else {
				fact = new Fact(predicate, List.of(subject, object));
			}

			facts.add(fact);

		}

		return facts;
	}

}
