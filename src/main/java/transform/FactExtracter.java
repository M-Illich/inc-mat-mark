package transform;

import java.io.File;
import java.io.InputStream;
import java.util.Arrays;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

/**
 * Extract Datalog facts from OWL ontologies
 */
public class FactExtracter {

	public static void main(String[] args) {

		File fileOWL = new File("src/main/resources/University0_0.owl"); // univ-bench.owl

		File fileRDF = new File("src/main/resources/clarosTest.txt");

		for (Fact f : getFactsFromOWL(fileOWL)) {
			System.out.println(f);
		}

//		for (Fact f : getFactsFromRDF(fileRDF, "TURTLE")) {
//			System.out.println(f);
//		}

	}

	/**
	 * TODO
	 * 
	 * @param file
	 * @return
	 */
	public static Set<Fact> getFactsFromOWL(File file) {
		Set<Fact> facts = new HashSet<>();

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
	 * @param file {@link File} where RDF triples are stored
	 * @param lang {@link String} that states what RDF language is used; options are
	 *             {@code "RDF/XML"}, {@code"N-TRIPLE"}, or {@code "TURTLE"}
	 * @return {@link Set} of {@link Fact} objects
	 */
	public static Set<Fact> getFactsFromRDF(File file, String lang) {
		Set<Fact> facts = new HashSet<>();

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

			// extract predicate
			String predicate = model.shortForm(s.getPredicate().getURI());
			// extract arguments
			String subject = model.shortForm(s.getSubject().getURI());
			String object = model.shortForm(s.getObject().toString());
			// wrap literal in "..."
			if (s.getObject().isLiteral()) {
				object = "\"" + object + "\"";
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
				fact = new Fact("[" + object + "," + subject + "]");
			} else {
				fact = new Fact("[" + predicate + "," + subject + "," + object + "]");
			}

			facts.add(fact);

		}

		return facts;
	}

}
