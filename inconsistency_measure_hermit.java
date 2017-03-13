package inconsistency_measure;

import java.io.File;
import java.io.FileOutputStream;
import java.io.PrintStream;
import java.text.DecimalFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashSet;
import java.util.NoSuchElementException;
import java.util.Set;

import org.semanticweb.HermiT.Configuration;
import org.semanticweb.HermiT.Reasoner.ReasonerFactory;
import org.semanticweb.owl.explanation.api.Explanation;
import org.semanticweb.owl.explanation.api.ExplanationGenerator;
import org.semanticweb.owl.explanation.impl.blackbox.checker.InconsistentOntologyExplanationGeneratorFactory;
import org.semanticweb.owlapi.apibinding.OWLManager;
import org.semanticweb.owlapi.model.AddAxiom;
import org.semanticweb.owlapi.model.AxiomType;
import org.semanticweb.owlapi.model.OWLAsymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLAxiom;
import org.semanticweb.owlapi.model.OWLClass;
import org.semanticweb.owlapi.model.OWLClassAssertionAxiom;
import org.semanticweb.owlapi.model.OWLDataFactory;
import org.semanticweb.owlapi.model.OWLDifferentIndividualsAxiom;
import org.semanticweb.owlapi.model.OWLDisjointClassesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLDisjointUnionAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentClassesAxiom;
import org.semanticweb.owlapi.model.OWLEquivalentObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseFunctionalObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLInverseObjectPropertiesAxiom;
import org.semanticweb.owlapi.model.OWLIrreflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLNamedIndividual;
import org.semanticweb.owlapi.model.OWLNegativeObjectPropertyAssertionAxiom;
//import org.semanticweb.owlapi.model.OWLObjectComplementOf;
import org.semanticweb.owlapi.model.OWLObjectProperty;
import org.semanticweb.owlapi.model.OWLObjectPropertyAssertionAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyDomainAxiom;
import org.semanticweb.owlapi.model.OWLObjectPropertyRangeAxiom;
import org.semanticweb.owlapi.model.OWLOntology;
import org.semanticweb.owlapi.model.OWLOntologyManager;
import org.semanticweb.owlapi.model.OWLReflexiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLSameIndividualAxiom;
import org.semanticweb.owlapi.model.OWLSubClassOfAxiom;
import org.semanticweb.owlapi.model.OWLSubObjectPropertyOfAxiom;
import org.semanticweb.owlapi.model.OWLSymmetricObjectPropertyAxiom;
import org.semanticweb.owlapi.model.OWLTransitiveObjectPropertyAxiom;
import org.semanticweb.owlapi.model.RemoveAxiom;
import org.semanticweb.owlapi.reasoner.InconsistentOntologyException;
import org.semanticweb.owlapi.reasoner.OWLReasoner;

public class inconsistency_measure_hermit {

	public static void main(String[] args) throws Exception {

		long startTime = System.currentTimeMillis();

		try {
			// System.out.println(System.getProperty("line.separator"));
			File file = new File("output_hermit_.txt");
			FileOutputStream fos = new FileOutputStream(file);
			PrintStream ps = new PrintStream(fos);
			System.setOut(ps);

			System.err.close();

			ArrayList<Integer> explanationSizeList = new ArrayList<>();
			ArrayList<Set<OWLAxiom>> MCKcandidate = new ArrayList<Set<OWLAxiom>>();

			float onePerSizeOfM;
			float sizeOfM;

			float sumOfSize = 0;

			HashSet<OWLAxiom> MIKAxiomSet = new HashSet<OWLAxiom>();
			HashSet<OWLClass> MIKClassSet = new HashSet<OWLClass>();
			HashSet<OWLNamedIndividual> MIKIndividualSet = new HashSet<OWLNamedIndividual>();
			HashSet<OWLObjectProperty> MIKObjectPropertySet = new HashSet<OWLObjectProperty>();
			HashSet<OWLAxiom> topBottom = new HashSet<OWLAxiom>();

			Set<OWLClass> inconsistentClass = null;
			Set<OWLNamedIndividual> inconsistentIndividual = null;
			Set<OWLObjectProperty> inconsistentObjectProperty = null;

			HashSet<OWLAxiom> ontologyAxiomSet = new HashSet<OWLAxiom>(3000000, 1000000F);

			File inputOntologyFile = new File("examples/knowledgebaseK4.owl");
			ReasonerFactory rf = new ReasonerFactory();

			OWLOntologyManager manager = OWLManager.createOWLOntologyManager();

			OWLDataFactory df = manager.getOWLDataFactory();

			OWLOntology ontology = manager.loadOntologyFromOntologyDocument(inputOntologyFile);

			Configuration configuration = new Configuration();
			configuration.throwInconsistentOntologyException = false;
			OWLReasoner reasoner = rf.createReasoner(ontology, configuration);

			System.out.println(
					"Is ontology (file name: " + inputOntologyFile + ") consistent? " + reasoner.isConsistent());

			ExplanationGenerator<OWLAxiom> explainInconsistency = new InconsistentOntologyExplanationGeneratorFactory(
					rf, 1000L).createExplanationGenerator(ontology);

			Set<Explanation<OWLAxiom>> explanations = explainInconsistency
					.getExplanations(df.getOWLSubClassOfAxiom(df.getOWLThing(), df.getOWLNothing()));
			System.out.println("Explanation of inconsistency (MI(K)): " + explanations);

			Set<OWLAxiom> ontologyAxiomsCausingUnsatisfiable = new HashSet<OWLAxiom>();

			Set<OWLSubClassOfAxiom> OWLSubClassOfAxiomSet = ontology.getAxioms(AxiomType.SUBCLASS_OF);
			for (OWLSubClassOfAxiom OWLSubClassOf : OWLSubClassOfAxiomSet) {
				ontologyAxiomSet.add(OWLSubClassOf);
			}

			Set<OWLEquivalentClassesAxiom> OWLEquivalentClassesAxiomSet = ontology
					.getAxioms(AxiomType.EQUIVALENT_CLASSES);
			for (OWLEquivalentClassesAxiom OWLEquivalentClasses : OWLEquivalentClassesAxiomSet) {
				ontologyAxiomSet.add(OWLEquivalentClasses);
			}

			Set<OWLDisjointClassesAxiom> OWLDisjointClassesAxiomSet = ontology.getAxioms(AxiomType.DISJOINT_CLASSES);
			for (OWLDisjointClassesAxiom OWLDisjointClasses : OWLDisjointClassesAxiomSet) {
				ontologyAxiomSet.add(OWLDisjointClasses);
			}

			Set<OWLDisjointUnionAxiom> OWLDisjointUnionAxiomSet = ontology.getAxioms(AxiomType.DISJOINT_UNION);
			for (OWLDisjointUnionAxiom OWLDisjointUnion : OWLDisjointUnionAxiomSet) {
				ontologyAxiomSet.add(OWLDisjointUnion);
			}

			Set<OWLDifferentIndividualsAxiom> OWLDifferentIndividualsAxiomSet = ontology
					.getAxioms(AxiomType.DIFFERENT_INDIVIDUALS);
			for (OWLDifferentIndividualsAxiom OWLDifferentIndividuals : OWLDifferentIndividualsAxiomSet) {
				ontologyAxiomSet.add(OWLDifferentIndividuals);
			}

			Set<OWLSameIndividualAxiom> OWLSameIndividualAxiomSet = ontology.getAxioms(AxiomType.SAME_INDIVIDUAL);
			for (OWLSameIndividualAxiom OWLSameIndividual : OWLSameIndividualAxiomSet) {
				ontologyAxiomSet.add(OWLSameIndividual);
			}

			Set<OWLClassAssertionAxiom> OWLClassAssertionAxiomSet = ontology.getAxioms(AxiomType.CLASS_ASSERTION);
			for (OWLClassAssertionAxiom OWLClassAssertion : OWLClassAssertionAxiomSet) {
				ontologyAxiomSet.add(OWLClassAssertion);
			}

			Set<OWLObjectPropertyAssertionAxiom> OWLObjectPropertyAssertionAxiomSet = ontology
					.getAxioms(AxiomType.OBJECT_PROPERTY_ASSERTION);
			for (OWLObjectPropertyAssertionAxiom OWLObjectPropertyAssertion : OWLObjectPropertyAssertionAxiomSet) {
				ontologyAxiomSet.add(OWLObjectPropertyAssertion);
			}

			Set<OWLNegativeObjectPropertyAssertionAxiom> OWLNegativeObjectPropertyAssertionAxiomSet = ontology
					.getAxioms(AxiomType.NEGATIVE_OBJECT_PROPERTY_ASSERTION);
			for (OWLNegativeObjectPropertyAssertionAxiom OWLNegativeObjectPropertyAssertion : OWLNegativeObjectPropertyAssertionAxiomSet) {
				ontologyAxiomSet.add(OWLNegativeObjectPropertyAssertion);
			}

			Set<OWLSubObjectPropertyOfAxiom> OWLSubObjectPropertyOfAxiomSet = ontology
					.getAxioms(AxiomType.SUB_OBJECT_PROPERTY);
			for (OWLSubObjectPropertyOfAxiom OWLSubObjectPropertyOf : OWLSubObjectPropertyOfAxiomSet) {
				ontologyAxiomSet.add(OWLSubObjectPropertyOf);
			}

			Set<OWLEquivalentObjectPropertiesAxiom> OWLEquivalentObjectPropertyAxiomSet = ontology
					.getAxioms(AxiomType.EQUIVALENT_OBJECT_PROPERTIES);
			for (OWLEquivalentObjectPropertiesAxiom OWLEquivalentObjectProperty : OWLEquivalentObjectPropertyAxiomSet) {
				ontologyAxiomSet.add(OWLEquivalentObjectProperty);
			}

			Set<OWLDisjointObjectPropertiesAxiom> OWLDisjointObjectPropertiesSet = ontology
					.getAxioms(AxiomType.DISJOINT_OBJECT_PROPERTIES);
			for (OWLDisjointObjectPropertiesAxiom OWLDisjointObjectProperties : OWLDisjointObjectPropertiesSet) {
				ontologyAxiomSet.add(OWLDisjointObjectProperties);
			}

			Set<OWLInverseObjectPropertiesAxiom> OWLInverseObjectPropertiesAxiomSet = ontology
					.getAxioms(AxiomType.INVERSE_OBJECT_PROPERTIES);
			for (OWLInverseObjectPropertiesAxiom OWLInverseObjectProperties : OWLInverseObjectPropertiesAxiomSet) {
				ontologyAxiomSet.add(OWLInverseObjectProperties);
			}

			Set<OWLObjectPropertyDomainAxiom> OWLObjectPropertyDomainAxiomSet = ontology
					.getAxioms(AxiomType.OBJECT_PROPERTY_DOMAIN);
			for (OWLObjectPropertyDomainAxiom OWLObjectPropertyDomain : OWLObjectPropertyDomainAxiomSet) {
				ontologyAxiomSet.add(OWLObjectPropertyDomain);
			}

			Set<OWLObjectPropertyRangeAxiom> OWLObjectPropertyRangeAxiomSet = ontology
					.getAxioms(AxiomType.OBJECT_PROPERTY_RANGE);
			for (OWLObjectPropertyRangeAxiom OWLObjectPropertyRange : OWLObjectPropertyRangeAxiomSet) {
				ontologyAxiomSet.add(OWLObjectPropertyRange);
			}

			Set<OWLFunctionalObjectPropertyAxiom> OWLFunctionalObjectPropertyAxiomSet = ontology
					.getAxioms(AxiomType.FUNCTIONAL_OBJECT_PROPERTY);
			for (OWLFunctionalObjectPropertyAxiom OWLFunctionalObjectProperty : OWLFunctionalObjectPropertyAxiomSet) {
				ontologyAxiomSet.add(OWLFunctionalObjectProperty);
			}

			Set<OWLInverseFunctionalObjectPropertyAxiom> OWLInverseFunctionalObjectPropertyAxiomSet = ontology
					.getAxioms(AxiomType.INVERSE_FUNCTIONAL_OBJECT_PROPERTY);
			for (OWLInverseFunctionalObjectPropertyAxiom OWLInverseFunctionalObjectProperty : OWLInverseFunctionalObjectPropertyAxiomSet) {
				ontologyAxiomSet.add(OWLInverseFunctionalObjectProperty);
			}

			Set<OWLReflexiveObjectPropertyAxiom> OWLReflexiveObjectPropertyAxiomSet = ontology
					.getAxioms(AxiomType.REFLEXIVE_OBJECT_PROPERTY);
			for (OWLReflexiveObjectPropertyAxiom OWLReflexiveObjectProperty : OWLReflexiveObjectPropertyAxiomSet) {
				ontologyAxiomSet.add(OWLReflexiveObjectProperty);
			}

			Set<OWLIrreflexiveObjectPropertyAxiom> OWLIrreflexiveObjectPropertyAxiomSet = ontology
					.getAxioms(AxiomType.IRREFLEXIVE_OBJECT_PROPERTY);
			for (OWLIrreflexiveObjectPropertyAxiom OWLIrreflexiveObjectProperty : OWLIrreflexiveObjectPropertyAxiomSet) {
				ontologyAxiomSet.add(OWLIrreflexiveObjectProperty);
			}

			Set<OWLSymmetricObjectPropertyAxiom> OWLSymmetricObjectPropertyAxiomSet = ontology
					.getAxioms(AxiomType.SYMMETRIC_OBJECT_PROPERTY);
			for (OWLSymmetricObjectPropertyAxiom OWLSymmetricObjectProperty : OWLSymmetricObjectPropertyAxiomSet) {
				ontologyAxiomSet.add(OWLSymmetricObjectProperty);
			}

			Set<OWLAsymmetricObjectPropertyAxiom> OWLAsymmetricObjectPropertyAxiomSet = ontology
					.getAxioms(AxiomType.ASYMMETRIC_OBJECT_PROPERTY);
			for (OWLAsymmetricObjectPropertyAxiom OWLAsymmetricObjectProperty : OWLAsymmetricObjectPropertyAxiomSet) {
				ontologyAxiomSet.add(OWLAsymmetricObjectProperty);
			}

			Set<OWLTransitiveObjectPropertyAxiom> OWLTransitiveObjectPropertyAxiomSet = ontology
					.getAxioms(AxiomType.TRANSITIVE_OBJECT_PROPERTY);
			for (OWLTransitiveObjectPropertyAxiom OWLTransitiveObjectProperty : OWLTransitiveObjectPropertyAxiomSet) {
				ontologyAxiomSet.add(OWLTransitiveObjectProperty);
			}

			Set<OWLAxiom> arrayOfExplanation = null;

			Set<Set<OWLAxiom>> arrayOfExplanationSet = new HashSet<Set<OWLAxiom>>(3000000, 1000000F);

			Set<OWLAxiom> theSet = new HashSet<OWLAxiom>(3000000, 1000000F);
			theSet.addAll(ontologyAxiomSet);

			for (Explanation<OWLAxiom> explanation : explanations) { // explanation
																		// is
																		// M
																		// in
																		// MI(K),
																		// while
																		// explanations
																		// is
																		// MI(K).
				arrayOfExplanation = explanation.getAxioms(); // arrayOfExplanation
																// is M in
																// MI(K)
				System.out.println("-----------------------------------------------------------------------------");
				System.out.println("MI(K) subset: " + arrayOfExplanation);
				arrayOfExplanationSet.add(arrayOfExplanation); // arrayOfExplanationSet
																// is MI(K)
																// set
				System.out.println("-----------------------------------------------------------------------------");

				System.out.println("Axioms causing the inconsistency: ");
				for (OWLAxiom causingAxiom : arrayOfExplanation) {
					System.out.println(causingAxiom);
					MIKAxiomSet.add(causingAxiom);
					if ((causingAxiom.isBottomEntity() == true) || (causingAxiom.isTopEntity() == true)) {
						topBottom.add(causingAxiom);
					}

					inconsistentClass = (Set<OWLClass>) causingAxiom.getClassesInSignature();
					for (OWLClass theClass : inconsistentClass) {
						// System.out.println("theClass: " + theClass);
						MIKClassSet.add(theClass);
					}
					inconsistentIndividual = (Set<OWLNamedIndividual>) causingAxiom.getIndividualsInSignature();
					for (OWLNamedIndividual theIndividual : inconsistentIndividual) {

						MIKIndividualSet.add(theIndividual);
					}
					inconsistentObjectProperty = (Set<OWLObjectProperty>) causingAxiom.getObjectPropertiesInSignature();
					for (OWLObjectProperty theObjectProperty : inconsistentObjectProperty) {
						MIKObjectPropertySet.add(theObjectProperty);
					}
				}

				System.out.println("-----------------------------------------------------------------------------");
				System.out.println("--------------------------Computation for I_mic------------------------------");
				System.out.println("M in MI(K): " + arrayOfExplanation);
				sizeOfM = arrayOfExplanation.size();
				System.out.println("M size: " + sizeOfM);
				explanationSizeList.add((int) sizeOfM);
				onePerSizeOfM = (float) 1 / sizeOfM;
				System.out.println("One per M size: " + onePerSizeOfM);
				sumOfSize = sumOfSize + onePerSizeOfM;

				System.out.println("Sum of one per M size: " + sumOfSize);
				System.out.println("-----------------------------------------------------------------------------");

			}

			// System.out.println("SIZE: " + explanations.size());

			// System.out.println("explanationSizeList: " +
			// explanationSizeList.size());

			// System.out.println("ExplanationSet: " +
			// arrayOfExplanationSet.size());

			float RiK;
			float Msize;
			float OneMinusRiK;
			ArrayList<Float> RiKarray = new ArrayList<>();

			int OWLSubClassOfAxiomSetSize = OWLSubClassOfAxiomSet.size();
			int OWLEquivalentClassesAxiomSetSize = OWLEquivalentClassesAxiomSet.size();
			int OWLDisjointClassesAxiomSetSize = OWLDisjointClassesAxiomSet.size();
			int OWLDisjointUnionAxiomSetSize = OWLDisjointUnionAxiomSet.size();
			int OWLDifferentIndividualsAxiomSetSize = OWLDifferentIndividualsAxiomSet.size();
			int OWLSameIndividualAxiomSetSize = OWLSameIndividualAxiomSet.size();
			int OWLClassAssertionAxiomSetSize = OWLClassAssertionAxiomSet.size();
			int OWLObjectPropertyAssertionAxiomSetSize = OWLObjectPropertyAssertionAxiomSet.size();
			int OWLNegativeObjectPropertyAssertionAxiomSetSize = OWLNegativeObjectPropertyAssertionAxiomSet.size();
			int OWLSubObjectPropertyOfAxiomSetSize = OWLSubObjectPropertyOfAxiomSet.size();
			int OWLEquivalentObjectPropertyAxiomSetSize = OWLEquivalentObjectPropertyAxiomSet.size();
			int OWLDisjointObjectPropertiesSetSize = OWLDisjointObjectPropertiesSet.size();
			int OWLInverseObjectPropertiesAxiomSetSize = OWLInverseObjectPropertiesAxiomSet.size();
			int OWLObjectPropertyDomainAxiomSetSize = OWLObjectPropertyDomainAxiomSet.size();
			int OWLObjectPropertyRangeAxiomSetSize = OWLObjectPropertyRangeAxiomSet.size();
			int OWLFunctionalObjectPropertyAxiomSetSize = OWLFunctionalObjectPropertyAxiomSet.size();
			int OWLInverseFunctionalObjectPropertyAxiomSetSize = OWLInverseFunctionalObjectPropertyAxiomSet.size();
			int OWLReflexiveObjectPropertyAxiomSetSize = OWLReflexiveObjectPropertyAxiomSet.size();
			int OWLIrreflexiveObjectPropertyAxiomSetSize = OWLIrreflexiveObjectPropertyAxiomSet.size();
			int OWLSymmetricObjectPropertyAxiomSetSize = OWLSymmetricObjectPropertyAxiomSet.size();
			int OWLAsymmetricObjectPropertyAxiomSetSize = OWLAsymmetricObjectPropertyAxiomSet.size();
			int OWLTransitiveObjectPropertyAxiomSetSize = OWLTransitiveObjectPropertyAxiomSet.size();

			System.out.println("OWLSubClassOfAxiomSetSize: " + OWLSubClassOfAxiomSetSize);
			System.out.println("OWLEquivalentClassesAxiomSetSize: " + OWLEquivalentClassesAxiomSetSize);
			System.out.println("OWLDisjointClassesAxiomSetSize: " + OWLDisjointClassesAxiomSetSize);
			System.out.println("OWLDisjointUnionAxiomSetSize: " + OWLDisjointUnionAxiomSetSize);
			System.out.println("OWLDifferentIndividualsAxiomSetSize: " + OWLDifferentIndividualsAxiomSetSize);
			System.out.println("OWLSameIndividualAxiomSetSize: " + OWLSameIndividualAxiomSetSize);
			System.out.println("OWLClassAssertionAxiomSetSize: " + OWLClassAssertionAxiomSetSize);
			System.out.println("OWLObjectPropertyAssertionAxiomSetSize: " + OWLObjectPropertyAssertionAxiomSetSize);
			System.out.println("OWLNegativeObjectPropertyAssertionAxiomSetSize: "
					+ OWLNegativeObjectPropertyAssertionAxiomSetSize);
			System.out.println("OWLSubObjectPropertyOfAxiomSetSize: " + OWLSubObjectPropertyOfAxiomSetSize);
			System.out.println("OWLEquivalentObjectPropertyAxiomSetSize: " + OWLEquivalentObjectPropertyAxiomSetSize);
			System.out.println("OWLDisjointObjectPropertiesSetSize: " + OWLDisjointObjectPropertiesSetSize);
			System.out.println("OWLInverseObjectPropertiesAxiomSetSize: " + OWLInverseObjectPropertiesAxiomSetSize);
			System.out.println("OWLObjectPropertyDomainAxiomSetSize: " + OWLObjectPropertyDomainAxiomSetSize);
			System.out.println("OWLObjectPropertyRangeAxiomSetSize: " + OWLObjectPropertyRangeAxiomSetSize);
			System.out.println("OWLFunctionalObjectPropertyAxiomSetSize: " + OWLFunctionalObjectPropertyAxiomSetSize);
			System.out.println("OWLInverseFunctionalObjectPropertyAxiomSetSize: "
					+ OWLInverseFunctionalObjectPropertyAxiomSetSize);
			System.out.println("OWLReflexiveObjectPropertyAxiomSetSize: " + OWLReflexiveObjectPropertyAxiomSetSize);
			System.out.println("OWLIrreflexiveObjectPropertyAxiomSetSize: " + OWLIrreflexiveObjectPropertyAxiomSetSize);
			System.out.println("OWLSymmetricObjectPropertyAxiomSetSize: " + OWLSymmetricObjectPropertyAxiomSetSize);
			System.out.println("OWLAsymmetricObjectPropertyAxiomSetSize: " + OWLAsymmetricObjectPropertyAxiomSetSize);
			System.out.println("OWLTransitiveObjectPropertyAxiomSetSize: " + OWLTransitiveObjectPropertyAxiomSetSize);

			int sizeOfK = ontologyAxiomSet.size();
			System.out.println("Size of K: " + sizeOfK);

			System.out.println("                                   ");
			System.out.println("===============================================================");
			System.out.println("==============INCONSISTENCY MEASURES FOR ONTOLOGY==============");
			System.out.println("===============================================================");

			if (reasoner.isConsistent()) {
				System.out.println("1. DRASTIC INCONSISTENCY MEASURE I_d: " + 0);
			} else {
				System.out.println("1. DRASTIC INCONSISTENCY MEASURE I_d: " + 1);
			}
			System.out.println("***************************************************************");
			float sizeOfMI = explanations.size();
			System.out.println("Explanation size: " + explanations.size());

			System.out.println("2. MI-INCONSISTENCY MEASURE I_mi: " + sizeOfMI);
			System.out.println("***************************************************************");
			System.out.println("3. MI^C-INCONSISTENCY MEASURE I_mic: " + sumOfSize);
			System.out.println("***************************************************************");

			ReasonerFactory rf6 = new ReasonerFactory();
			OWLOntologyManager manager6 = OWLManager.createOWLOntologyManager();
			OWLOntology AxiomOntology6 = manager6.createOntology();
			// OWLDataFactory df6 = manager6.getOWLDataFactory();
			AddAxiom addAxiom6;
			Set<OWLAxiom> axiomsToRemove6;
			ArrayList<Integer> consistentSubsetSize = new ArrayList<>();
			HashSet<Set<OWLAxiom>> consistentSubset = new HashSet<Set<OWLAxiom>>();
			HashSet<Set<OWLAxiom>> inconsistentSubset = new HashSet<Set<OWLAxiom>>();

			for (Set<OWLAxiom> s : powerSet(ontologyAxiomSet)) {
				manager6 = OWLManager.createOWLOntologyManager();
				AxiomOntology6 = manager6.createOntology();

				axiomsToRemove6 = AxiomOntology6.getAxioms();

				if (axiomsToRemove6 != null) {
					manager6.removeAxioms(AxiomOntology6, axiomsToRemove6);
				}

				for (OWLAxiom axiomOfS : s) {
					addAxiom6 = new AddAxiom(AxiomOntology6, axiomOfS);
					manager6.applyChange(addAxiom6);
				}

				OWLReasoner reasoner6 = rf6.createReasoner(AxiomOntology6); // for
																			// hermit
																			// and
																			// JFact

				System.out.println("C: " + s);
				System.out.println("Is C consistent? " + reasoner6.isConsistent());

				if (reasoner6.isConsistent() == true) {
					consistentSubset.add(s);
					consistentSubsetSize.add(s.size());
				}

				if (reasoner6.isConsistent() == false) {
					inconsistentSubset.add(s);
				}
			}

			for (int i = 0; i < sizeOfK; i++) {

				int iPlus1 = i + 1;

				Msize = Collections.frequency(explanationSizeList, iPlus1);

				float Csize;

				Csize = Collections.frequency(consistentSubsetSize, iPlus1);
				System.out.println("Msize of " + iPlus1 + ": " + Msize);
				System.out.println("Csize of " + iPlus1 + ": " + Csize);
				float MsizePlusCsize = Msize + Csize;
				if (Msize == 0) {
					RiK = 0;
				} else {
					RiK = Msize / MsizePlusCsize;
				}

				System.out.println("R" + iPlus1 + "(K): " + Msize + "/" + MsizePlusCsize + "= " + RiK);
				float RiKDivi = RiK / (float) iPlus1;
				System.out.println("RiKDivi: " + RiKDivi);
				OneMinusRiK = (float) 1 - RiKDivi;
				System.out.println("(1 - RiK): " + OneMinusRiK);

				RiKarray.add(OneMinusRiK);
			}

			float total = 1;
			System.out.println("Number of one minus RiK: " + RiKarray.size());
			for (float value : RiKarray) {
				System.out.println("Each value in one minus RiK: " + value);
				total *= value;
			}
			System.out.println("Total of multiplication of one minus RiK: " + total);
			float idf = (float) 1 - total;
			System.out.println("1 - Total of multiplication of one minus RiK: " + idf);
			System.out.println("4. Df INCONSISTENCY MEASURE I_df: " + idf);
			System.out.println("***************************************************************");

			for (OWLAxiom MIKAxiom : MIKAxiomSet) {
				System.out.println("Axiom of M in MI(K) : " + MIKAxiom);
			}

			float cardOfAxiomMIUnion = MIKAxiomSet.size();
			System.out.println("5. PROBLEMATIC INCONSISTENCY MEASURE I_p: " + cardOfAxiomMIUnion);
			System.out.println("***************************************************************");

			float I_ir = sizeOfMI / sizeOfK;
			System.out.println("Size of MI(K): " + sizeOfMI);
			System.out.println("Size of K: " + sizeOfK);
			if ((sizeOfMI == 0) && (sizeOfK == 0)) {
				System.out.println("6. INCOMPATIBILITY RATIO INCONSISTENCY MEASURE I_ir: 0");
			} else {
				System.out.println("6. INCOMPATIBILITY RATIO INCONSISTENCY MEASURE I_ir: " + I_ir);
			}
			System.out.println("***************************************************************");

			if (explanations.size() > 0) {

				for (Set<OWLAxiom> inconsistent : inconsistentSubset) {
					for (Set<OWLAxiom> consistent : consistentSubset) {
						if ((inconsistent.containsAll(consistent) == true)
								&& (inconsistent.equals(consistent) == false)) {
							// if (inconsistent.size() != consistent.size() &&
							// consistent.isEmpty() == false) {
							MCKcandidate.add(consistent);
							// }
						}
					}
				}

			} else {
				MCKcandidate.add(ontologyAxiomSet);
			}

			for (Set<OWLAxiom> mck : eliminate_notMCK(MCKcandidate)) {
				System.out.println("MCK: " + mck);
			}

			int MCsize = eliminate_notMCK(MCKcandidate).size();

			// To compute SC(K) in MC Inconsistency Measure
			ReasonerFactory rf8 = new ReasonerFactory();
			OWLOntologyManager manager8 = OWLManager.createOWLOntologyManager();
			OWLOntology AxiomOntology8 = manager8.createOntology();
			Set<OWLAxiom> axiomsToRemove8;
			AddAxiom addAxiom8;

			for (OWLAxiom theAxiom : ontologyAxiomSet) {

				manager8 = OWLManager.createOWLOntologyManager();
				AxiomOntology8 = manager8.createOntology();

				axiomsToRemove8 = AxiomOntology8.getAxioms();

				if (axiomsToRemove8 != null) {
					manager8.removeAxioms(AxiomOntology8, axiomsToRemove8);
				}

				addAxiom8 = new AddAxiom(AxiomOntology8, theAxiom);
				manager8.applyChange(addAxiom8);

				OWLReasoner reasoner8 = rf8.createReasoner(AxiomOntology8); // for
																			// hermit
																			// and
																			// JFact

				System.out.println("The axiom: " + theAxiom);
				System.out
						.println("Is the axiom (" + theAxiom + ") consistent/satisfiable? " + reasoner8.isConsistent());

				if (reasoner8.isConsistent() == false) {
					ontologyAxiomsCausingUnsatisfiable.add(theAxiom);
				}

			}

			float SCsize = ontologyAxiomsCausingUnsatisfiable.size();
			System.out.println("MCsize: " + MCsize);
			System.out.println("SCsize: " + SCsize);
			float imc = (float) MCsize + SCsize - 1;

			System.out.println("7. MC INCONSISTENCY MEASURE I_mc: " + imc);
			System.out.println("***************************************************************");

			System.out.println("Size of consistent subset size: " + consistentSubsetSize.size());

			if (consistentSubsetSize.size() != 0) {
				int maxOfSizeK = Collections.max(consistentSubsetSize);
				System.out.println("Size of K: " + sizeOfK);
				System.out.println("Max of size K: " + maxOfSizeK);
				float inc = (float) sizeOfK - (float) maxOfSizeK;
				System.out.println("8. NC INCONSISTENCY MEASURE I_nc: " + inc);
				System.out.println("***************************************************************");
			} else {
				System.out.println("Size of K: " + sizeOfK);
				float inc = (float) sizeOfK;
				System.out.println("8. NC INCONSISTENCY MEASURE I_nc: " + inc);
				System.out.println("***************************************************************");
			}

			Set<OWLClass> ontologyClass = null;
			Set<OWLNamedIndividual> ontologyIndividual = null;
			Set<OWLObjectProperty> ontologyObjectProperty = null;

			int cardOfMIKClassSet = MIKClassSet.size();
			int cardOfMIKIndividualSet = MIKIndividualSet.size();
			int cardOfMIKObjectPropertySet = MIKObjectPropertySet.size();

			System.out.println("MIKClassSet Size: " + cardOfMIKClassSet);
			System.out.println("MIKIndividualSet Size: " + cardOfMIKIndividualSet);
			System.out.println("MIKObjectPropertySet Size: " + cardOfMIKObjectPropertySet);

			float cardOfSignAxiomMIKUnion = cardOfMIKClassSet + cardOfMIKIndividualSet + cardOfMIKObjectPropertySet;

			for (OWLAxiom theAxiom : ontologyAxiomSet) {
				ontologyClass = (Set<OWLClass>) theAxiom.getClassesInSignature();
				ontologyIndividual = (Set<OWLNamedIndividual>) theAxiom.getIndividualsInSignature();
				ontologyObjectProperty = (Set<OWLObjectProperty>) theAxiom.getObjectPropertiesInSignature();

				for (OWLClass theClass2 : ontologyClass) {
					// System.out.println("theClass2: " + theClass2);
					MIKClassSet.add(theClass2);
				}
				for (OWLNamedIndividual theIndividual2 : ontologyIndividual) {
					MIKIndividualSet.add(theIndividual2);
				}
				for (OWLObjectProperty theObjectProperty2 : ontologyObjectProperty) {

					MIKObjectPropertySet.add(theObjectProperty2);
				}
			}

			float cardOfSignInK = MIKClassSet.size() + MIKIndividualSet.size() + MIKObjectPropertySet.size();
			System.out.println("Cardinality of signatures in axiom union: " + cardOfSignAxiomMIKUnion);
			System.out.println("Cardinality of signatures in K: " + cardOfSignInK);
			if ((cardOfSignAxiomMIKUnion == 0) && (cardOfSignInK == 0)) {
				System.out.println("9. MV INCONSISTENCY MEASURE I_mv: 0 ");
			} else {
				System.out.println("9. MV INCONSISTENCY MEASURE I_mv: " + cardOfSignAxiomMIKUnion / cardOfSignInK);
			}
			System.out.println("***************************************************************");

			ReasonerFactory rf3 = new ReasonerFactory();
			OWLOntologyManager manager3 = OWLManager.createOWLOntologyManager();
			OWLOntology AxiomOntology3 = manager3.createOntology();
			// OWLDataFactory df3 = manager3.getOWLDataFactory();
			AddAxiom addAxiom3;
			Set<OWLAxiom> axiomsToRemove3;

			ReasonerFactory rf5 = new ReasonerFactory();
			OWLOntologyManager manager5 = OWLManager.createOWLOntologyManager();
			OWLOntology AxiomOntology5 = manager3.createOntology();
			// OWLDataFactory df5 = manager5.getOWLDataFactory();
			AddAxiom addAxiom5;
			Set<OWLAxiom> axiomsToRemove5;
			Set<Set<OWLAxiom>> MCSes = new HashSet<Set<OWLAxiom>>();

			for (Set<OWLAxiom> subsetM : powerSet(ontologyAxiomSet)) {

				manager3 = OWLManager.createOWLOntologyManager();
				AxiomOntology3 = manager3.createOntology();

				// Condition 1 of MCS

				axiomsToRemove3 = AxiomOntology3.getAxioms();

				if (axiomsToRemove3 != null) {
					manager3.removeAxioms(AxiomOntology3, axiomsToRemove3);
				}

				for (OWLAxiom axiomOfK : ontologyAxiomSet) {
					addAxiom3 = new AddAxiom(AxiomOntology3, axiomOfK);
					manager3.applyChange(addAxiom3);
				}

				System.out.println("========================================");

				System.out.println("M: " + subsetM);

				manager3.removeAxioms(AxiomOntology3, subsetM);

				OWLReasoner reasoner3 = rf3.createReasoner(AxiomOntology3); // for
																			// hermit
																			// and
																			// JFact

				System.out.println("Is K minus subset M consistent? " + reasoner3.isConsistent());

				//
				// Condition 2 of MCS
				//

				manager5 = OWLManager.createOWLOntologyManager();
				AxiomOntology5 = manager5.createOntology();

				axiomsToRemove5 = AxiomOntology5.getAxioms();

				if (axiomsToRemove5 != null) {
					manager5.removeAxioms(AxiomOntology5, axiomsToRemove5);
				}

				for (OWLAxiom axiomOfK : ontologyAxiomSet) {
					addAxiom5 = new AddAxiom(AxiomOntology5, axiomOfK);
					manager5.applyChange(addAxiom5);
				}

				ArrayList<String> consistentValue = new ArrayList<String>();
				for (OWLAxiom Ci : subsetM) {
					System.out.println("Ci: " + Ci);

					manager5.removeAxioms(AxiomOntology5, subsetM);
					manager5.addAxiom(AxiomOntology5, Ci);

					OWLReasoner reasoner5 = rf5.createReasoner(AxiomOntology5);

					System.out.println("Is K minus (subset M minus Ci) consistent? " + reasoner5.isConsistent());

					if (reasoner5.isConsistent() == true) {
						consistentValue.add("true");
					} else if (reasoner5.isConsistent() == false) {
						consistentValue.add("false");
					}

				}

				if (reasoner3.isConsistent() == true) {
					if (doesListContainAllFalse(consistentValue) == true) {
						MCSes.add(subsetM);
					}
				}
			}

			System.out.println("MCSes size: " + MCSes.size());

			Set<OWLClass> ontologyClass2 = null;
			Set<OWLNamedIndividual> ontologyIndividual2 = null;
			Set<OWLObjectProperty> ontologyObjectProperty2 = null;

			HashSet<OWLClass> MCSClassSet = new HashSet<OWLClass>();
			HashSet<OWLNamedIndividual> MCSIndividualSet = new HashSet<OWLNamedIndividual>();
			HashSet<OWLObjectProperty> MCSObjectPropertySet = new HashSet<OWLObjectProperty>();

			for (Set<OWLAxiom> MCS : MCSes) {
				System.out.println("MCS: " + MCS);
				for (OWLAxiom axiomInMcs : MCS) {
					// System.out.println("axiomInMcs: " + axiomInMcs);
					ontologyClass2 = (Set<OWLClass>) axiomInMcs.getClassesInSignature();
					ontologyIndividual2 = (Set<OWLNamedIndividual>) axiomInMcs.getIndividualsInSignature();
					ontologyObjectProperty2 = (Set<OWLObjectProperty>) axiomInMcs.getObjectPropertiesInSignature();

					for (OWLClass theClass3 : ontologyClass2) {
						// System.out.println("theClass3: " + theClass3);
						MCSClassSet.add(theClass3);
					}
					for (OWLNamedIndividual theIndividual3 : ontologyIndividual2) {
						// System.out.println("theIndividual3: " +
						// theIndividual3);
						MCSIndividualSet.add(theIndividual3);
					}
					for (OWLObjectProperty theObjectProperty3 : ontologyObjectProperty2) {
						// System.out.println("theObjectProperty3: " +
						// theObjectProperty3);
						MCSObjectPropertySet.add(theObjectProperty3);
					}

				}

				// System.out.println("MCSIndividualSet: " +
				// ontologyIndividual2.size());
			}

			int cardOfMCSesSign = MCSClassSet.size() + MCSIndividualSet.size() + MCSObjectPropertySet.size();
			System.out.println("Cardinality of Class in MCS: " + MCSClassSet.size());
			System.out.println("Cardinality of Individual in MCS: " + MCSIndividualSet.size());
			System.out.println("Cardinality of ObjectProperty in MCS: " + MCSObjectPropertySet.size());
			System.out.println("Cardinality of signatures in MCS: " + cardOfMCSesSign);
			System.out.println("Cardinality of signatures in K: " + cardOfSignInK);

			if ((cardOfMCSesSign == 0) && (cardOfSignInK == 0)) {
				System.out.println("10. ID_MCS INCONSISTENCY MEASURE: 0");
			} else {
				System.out.println("10. ID_MCS INCONSISTENCY MEASURE: " + cardOfMCSesSign / cardOfSignInK);
			}
			System.out.println("***************************************************************");

			System.out.println("11. MIV_D INCONSISTENCY MEASURE: ");
			for (OWLAxiom axiomInK : ontologyAxiomSet) {
				if (MIKAxiomSet.contains(axiomInK) == true) {
					System.out.println("MIV_D(K," + axiomInK + ") = 1");
				} else if (MIKAxiomSet.contains(axiomInK) == false) {
					System.out.println("MIV_D(K," + axiomInK + ") = 0");
				}
			}

			System.out.println("***************************************************************");
			System.out.println("12. MIV_Sharp INCONSISTENCY MEASURE: ");

			Set<Set<OWLAxiom>> SetOfMinMIK = new HashSet<Set<OWLAxiom>>();

			float onePerMsize, MIVc = 0;
			for (OWLAxiom axiomInK2 : ontologyAxiomSet) {
				SetOfMinMIK.clear();
				for (Set<OWLAxiom> MinMIK : arrayOfExplanationSet) {
					if (MinMIK.contains(axiomInK2)) {
						SetOfMinMIK.add(MinMIK);
					}
				}
				System.out.println("MIV_Sharp(K," + axiomInK2 + ") = " + SetOfMinMIK.size());

			}
			System.out.println("***************************************************************");
			System.out.println("13. MIV_c INCONSISTENCY MEASURE: ");
			for (OWLAxiom axiomInK3 : ontologyAxiomSet) {
				MIVc = 0;
				for (Set<OWLAxiom> MinMIK : arrayOfExplanationSet) {
					if (MinMIK.contains(axiomInK3)) {
						onePerMsize = (float) 1 / (MinMIK.size());
						MIVc = MIVc + onePerMsize;
					}
				}

				System.out.println("MIV_c(K," + axiomInK3 + ") = " + new DecimalFormat("####.##").format(MIVc));
			}
			System.out.println("***************************************************************");
			System.out.println("14. MI SHAPLEY INCONSISTENCY MEASURE: ");
			float shapleyValue, shapleyVal;
			int c, n;
			// System.out.println("Factorial of 3: " + factorial(3));

			ReasonerFactory rf4 = new ReasonerFactory();
			OWLOntologyManager manager4 = OWLManager.createOWLOntologyManager();
			OWLOntology AxiomOntology = manager4.createOntology();
			OWLDataFactory df4 = manager4.getOWLDataFactory();
			AddAxiom addAxiom4;
			Set<OWLAxiom> axiomsToRemove4;
			int sizeOfMIOfC, sizeOfMIOfCMinusAlpha;
			float factorial1, factorial2, factorial3, firstComputation, secondComputation;

			for (OWLAxiom alpha : ontologyAxiomSet) {
				System.out.println("Alpha: " + alpha);
				shapleyValue = 0;
				shapleyVal = 0;
				for (Set<OWLAxiom> s : powerSet(ontologyAxiomSet)) {
					c = s.size();
					n = ontologyAxiomSet.size();

					manager4 = OWLManager.createOWLOntologyManager();
					AxiomOntology = manager4.createOntology();

					axiomsToRemove4 = AxiomOntology.getAxioms();
					// for (OWLAxiom ax : axiomsToRemove)
					if (axiomsToRemove4 != null) {
						manager4.removeAxioms(AxiomOntology, axiomsToRemove4);
					}

					for (OWLAxiom axiomOfS : s) {
						addAxiom4 = new AddAxiom(AxiomOntology, axiomOfS);
						manager4.applyChange(addAxiom4);
					}

					OWLReasoner reasoner4 = rf4.createReasoner(AxiomOntology); // for
																				// hermit
																				// and
																				// JFact

					System.out.println("========================================");

					// //for hermit and JFact
					System.out.println("C: " + s);
					System.out.println("Is C consistent? " + reasoner4.isConsistent());

					ExplanationGenerator<OWLAxiom> explainInconsistency4 = new InconsistentOntologyExplanationGeneratorFactory(
							rf4, 1000L).createExplanationGenerator(AxiomOntology);

					Set<Explanation<OWLAxiom>> explanations4 = explainInconsistency4
							.getExplanations(df4.getOWLSubClassOfAxiom(df4.getOWLThing(), df4.getOWLNothing()));
					System.out.println("Explanation of inconsistency of C: " + explanations4);

					RemoveAxiom removeAxiom = new RemoveAxiom(AxiomOntology, alpha);
					manager4.applyChange(removeAxiom);

					Set<OWLAxiom> cminusalphaaxioms = AxiomOntology.getAxioms();
					for (OWLAxiom memberOfcminusalphaaxioms : cminusalphaaxioms) {
						System.out.println("Member of C minus alpha axioms: " + memberOfcminusalphaaxioms);
					}

					sizeOfMIOfC = explanations4.size();

					System.out.println("Size of MI of C: " + sizeOfMIOfC);

					System.out.println("Is C minus alpha consistent? " + reasoner4.isConsistent());

					ExplanationGenerator<OWLAxiom> explainInconsistency5 = new InconsistentOntologyExplanationGeneratorFactory(
							rf4, 1000L).createExplanationGenerator(AxiomOntology);

					Set<Explanation<OWLAxiom>> explanations5 = explainInconsistency5
							.getExplanations(df.getOWLSubClassOfAxiom(df4.getOWLThing(), df4.getOWLNothing()));
					System.out.println("Explanation of inconsistency C minus alpha: " + explanations5);

					sizeOfMIOfCMinusAlpha = explanations5.size();

					System.out.println("Size of MI of C minus alpha: " + sizeOfMIOfCMinusAlpha);

					System.out.println("Size of n: " + n);
					System.out.println("Size of c: " + c);

					factorial1 = factorial(c - 1);
					factorial2 = factorial(n - c);
					factorial3 = factorial(n);
					firstComputation = (factorial1 * factorial2) / factorial3;
					secondComputation = sizeOfMIOfC - sizeOfMIOfCMinusAlpha;

					System.out.println("factorial(c-1): " + factorial1);
					System.out.println("factorial(n-c): " + factorial2);
					System.out.println("factorial(n): " + factorial3);
					// System.out.println("First Computation: " +
					// firstComputation);
					System.out.println("(Size of MI of C) - (Size of MI of C minus alpha): " + secondComputation);

					shapleyVal = firstComputation * secondComputation;
					System.out.println("Shapley value: " + shapleyVal);
					shapleyValue = shapleyValue + shapleyVal;
					System.out.println("Sum of Shapley Value = " + new DecimalFormat("####.##").format(shapleyValue));
					System.out.println("========================================");
				}
				System.out.println("S^(I_MI)(K," + alpha + ") = " + shapleyValue);
				System.out.println("-----------------------------------------------");
			}

			System.out.println("***************************************************************");
			System.out.println("15. SCORING INCONSISTENCY MEASURE I_s: ");

			ReasonerFactory rf7 = new ReasonerFactory();
			OWLOntologyManager manager7 = OWLManager.createOWLOntologyManager();
			OWLOntology AxiomOntology7;
			OWLDataFactory df7 = manager7.getOWLDataFactory();
			AddAxiom addAxiom7;
			Set<OWLAxiom> axiomsToRemove7;
			int sizeOfMIOfK, sizeOfMIOfKMinusAlpha;
			float scoringValue;

			for (OWLAxiom alpha : ontologyAxiomSet) {
				System.out.println("Alpha: " + alpha);

				manager7 = OWLManager.createOWLOntologyManager();
				AxiomOntology7 = manager7.createOntology();

				axiomsToRemove7 = AxiomOntology7.getAxioms();

				if (axiomsToRemove7 != null) {
					manager7.removeAxioms(AxiomOntology7, axiomsToRemove7);
				}

				for (OWLAxiom alpha2 : ontologyAxiomSet) {
					addAxiom7 = new AddAxiom(AxiomOntology7, alpha2);
					manager7.applyChange(addAxiom7);
				}

				OWLReasoner reasoner7 = rf7.createReasoner(AxiomOntology7); // for
																			// hermit
																			// and
																			// JFact
				System.out.println("========================================");

				RemoveAxiom removeAxiom7 = new RemoveAxiom(AxiomOntology7, alpha);
				manager7.applyChange(removeAxiom7);

				Set<OWLAxiom> kminusalphaaxioms = AxiomOntology7.getAxioms();
				System.out.println("Size of K minus axiom alpha: " + kminusalphaaxioms.size());
				for (OWLAxiom memberOfkminusalphaaxioms : kminusalphaaxioms) {
					System.out.println("Member of K minus axiom alpha: " + memberOfkminusalphaaxioms);
				}

				System.out.println("Is K minus alpha consistent? " + reasoner7.isConsistent());

				ExplanationGenerator<OWLAxiom> explainInconsistency7 = new InconsistentOntologyExplanationGeneratorFactory(
						rf7, 1000L).createExplanationGenerator(AxiomOntology7);

				Set<Explanation<OWLAxiom>> explanations7 = explainInconsistency7
						.getExplanations(df7.getOWLSubClassOfAxiom(df7.getOWLThing(), df7.getOWLNothing()));
				System.out.println("Explanation of inconsistency K minus alpha: " + explanations7);

				sizeOfMIOfK = explanations.size();
				sizeOfMIOfKMinusAlpha = explanations7.size();

				System.out.println("Size of MI of K: " + sizeOfMIOfK);
				System.out.println("Size of MI of K minus alpha: " + sizeOfMIOfKMinusAlpha);

				scoringValue = sizeOfMIOfK - sizeOfMIOfKMinusAlpha;

				System.out.println("(Size of MI of K) - (Size of MI of K minus alpha): " + scoringValue);

				System.out.println("========================================");

				System.out.println("I_s(K," + alpha + ") = " + scoringValue);
				System.out.println("-----------------------------------------------");
			}

			System.out.println("***************************************************************");

		} catch (NoSuchElementException e) {
			System.out.println("NoSuchElementException: " + e.getMessage());
		} catch (InconsistentOntologyException f) {
			System.out.println("InconsistentOntologyException: " + f.getMessage());
		}
		// Warningnya berarti do not create data factories directly; use
		// OWLOntologyManager::getOWLDataFactory()

		long endTime = System.currentTimeMillis();
		long totalTime = endTime - startTime;
		System.out.println("                                 ");
		System.out.println("Total time execution: " + totalTime + " milliseconds.");

	}

	public static <T> Set<Set<T>> powerSet(Set<T> originalSet) {
		Set<Set<T>> sets = new HashSet<Set<T>>();
		if (originalSet.isEmpty()) {
			sets.add(new HashSet<T>());
			return sets;
		}
		ArrayList<T> list = new ArrayList<T>(originalSet);
		T head = list.get(0);
		Set<T> rest = new HashSet<T>(list.subList(1, list.size()));
		for (Set<T> set : powerSet(rest)) {
			Set<T> newSet = new HashSet<T>();
			newSet.add(head);
			newSet.addAll(set);
			sets.add(newSet);
			sets.add(set);
		}
		return sets;
	}

	public static int factorial(int number) {
		int i, fact = 1;
		for (i = 1; i <= number; i++) {
			fact = fact * i;
		}
		return fact;
	}

	public static boolean doesListContainAllFalse(ArrayList<String> arrayList) {
		String falseValue = "false";
		for (String str : arrayList) {
			if (!str.equals(falseValue)) {
				return false;
			}
		}
		return true;
	}

	public static <T> HashSet<Set<OWLAxiom>> eliminate_notMCK(ArrayList<Set<OWLAxiom>> MCKcandidate) {

		HashSet<Set<OWLAxiom>> MCK = new HashSet<Set<OWLAxiom>>();

		Collections.sort(MCKcandidate, new Comparator<Set<OWLAxiom>>() {
			public int compare(Set<OWLAxiom> axiom1, Set<OWLAxiom> axiom2) {
				return axiom2.size() - axiom1.size();
			}
		});

		for (int i = 0; i < MCKcandidate.size(); i++) {

			Set<OWLAxiom> candidateI = MCKcandidate.get(i);
			boolean flag = true;

			for (Set<OWLAxiom> MCKcand : MCK) {

				if (MCKcand.containsAll(candidateI)) {
					flag = false;
					break;
				}
			}
			if (flag) {
				MCK.add(candidateI);
			}
		}

		return MCK;

	}

}
