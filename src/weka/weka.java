package weka;


import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.Supplier;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;
import java.util.stream.IntStream;

import weka.attributeSelection.ASEvaluation;
import weka.attributeSelection.ASSearch;
import weka.attributeSelection.BestFirst;
import weka.attributeSelection.CfsSubsetEval;
import weka.classifiers.Classifier;
import weka.classifiers.CostMatrix;
import weka.classifiers.Evaluation;
import weka.classifiers.bayes.NaiveBayes;
import weka.classifiers.lazy.IBk;
import weka.classifiers.meta.CostSensitiveClassifier;
import weka.classifiers.meta.FilteredClassifier;
import weka.classifiers.trees.RandomForest;
import weka.core.Instance;
import weka.core.Instances;
import weka.core.converters.ConverterUtils.DataSource;
import weka.filters.Filter;
import weka.filters.supervised.attribute.AttributeSelection;
import weka.filters.supervised.instance.Resample;
import weka.filters.supervised.instance.SpreadSubsample;
import weka.filters.supervised.instance.SMOTE;

public class weka{ 
	static String projectName = "OPENJPA"; //or OPENJPA
	public static final String SENSITIVE_LEARNING = "SENSITIVE LEARNING";
	public static final String SENSITIVE_THRESHOLD = "SENSITIVE THRESHOLD";
	public static final String NO = "NO";


	private static final Logger logger =  Logger.getLogger(weka.class.getName());
	public static void main(String[] args) throws Exception
	{
		String projectName1 = "OPENJPA"; //or OPENJPA
		
		String nomeFile = projectName1.toLowerCase() + "Dataset.arff" ;
		String path = "/Users/giuliamenichini/eclipse-workspace/ISW2/" + nomeFile ;
		logger.info("Caricando dataset: ");

	    
		createFile(path);
		

	}

	// metodo per impostare nome del progetto, release, classificatore utilizzato, bilanciamento, featureSelection
	//sensitivity, defectiveInTraining, defectiveInTesting, trainPercentage, testPercentage
	public static ClassifierInfo createMeasureObject(Instances train, Instances test, String[] s,  int version) {
		ClassifierInfo m = new ClassifierInfo(projectName);
	    m.setReleaseNumber(version + 1);

	    String[] fields = {"setClassifierType", "setBalancingMethod", "setFeatureSelectionMethod", "setSensitivityMethod"};
	    for (int i = 0; i < fields.length; i++) {
	        try {
	            Method method = ClassifierInfo.class.getMethod(fields[i], String.class);
	            method.invoke(m, s[i]);
	        } catch (Exception e) {
	            logger.log(Level.SEVERE, (Supplier<String>) () ->"Error occurred while calculating Buggyness " );

	        }
	    }

	    //m.setNumberTrainTest(calculateTrainingTestingRatio(train, test));
	    //m.setBuggyInTrain(calculateBuggy(train));
	    //m.setBuggyInTest(calculateBuggy(test));
	    return m;
	}

	//prende in input le info e setta le metriche di valutazione con tp,fp,fn,tn
	private static void evaluateAndAddMeasure(Evaluation e,ClassifierInfo measure) {
	    logger.info("Settando le metriche");
		String[] evaluationMetrics = {"auc", "kappa", "recall", "precision", "trueNegatives", "truePositives", "falseNegatives", "falsePositives"};
		double[] evaluationValues = {e.areaUnderROC(1), e.kappa(), e.recall(1), e.precision(1), e.numTrueNegatives(1), e.numTruePositives(1), e.numFalseNegatives(1), e.numFalsePositives(1)};
		for (int i = 0; i < evaluationMetrics.length; i++) {
			String metric = evaluationMetrics[i];
			double value = evaluationValues[i];
				switch (metric) {
				case "auc":
					measure.setAuc(value);
					break;
				case "kappa":
					measure.setKappa(value);
					break;
				case "recall":
					measure.setRecall(value);
					break;
				case "precision":
					measure.setPrecision(value);
					break;
				case "trueNegatives":
					measure.setTrueNegatives((int) value);
					break;
				case "truePositives":
					measure.setTruePositives((int) value);
					break;
				case "falseNegatives":
					measure.setFalseNegatives((int) value);
					break;
				case "falsePositives":
					measure.setFalsePositives((int) value);
					break;
				default:
					break;
				}
				
			
				}
			}



	
	//filtro di selezione delle feature, applica CfsSubsetEval che valuta l'importanza di ogni feature
	//in base alla relazione con la classe target e con gli altri attributi
	//BestFirst ricerca il sottoinsieme migliore utilizzando una strategia di ricerca forward
	//la ricerca è indipendente dall'algoritmo di addestramento
	public static AttributeSelection createFeatureSelectionFilter() throws Exception {
	    return createFilter(new CfsSubsetEval(), new BestFirst());
	}

	private static AttributeSelection createFilter(ASEvaluation evaluator, ASSearch search) {
	    AttributeSelection filter = new AttributeSelection();
	    filter.setEvaluator(evaluator);
	    filter.setSearch(search);
	    return filter;
	}

	//creazione set di addestramento e di test . Il set di test è creato a partire dall'insieme corrente mentre il train
	//tutte meno una infine si impostano gli attributi.
	public Instances[] createTrainingAndTestSet(List<Instances> sets, int currentIndex) {
	    Instances testSet = new Instances(sets.get(currentIndex));
	    Instances trainingSet = createTrainingSet(sets, currentIndex);
	    trainingSet.setClassIndex(trainingSet.numAttributes() - 1);
	    testSet.setClassIndex(testSet.numAttributes() - 1);
	    return new Instances[]{trainingSet, testSet};
	}
	// applicazione algoritmo di FS al train e al test in particolare BESTFIRST
	public Instances[] applyFeatureSelection(String featureSelection, Instances trainingSet, Instances testSet) throws Exception {
	    Instances filteredTrainingSet = trainingSet;
	    Instances filteredTestSet = testSet;
	    logger.info("Feature Selection");
	    if (featureSelection.equals("BEST FIRST")) {
	        List<Instances> filteredSets = featureSelection(trainingSet, testSet);
	        filteredTrainingSet = filteredSets.get(1);
	        filteredTestSet = filteredSets.get(0);
	    }
	    return new Instances[]{filteredTrainingSet, filteredTestSet};
	}
	//nessuna applicazione del bilanciamento
	public Evaluation trainAndEvaluateModel(String balancing, String classifier, String costEvaluation, Instances trainingSet, Instances testSet) throws Exception {
	    Classifier classifierInstance = chooseClassificationType(classifier);
	    if (balancing.equals("NO")) {
	        // do nothing
	    } else {
	        classifierInstance = balancing(classifierInstance, balancing, trainingSet);
	    }

	    return evaluateModel(costEvaluation, classifierInstance, trainingSet, testSet);
	}
	//Iterazione di un loop su i dati di train e test con l'applicazione di FS, balancing e classification. 
	//Per ogni iterazione i dati vengono salvati e si va avanti per ogni versione
	public void walkForward(ExperimentParams params, List<Instances> sets, List<ClassifierInfo> measures) throws Exception {
		for (int i = 1; i < sets.size(); i++) {
		Instances[] trainingAndTestSet = createTrainingAndTestSet(sets, i);
		Instances[] filteredTrainingAndTestSet = applyFeatureSelection(params.getFeatureSelection(), trainingAndTestSet[0], trainingAndTestSet[1]);
		Evaluation evaluation = trainAndEvaluateModel(params.getBalancing(), params.getClassifier(), params.getCostEvaluation(), filteredTrainingAndTestSet[0], filteredTrainingAndTestSet[1]);
	    String[] labels = {params.getClassifier(), params.getBalancing(), params.getFeatureSelection(), params.getCostEvaluation()};
	    if (evaluation == null) {
	        logger.log(Level.INFO, "Errore valutando il modello");
	    } else {
	    	ClassifierInfo measure = createMeasureObject(filteredTrainingAndTestSet[0], filteredTrainingAndTestSet[1], labels,  i - 1);
	        evaluateAndAddMeasure(evaluation, measure);
	        measures.add(measure);
	    }
	}
	}
	//input = indice che specifica il set di test che verrà escluso dal set di addestramento.
	// se la lista è vuota viene restituita istanza vuota
	private Instances createTrainingSet(List<Instances> sets, int endIndex) {
	    Optional<Instances> merged = sets.stream()
	            .limit(endIndex)
	            .reduce((train, next) -> {
	                Instances mergedSet = new Instances(train, 0);
	                for (Instance instance : next) {
	                    mergedSet.add(instance);
	                }
	                return mergedSet;
	            });
	    return merged.orElse(new Instances(sets.get(0), 0));
	}

	//copia istante train e test applica FS
	public static List<Instances> applyFeatureSelection(AttributeSelection filter, Instances train, Instances test) throws Exception {
		Instances[] filteredData = new Instances[]{new Instances(train), new Instances(test)};
		filter.setInputFormat(train);
		for (int i = 0; i < filteredData.length; i++) {
			filteredData[i] = Filter.useFilter(filteredData[i], filter);
			filteredData[i].setClassIndex(filteredData[i].numAttributes() - 1);
			}
		return Arrays.asList(filteredData[1], filteredData[0]);
		}
	
	public static List<Instances> featureSelection(Instances train, Instances test) throws Exception {
		return applyFeatureSelection(createFeatureSelectionFilter(), train, test);
		}
	/*
	 * Resample and apply it with noReplacement=false, biasToUniformClass=1.0, and 
	 * sampleSizePercent=Y, where Y/2 is (approximately) the percentage of data that 
	 * belongs to the majority class.
	 */

	//oversampling: aumento numero istanze della classe minoritaria
	//undersampling: riduco numero istanze della classe maggioritaria
	//smote: genero sinteticamente nuove istanze della classe minoritaria
	private static Filter getBalancingFilter(String balancing, Instances train) throws Exception {
	    Filter filter = null;
	    if ("OVERSAMPLING".equals(balancing)) {
	    	int attributeNumber = train.numAttributes();
	    	double majority = train.attributeStats(attributeNumber-1).nominalCounts[1];
	    	String outputSizePerc = Double.toString(2*100*(majority/train.size()));
	        filter = getResampleFilter(train,  new String[]{"-B", "1.0", "-Z", outputSizePerc});
	    } else if ("UNDERSAMPLING".equals(balancing)) {
	        filter = getSpreadSubsampleFilter(train, new String[]{"-M", "1.0"});
	    } else if ("SMOTE".equals(balancing)) {
	        filter = getSMOTEFilter(train);
	    }

	    if (filter != null) {
	        filter.setInputFormat(train);
	    }

	    return filter;
	}
	//data: istanze su cui fare campionamento
	//noReplacement: campionamento con o senza rimpiazzamento
	//biasUniformClass: double indica importanza tra classe minoritaria e maggioritaria più è vicino a 1 più si da
	//importanza alla classe minoritaria 
	//sampleSizePercent: percentuale istanze da mantenere dopo campionamento
	//options: array di stringhe per info aggiuntive
	private static Resample getResampleFilter(Instances data,  String[] options) throws Exception {
        Resample resample = new Resample();
	    resample.setNoReplacement(false);
	    resample.setBiasToUniformClass(1.0);
        resample.setOptions(options);
	    resample.setInputFormat(data);
	    return resample;
	}
	//filtro per sottocampionamento
	private static SpreadSubsample getSpreadSubsampleFilter(Instances data, String[] options) throws Exception {
		SpreadSubsample spreadSubsample = new SpreadSubsample();
	    spreadSubsample.setOptions(options);
	    spreadSubsample.setInputFormat(data);
	    return spreadSubsample;
	}
	//smote function
	private static SMOTE getSMOTEFilter(Instances data) throws Exception {
		SMOTE smote = new SMOTE();
	    smote.setInputFormat(data);
	    return smote;
	}

	//applica filtro prima di passare i dati al classificatore
	private static FilteredClassifier createFilteredClassifier(Classifier c, Filter filter) {
		FilteredClassifier fc = new FilteredClassifier();
	    fc.setClassifier(c);
	    if (filter != null) {
	        fc.setFilter(filter);
	    }
	    return fc;
	}

	private static FilteredClassifier balancing(Classifier c, String balancing, Instances train) throws Exception {
	    logger.info("Bilanciamento");

		Filter filter = getBalancingFilter(balancing, train);
	    return createFilteredClassifier(c, filter);
	}

	
	//sesitiveTreshold imposta matrice di costo specifica per le classi in modo da dare più peso alla class. di una classe
	//sensitiveLearning imposta matrice di costo ed esegue sensitiveLearning per dare più peso ad alcune istanze
	private static Evaluation evaluateModel(String costEvaluation, Classifier c, Instances train, Instances test) {
	    Evaluation ev = null;
	    logger.info("Inizio valutazione Cost Sensitive Classifier");

	    for (String evalType : Arrays.asList(NO, SENSITIVE_THRESHOLD, SENSITIVE_LEARNING)) {
	        if (evalType.equals(costEvaluation)) {
	            try {
	                switch (evalType) {
	                    case NO:
	                        c.buildClassifier(train);
	                        ev = new Evaluation(test);
	                        ev.evaluateModel(c, test);
	                        break;
	                    case SENSITIVE_THRESHOLD:
	                        CostSensitiveClassifier cst = new CostSensitiveClassifier();
	                        cst.setClassifier(c);
	                        cst.setCostMatrix(createCostMatrix(1.0, 10.0));
	                        cst.setMinimizeExpectedCost(true);
	                        cst.buildClassifier(train);
	                        ev = new Evaluation(test, cst.getCostMatrix());
	                        ev.evaluateModel(cst, test);
	                        break;
	                    case SENSITIVE_LEARNING:
	                        CostSensitiveClassifier sl = new CostSensitiveClassifier();
	                        sl.setClassifier(c);
	                        sl.setCostMatrix(createCostMatrix(1.0, 10.0));
	                        sl.setMinimizeExpectedCost(false);
	                        sl.buildClassifier(train);
	                        ev = new Evaluation(test, sl.getCostMatrix());
	                        ev.evaluateModel(sl, test);
	                        break;
	                    default:
	                    	logger.log(Level.WARNING, () -> "Tipo di valutazione non supportato: " + evalType);
	                        break;
	                }
	            } catch (Exception e) {
	                logger.log(Level.INFO, "Errore durante la valutazione del modello");
	            }
	            break;
	        }
	    }

	    if (ev == null) {
	        logger.log(Level.INFO, "Cost evaluation non valida");
	    }

	    return ev;
	}

	//peso assegnato alla matrice di costo
	private static CostMatrix createCostMatrix(double weightFalsePositive, double weightFalseNegative) {
		CostMatrix costMatrix = new CostMatrix(2); 
	    costMatrix.setCell(0, 0, 0.0); 
	    costMatrix.setCell(1, 0, weightFalsePositive); 
	    costMatrix.setCell(0, 1, weightFalseNegative); 
	    costMatrix.setCell(1, 1, 0.0); 
	    return costMatrix;
	}




	//Metodo di controllo dell'applicativo
	public static void createFile(String path) throws Exception {
	    logger.info("Creando il file di output");
	    ArrayList<Instances> sets = ordering(path);
	    List<ExperimentParams> paramsList = getModelConfigurations();
	    List<ClassifierInfo> measures = computeMeasures(paramsList, sets);
	    toCSV(measures);
	    logger.info("File creato!");
	}
	

	public static List<ExperimentParams> getModelConfigurations() {
	    List<ExperimentParams> experimentParamsList = new ArrayList<>();
	    for (String featureSelection : Arrays.asList("NO", "BEST FIRST")) {
	        for (String balancing : Arrays.asList("NO", "UNDERSAMPLING", "OVERSAMPLING", "SMOTE")) {
	            for (String costMatrix : Arrays.asList("NO", SENSITIVE_THRESHOLD, SENSITIVE_LEARNING)) {
	                for (String classifier : Arrays.asList("RANDOM FOREST", "NAIVE BAYES", "IBK")) {
	                    ExperimentParams experimentParams = new ExperimentParams(featureSelection, balancing, costMatrix, classifier);
	                    experimentParamsList.add(experimentParams);
	                }
	            }
	        }
	    }
	    return experimentParamsList;
	}



	    
	public static List<ClassifierInfo> computeMeasures(List<ExperimentParams> paramsList, List<Instances> sets) throws Exception {
	    List<ClassifierInfo> measures = new ArrayList<>();
	    weka weka = new weka();
	    for (ExperimentParams params : paramsList) {
		    logger.info("Walk Forward");

	        weka.walkForward(params, sets, measures);
	    }
	    return measures;
	}


	
	//ordina istanze dataset in base alla versione
	private static ArrayList<Instances> ordering(String path) throws Exception {
	    Instances data = DataSource.read(path);
	    data.sort(0);
	    return extractVersions(data);
	}

	
	//ordina le istanze in base al numero di versione
	private static ArrayList<Instances> extractVersions(Instances data) {
	    return IntStream.rangeClosed(1, (int) data.lastInstance().value(0))
	            .mapToObj(version -> extractInstancesForVersion(data, version))
	            .collect(Collectors.toCollection(ArrayList::new));
	}

	private static Instances extractInstancesForVersion(Instances data, int version) {
	    
	    return data.stream()
	            .filter(instance -> (int) instance.value(0) == version)
	            .collect(Collectors.toCollection(() -> {
	                Instances instances = new Instances(data, 0);
	                instances.setRelationName("version_" + version);
	                return instances;
	            }));
	}


	
	public static void toCSV(List<ClassifierInfo> measures) {
	    String outName = projectName + "Output.csv";
	    
	    try (PrintWriter writer = new PrintWriter(new FileWriter(outName))) {
	        writer.println("Dataset,#TrainingRelease,Classifier,Balancing,Feature Selection,Sensitivity,TP,FP,TN,FN,Precision,Recall,AUC,Kappa");
	        
	        measures.forEach(measure -> createCSV(writer, measure));

	    } catch (IOException e) {
	        logger.log(Level.INFO, "Errore durante la scrittura del csv.");
	    }
	}

	private static void createCSV(PrintWriter writer, ClassifierInfo measure)  {
	    String[] fields = {projectName, measure.getRelease().toString(), 
	        measure.getClassifierType(), measure.getBalancing(), measure.getFeatureSelection(), measure.getSensitivity(),
	        measure.getTp().toString(), measure.getFp().toString(), measure.getTn().toString(), measure.getFn().toString(),
	        measure.getPrecision().toString(), measure.getRecall().toString(), measure.getAuc().toString(),
	        measure.getKappa().toString()};

	    for (int i = 0; i < fields.length; i++) {
	        writer.append(fields[i]);
	        writer.append(",");
	    }
	    writer.append("\n");
	}


		
	public static Classifier chooseClassificationType(String type) {
		Map<String, Supplier<Classifier>> classifierMap = new HashMap<>();
	    classifierMap.put("RANDOM FOREST", RandomForest::new);
	    classifierMap.put("NAIVE BAYES", NaiveBayes::new);
	    classifierMap.put("IBK", IBk::new);

	    return classifierMap.getOrDefault(type, () -> null).get();
	}


}
