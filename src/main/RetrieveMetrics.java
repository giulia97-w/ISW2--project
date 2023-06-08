



package main;

import org.eclipse.jgit.api.Git;
import org.eclipse.jgit.api.errors.GitAPIException;
import org.eclipse.jgit.diff.DiffEntry;
import org.eclipse.jgit.diff.DiffEntry.ChangeType;
import org.eclipse.jgit.diff.DiffFormatter;
import org.eclipse.jgit.diff.Edit;
import org.eclipse.jgit.diff.RawTextComparator;
import org.eclipse.jgit.lib.ObjectId;
import org.eclipse.jgit.lib.ObjectLoader;
import org.eclipse.jgit.lib.ObjectReader;
import org.eclipse.jgit.lib.Repository;
import org.eclipse.jgit.patch.FileHeader;
import org.eclipse.jgit.revwalk.RevCommit;
import org.eclipse.jgit.revwalk.RevTree;
import org.eclipse.jgit.revwalk.RevWalk;
import org.eclipse.jgit.storage.file.FileRepositoryBuilder;
import org.eclipse.jgit.treewalk.CanonicalTreeParser;
import org.eclipse.jgit.treewalk.EmptyTreeIterator;
import org.eclipse.jgit.treewalk.TreeWalk;
import org.eclipse.jgit.util.io.DisabledOutputStream;
import org.json.JSONException;

import weka.core.Instances;
import weka.core.converters.ArffSaver;
import weka.core.converters.CSVLoader;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.lang.reflect.InvocationTargetException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.Instant;
import java.time.LocalDateTime;
import java.time.ZoneId;
import java.util.*;
import java.util.function.Supplier;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;
import java.util.stream.IntStream;


public class RetrieveMetrics {
	
	public static final String BOOKKEEPER = "BOOKKEEPER";
	public static final String SYNCOPE = "SYNCOPE";
	public static final String OPENJPA = "OPENJPA";
	public static final String TAJO = "TAJO";
	public static final String ACCUMULO = "ACCUMULO";
	public static final String STORM = "STORM";
	public static final String AVRO = "AVRO";
	static String nameGit = "git";
	static String endPath = "/." + nameGit ;
	
	static String name = "giuliamenichini";
	static String percorso = "/Users/" + name + "/";
	static String percorsoProportion = "/Users/" + name + "/eclipse-workspace/ISW2/";
	public static final String PATH = System.getProperty("user.dir") + File.separator;
	public static final String DATASET_FILENAME = "Dataset.csv";
	public static final String URI_OPENJPA = PATH + OPENJPA + DATASET_FILENAME;
	public static final String URI_BOOKKEEPER = PATH + BOOKKEEPER + DATASET_FILENAME;


	static String uriArffOpenjpa = PATH +OPENJPA+"Dataset.arff";
	static String uriArffBookkeeper = PATH+BOOKKEEPER+"Dataset.arff";

	private static int movingWindowsCount;

	private static final String ENDFILE = ".java";
	private static final String DELETE = "DELETE";
	//scrittura file su stringa 
	private static void update(BufferedWriter fileWriter, Release release, JavaFile file) throws IOException {
	    StringBuilder sb = new StringBuilder();
	    sb.append(release.getIndex()).append(",");
	    sb.append(file.getName()).append(",");
	    
	    sb.append(file.getlinesOfCode()).append(",");
	    sb.append(file.getLocTouched()).append(",");

	    sb.append(file.getlinesOfCodeadded()).append(",");

	    // ciclo for per scrivere i valori massimi e medi di linesOfCodeAddedList
	    List<Integer> linesOfCodeAddedList = file.getlinesOfCodeAddedList();
	    int maxLOCAdded = 0;
	    double avgLOCAdded = 0;
	    for (int i = 0; i < linesOfCodeAddedList.size(); i++) {
	        int locAdded = linesOfCodeAddedList.get(i);
	        maxLOCAdded = Math.max(maxLOCAdded, locAdded);
	        avgLOCAdded += locAdded;
	    }
	    avgLOCAdded /= linesOfCodeAddedList.size();
	    sb.append(maxLOCAdded).append(",").append(avgLOCAdded).append(",");

	    sb.append(file.getChurn()).append(",");

	    // ciclo for per scrivere i valori massimi e medi di churnList
	    List<Integer> churnList = file.getChurnList();
	    int maxChurn = 0;
	    double avgChurn = 0;
	    for (int i = 0; i < churnList.size(); i++) {
	        int churn = churnList.get(i);
	        maxChurn = Math.max(maxChurn, churn);
	        avgChurn += churn;
	    }
	    avgChurn /= churnList.size();
	    sb.append(maxChurn).append(",").append(avgChurn).append(",");

	    sb.append(file.getNr()).append(",");
	    sb.append(file.getNAuth().size()).append(",");
	    sb.append(file.getBuggyness()).append("\n");

	    fileWriter.write(sb.toString());
	    fileWriter.flush();
	}
	
    private static void linkFunction() {
    	linkage();
        setResolutionDateAndFVBookkeeper();
        setResolutionDateAndFVOpenjpa();
        setResolutionDateAndFVAvro();
        setResolutionDateAndFVZookkeeper();
        setResolutionDateAndFVStorm();
        setResolutionDateAndFVTajo();
        setResolutionDateAndFVSyncope();
        removeUnlinkedTickets();
    }
    //restituisce data del commit
    private static LocalDateTime getCommitDate(RevCommit commit) {
        Instant commitInstant = Instant.ofEpochSecond(commit.getAuthorIdent().getWhen().getTime());
        return LocalDateTime.ofInstant(commitInstant, ZoneId.systemDefault());
    }
    //aggiunge il commit alla lista dei commit
    private static void addCommitToTicket(Ticket ticket, RevCommit commit) {
        ticket.getCommitList().add(commit);
    }
    //restituisce lista di date dei commit associate al ticket
    private static List<LocalDateTime> findCommitDatesForTicket(Ticket ticket, List<RevCommit> commitList) {
    	
        return commitList.stream()
                         .filter(commit -> commit.getFullMessage().contains(ticket.getTicketID()))
                         .map(commit -> {
                             addCommitToTicket(ticket, commit);
                             return getCommitDate(commit);
                         })
                         .collect(Collectors.toList());
    }

    private static void updateTicketCommitDatesAvro() {
        for (Ticket ticket : ticketListAvro) {
            List<LocalDateTime> commitDateList = findCommitDatesForTicket(ticket, commitListAvro);
            ticket.setCommitDateList(commitDateList);
        }
    }
    private static void updateTicketCommitDatesTajo() {
        for (Ticket ticket : ticketListTajo) {
            List<LocalDateTime> commitDateList = findCommitDatesForTicket(ticket, commitListTajo);
            ticket.setCommitDateList(commitDateList);
        }
    }

    //aggiorna la lista dei committ associati ai ticket per il progetto bookkeeper
    private static void updateTicketCommitDatesBookkeeper() {
        for (Ticket ticket : ticketListBookkeeper) {
            List<LocalDateTime> commitDateList = findCommitDatesForTicket(ticket, commitListBookkeeper);
            ticket.setCommitDateList(commitDateList);
        }
    }
    //aggiorna la lista dei committ associati ai ticket per il progetto openjpa

    private static void updateTicketCommitDatesOpenjpa() {
        for (Ticket ticket : ticketListOpenjpa) {
            List<LocalDateTime> commitDateList = findCommitDatesForTicket(ticket, commitListOpenjpa);
            ticket.setCommitDateList(commitDateList);
        }
    }
    private static void updateTicketCommitDatesZookkeeper() {
        for (Ticket ticket : ticketListAccumulo) {
            List<LocalDateTime> commitDateList = findCommitDatesForTicket(ticket, commitListAccumulo);
            ticket.setCommitDateList(commitDateList);
        }
    }
    
    private static void updateTicketCommitDatesStorm() {
        for (Ticket ticket : ticketListStorm) {
            List<LocalDateTime> commitDateList = findCommitDatesForTicket(ticket, commitListStorm);
            ticket.setCommitDateList(commitDateList);
        }
    }
    private static void updateTicketCommitDatesSyncope() {
        for (Ticket ticket : ticketListSyncope) {
            List<LocalDateTime> commitDateList = findCommitDatesForTicket(ticket, commitListSyncope);
            ticket.setCommitDateList(commitDateList);
        }
    }
    
    private static void linkage() {
        updateTicketCommitDatesAvro();
        updateTicketCommitDatesBookkeeper();
        updateTicketCommitDatesOpenjpa();
        updateTicketCommitDatesZookkeeper();
        updateTicketCommitDatesStorm();
        updateTicketCommitDatesTajo();
        updateTicketCommitDatesSyncope();

    }


    //aggiorna data di risoluzione e la versione fixed version per ogni ticket
    private static void setResolutionDateAndFVBookkeeper() {
        for (Ticket ticket : ticketListBookkeeper) {
            ArrayList<LocalDateTime> commitDateList = ticket.getCommitList().stream()
                    .map(commit -> commit.getAuthorIdent().getWhen().toInstant().atZone(ZoneId.systemDefault()).toLocalDateTime())
                    .sorted()
                    .collect(Collectors.toCollection(ArrayList::new));

            Optional<LocalDateTime> latestCommitDate = commitDateList.stream()
                    .max(LocalDateTime::compareTo);

            latestCommitDate.ifPresent(resolutionDate -> {
                ticket.setResolutionDate(resolutionDate);
                ticket.setFixedVersion(afterBeforeDate(resolutionDate, releasesListBookkeeper));
            }); }

    }
    
  //aggiorna data di risoluzione e la versione fixed version per ogni ticket
    private static void setResolutionDateAndFVSyncope() {
        for (Ticket ticket : ticketListSyncope) {
            ArrayList<LocalDateTime> commitDateList = ticket.getCommitList().stream()
                    .map(commit -> commit.getAuthorIdent().getWhen().toInstant().atZone(ZoneId.systemDefault()).toLocalDateTime())
                    .sorted()
                    .collect(Collectors.toCollection(ArrayList::new));

            Optional<LocalDateTime> latestCommitDate = commitDateList.stream()
                    .max(LocalDateTime::compareTo);

            latestCommitDate.ifPresent(resolutionDate -> {
                ticket.setResolutionDate(resolutionDate);
                ticket.setFixedVersion(afterBeforeDate(resolutionDate, releasesListSyncope));
            }); }

    }
    
  //aggiorna data di risoluzione e la versione fixed version per ogni ticket
    private static void setResolutionDateAndFVZookkeeper() {
        for (Ticket ticket : ticketListAccumulo) {
            ArrayList<LocalDateTime> commitDateList = ticket.getCommitList().stream()
                    .map(commit -> commit.getAuthorIdent().getWhen().toInstant().atZone(ZoneId.systemDefault()).toLocalDateTime())
                    .sorted()
                    .collect(Collectors.toCollection(ArrayList::new));

            Optional<LocalDateTime> latestCommitDate = commitDateList.stream()
                    .max(LocalDateTime::compareTo);

            latestCommitDate.ifPresent(resolutionDate -> {
                ticket.setResolutionDate(resolutionDate);
                ticket.setFixedVersion(afterBeforeDate(resolutionDate, releasesListAccumulo));
            }); }

    }
    
  //aggiorna data di risoluzione e la versione fixed version per ogni ticket
    private static void setResolutionDateAndFVTajo() {
        for (Ticket ticket : ticketListTajo) {
            ArrayList<LocalDateTime> commitDateList = ticket.getCommitList().stream()
                    .map(commit -> commit.getAuthorIdent().getWhen().toInstant().atZone(ZoneId.systemDefault()).toLocalDateTime())
                    .sorted()
                    .collect(Collectors.toCollection(ArrayList::new));

            Optional<LocalDateTime> latestCommitDate = commitDateList.stream()
                    .max(LocalDateTime::compareTo);

            latestCommitDate.ifPresent(resolutionDate -> {
                ticket.setResolutionDate(resolutionDate);
                ticket.setFixedVersion(afterBeforeDate(resolutionDate, releasesListTajo));
            }); }

    }
    private static void setResolutionDateAndFVAvro() {
        for (Ticket ticket : ticketListAvro) {
            ArrayList<LocalDateTime> commitDateList = ticket.getCommitList().stream()
                    .map(commit -> commit.getAuthorIdent().getWhen().toInstant().atZone(ZoneId.systemDefault()).toLocalDateTime())
                    .sorted()
                    .collect(Collectors.toCollection(ArrayList::new));

            Optional<LocalDateTime> latestCommitDate = commitDateList.stream()
                    .max(LocalDateTime::compareTo);

            latestCommitDate.ifPresent(resolutionDate -> {
                ticket.setResolutionDate(resolutionDate);
                ticket.setFixedVersion(afterBeforeDate(resolutionDate, releasesListAvro));
            }); }

    }
    private static void setResolutionDateAndFVStorm() {
        for (Ticket ticket : ticketListStorm) {
            ArrayList<LocalDateTime> commitDateList = ticket.getCommitList().stream()
                    .map(commit -> commit.getAuthorIdent().getWhen().toInstant().atZone(ZoneId.systemDefault()).toLocalDateTime())
                    .sorted()
                    .collect(Collectors.toCollection(ArrayList::new));

            Optional<LocalDateTime> latestCommitDate = commitDateList.stream()
                    .max(LocalDateTime::compareTo);

            latestCommitDate.ifPresent(resolutionDate -> {
                ticket.setResolutionDate(resolutionDate);
                ticket.setFixedVersion(afterBeforeDate(resolutionDate, releasesListStorm));
            }); }
    }
    private static void setResolutionDateAndFVOpenjpa() {
        for (Ticket ticket : ticketListOpenjpa) {
            ArrayList<LocalDateTime> commitDateList = ticket.getCommitList().stream()
                    .map(commit -> commit.getAuthorIdent().getWhen().toInstant().atZone(ZoneId.systemDefault()).toLocalDateTime())
                    .sorted()
                    .collect(Collectors.toCollection(ArrayList::new));

            Optional<LocalDateTime> latestCommitDate = commitDateList.stream()
                    .max(LocalDateTime::compareTo);

            latestCommitDate.ifPresent(resolutionDate -> {
                ticket.setResolutionDate(resolutionDate);
                ticket.setFixedVersion(afterBeforeDate(resolutionDate, releasesListOpenjpa));
            }); }
    }
    //rimuove ticket che non sono stati associati a nessun commit
    private static void removeUnlinkedTickets() {
        ticketListBookkeeper.removeIf(ticket -> ticket.getResolutionDate() == null);
        ticketListOpenjpa.removeIf(ticket -> ticket.getResolutionDate() == null);
        ticketListAvro.removeIf(ticket -> ticket.getResolutionDate() == null);
        ticketListAccumulo.removeIf(ticket -> ticket.getResolutionDate() == null);
        ticketListSyncope.removeIf(ticket -> ticket.getResolutionDate() == null);



    }


    

    //rimuove la metà della lista delle release assieme ai ticket associati alle release rimosse
    public static void removeObsoleteReleasesAndTickets(List<Release> releases, List<Ticket> tickets) {
    	int halfwayIndex = releases.size() / 2;
    	// Rimuove le release oltre il punto medio
    	releases.removeIf(release -> release.getIndex() > halfwayIndex);

    	// Rimuove i ticket obsoleti sulla base della versione iniettata, della data di risoluzione e della versione corretta
    	tickets.removeIf(ticket -> ticket.getInjectedVersion() > halfwayIndex || 
    	                           ticket.getResolutionDate() == null ||
    	                           ticket.getFixedVersion() > halfwayIndex);
    }
    


    
    
    /* IV != 0 -> AV else ERRORE
     * Se OV = 1 IV = 1, se FV = 1 -> AV = empty else setAV
     * Se OV != 1 se FV = OV, IV = OV -> AV = FV - IV
     * Se OV != 1 se FV != OV  set AV
     *  */

    //verifica che vengano rispettate determinate condizioni e setta AV
    public static void checkTicketBookkeeper() {
        ticketListBookkeeper.stream()
            .filter(ticket -> ticket.getInjectedVersion() != 0)
            .forEach(ticket -> {
                if (ordering(ticket)) {
                    List<Integer> affectedVersions = new ArrayList<>();
                    for (int i = ticket.getInjectedVersion(); i < ticket.getFixedVersion(); i++) {
                        affectedVersions.add(i);
                    }
                    ticket.setAffectedVersion(affectedVersions);
                } else {
                    setErrorTicket(ticket);
                }
                handleOV(ticket);
            });
    }
    
  //verifica che vengano rispettate determinate condizioni e setta AV
    public static void checkTicketSyncope() {
        ticketListSyncope.stream()
            .filter(ticket -> ticket.getInjectedVersion() != 0)
            .forEach(ticket -> {
                if (ordering(ticket)) {
                    List<Integer> affectedVersions = new ArrayList<>();
                    for (int i = ticket.getInjectedVersion(); i < ticket.getFixedVersion(); i++) {
                        affectedVersions.add(i);
                    }
                    ticket.setAffectedVersion(affectedVersions);
                } else {
                    setErrorTicket(ticket);
                }
                handleOV(ticket);
            });
    }
    
    public static void checkTicketAvro() {
        ticketListAvro.stream()
            .filter(ticket -> ticket.getInjectedVersion() != 0)
            .forEach(ticket -> {
                if (ordering(ticket)) {
                    List<Integer> affectedVersions = new ArrayList<>();
                    for (int i = ticket.getInjectedVersion(); i < ticket.getFixedVersion(); i++) {
                        affectedVersions.add(i);
                    }
                    ticket.setAffectedVersion(affectedVersions);
                } else {
                    setErrorTicket(ticket);
                }
                handleOV(ticket);
            });
    }
    
    public static void checkTicketTajo() {
        ticketListTajo.stream()
            .filter(ticket -> ticket.getInjectedVersion() != 0)
            .forEach(ticket -> {
                if (ordering(ticket)) {
                    List<Integer> affectedVersions = new ArrayList<>();
                    for (int i = ticket.getInjectedVersion(); i < ticket.getFixedVersion(); i++) {
                        affectedVersions.add(i);
                    }
                    ticket.setAffectedVersion(affectedVersions);
                } else {
                    setErrorTicket(ticket);
                }
                handleOV(ticket);
            });
    }
    
    public static void checkTicketStorm() {
        ticketListStorm.stream()
            .filter(ticket -> ticket.getInjectedVersion() != 0)
            .forEach(ticket -> {
                if (ordering(ticket)) {
                    List<Integer> affectedVersions = new ArrayList<>();
                    for (int i = ticket.getInjectedVersion(); i < ticket.getFixedVersion(); i++) {
                        affectedVersions.add(i);
                    }
                    ticket.setAffectedVersion(affectedVersions);
                } else {
                    setErrorTicket(ticket);
                }
                handleOV(ticket);
            });
    }
    
    public static void checkTicketZookkeeper() {
        ticketListAccumulo.stream()
            .filter(ticket -> ticket.getInjectedVersion() != 0)
            .forEach(ticket -> {
                if (ordering(ticket)) {
                    List<Integer> affectedVersions = new ArrayList<>();
                    for (int i = ticket.getInjectedVersion(); i < ticket.getFixedVersion(); i++) {
                        affectedVersions.add(i);
                    }
                    ticket.setAffectedVersion(affectedVersions);
                } else {
                    setErrorTicket(ticket);
                }
                handleOV(ticket);
            });
    }


    
    public static void checkTicketOpenjpa() {
        ticketListOpenjpa.stream()
            .filter(ticket -> ticket.getInjectedVersion() != 0)
            .forEach(ticket -> {
                if (ordering(ticket)) {
                    List<Integer> affectedVersions = new ArrayList<>();
                    for (int i = ticket.getInjectedVersion(); i < ticket.getFixedVersion(); i++) {
                        affectedVersions.add(i);
                    }
                    ticket.setAffectedVersion(affectedVersions);
                } else {
                    setErrorTicket(ticket);
                }
                handleOV(ticket);
            });
    }


    //gestisce OV, se è uguale a 1
    private static void handleOV(Ticket ticket) {
        if (ticket.getOpenVersion() == 1) {
            handleOVEquals1(ticket);
        } else {
            handleOVNotEquals1(ticket);
        }
    }


    //verifica ordinamento ticket in base alla IV OV e FV
    private static boolean ordering(Ticket ticket) {
        return ticket.getFixedVersion() > ticket.getInjectedVersion() && ticket.getOpenVersion() >= ticket.getInjectedVersion();
    }

    //importa la AV 0 se FV = IV
    private static void setErrorTicket(Ticket ticket) {
    	List<Integer> av = new ArrayList<>();
    	av.add(0);
    	ticket.setAffectedVersion(av);
    	ticket.setInjectedVersion(0);
    	if (ticket.getFixedVersion().equals(ticket.getInjectedVersion())) {
    		ticket.getAffectedVersion().clear();
    	}
    }



    //se FV = 1 AV = 0 altrimenti AV = [IV,FV)
    private static void handleOVEquals1(Ticket ticket) {
    	ticket.setInjectedVersion(1);
    	if (ticket.getFixedVersion() == 1) {
    		ticket.setAffectedVersion(Collections.emptyList());
    	} else {
    		List<Integer> avList = IntStream.range(ticket.getInjectedVersion(), ticket.getFixedVersion())
		    	.boxed()
		    	.collect(Collectors.toList());
		    	ticket.setAffectedVersion(avList);
    	}
    	}
    //se IV = OV AV = FV - OV se OV > FV -> clear
    private static void handleOVLessThanFV(Ticket ticket) {
        ticket.setInjectedVersion(ticket.getOpenVersion()); 
        int numAV = ticket.getFixedVersion() - ticket.getOpenVersion(); 
        ticket.setAffectedVersion(IntStream.range(ticket.getInjectedVersion(), ticket.getFixedVersion()).boxed().collect(Collectors.toList()));
        if (numAV <= 0) {
            ticket.getAffectedVersion().clear(); 
        }
    }

    //set AV
    private static void handleOVMoreThanFV(Ticket ticket) {
        int targetInjectedVersion = ticket.getInjectedVersion();
        OptionalInt validIV = IntStream.rangeClosed(targetInjectedVersion, ticket.getFixedVersion() - 1)
                                       .filter(v -> isIVValid(ticket, v))
                                       .findFirst();
        if (validIV.isPresent()) {
            ticket.setInjectedVersion(validIV.getAsInt());
            ticket.setAffectedVersion(IntStream.rangeClosed(ticket.getInjectedVersion(), ticket.getFixedVersion() - 1)
                                               .boxed()
                                               .collect(Collectors.toList()));
        } else {
            ticket.setAffectedVersion(Collections.singletonList(0));
            ticket.setInjectedVersion(0);
        }
    }

    //se FV <= OV 
    private static void handleOVNotEquals1(Ticket ticket) {        

    	if (ticket.getFixedVersion().equals(ticket.getOpenVersion())) {
    	    
            handleOVLessThanFV(ticket);
        } else { 
            handleOVMoreThanFV(ticket);
        }
    }
    private static boolean isIVValid(Ticket ticket, int injectedVersion) {
        return  injectedVersion >= 1 && injectedVersion <= ticket.getOpenVersion() && injectedVersion < ticket.getFixedVersion();
    }

    public static void createCSV(List<Release> releases, String projectName) {
    	String fileName = DATASET_FILENAME;
        try (BufferedWriter writer = Files.newBufferedWriter(Paths.get(projectName.toLowerCase() + fileName))) {
            // Creazione del file CSV e scrittura dell'intestazione.
            writer.write("RELEASE,FILENAME,SIZE,LOC_TOUCHED,LOC_added,MAX_LOC_Added,AVG_LOC_Added,CHURN,MAX_Churn,AVG_Churn,NR,NAUTH,BUGGYNESS\n");

            // Scrittura dei dati relativi a ciascun file per ogni release.
            for (Release release : releases) {
                writeReleaseMetrics(writer, release);
            }
        } catch (IOException e) {
            logger.log(Level.SEVERE, "Errore nella creazione del dataset", e);
        }
    }

    private static void writeReleaseMetrics( BufferedWriter fileWriter, Release release) throws IOException {
    		for (JavaFile file : release.getFile()) {
    		update(fileWriter, release, file);
    		}
    	}

   
    private static final Logger logger = Logger.getLogger(RetrieveMetrics.class.getName());


    private static List<Release> releasesListBookkeeper;
    private static List<Release> releasesListOpenjpa;
    private static List<Ticket> ticketListBookkeeper;
    private static List<Ticket> ticketListOpenjpa;
    private static List<RevCommit> commitListBookkeeper;
    private static List<RevCommit> commitListOpenjpa;
    private static List<Release> releasesListAvro;
    private static List<Ticket> ticketListAvro;
    private static List<RevCommit> commitListAvro;
    private static List<Release> releasesListAccumulo;
    private static List<Ticket> ticketListAccumulo;
    private static List<RevCommit> commitListAccumulo;
    private static List<Release> releasesListStorm;
    private static List<Ticket> ticketListStorm;
    private static List<RevCommit> commitListStorm;
    private static List<Release> releasesListTajo;
    private static List<Ticket> ticketListTajo;
    private static List<RevCommit> commitListTajo;
    private static List<Release> releasesListSyncope;
    private static List<Ticket> ticketListSyncope;
    private static List<RevCommit> commitListSyncope;

    public static void main(String[] args) throws IllegalStateException, GitAPIException, IOException, JSONException, NoSuchMethodException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, SecurityException {
    	
    	
        releasesListBookkeeper = Release.getListRelease(BOOKKEEPER);
        releasesListOpenjpa = Release.getListRelease(OPENJPA);
        commitListBookkeeper = getAllCommits(releasesListBookkeeper, Paths.get(percorso + BOOKKEEPER.toLowerCase()));
        commitListOpenjpa = getAllCommits(releasesListOpenjpa, Paths.get(percorso + OPENJPA.toLowerCase()));
        ticketListBookkeeper = Ticket.getTickets(releasesListBookkeeper, BOOKKEEPER);
        ticketListOpenjpa = Ticket.getTickets(releasesListOpenjpa, OPENJPA);
        

        releasesListAvro = Release.getListRelease(AVRO);
        commitListAvro = getAllCommits(releasesListAvro, Paths.get(percorso + AVRO.toLowerCase()));
        ticketListAvro = Ticket.getTickets(releasesListAvro, AVRO);
        releasesListAccumulo = Release.getListRelease(ACCUMULO);
        commitListAccumulo = getAllCommits(releasesListAccumulo, Paths.get(percorso + ACCUMULO.toLowerCase()));
        ticketListAccumulo = Ticket.getTickets(releasesListAccumulo, ACCUMULO.toLowerCase());
        releasesListStorm = Release.getListRelease(STORM);
        commitListStorm = getAllCommits(releasesListStorm, Paths.get(percorso + STORM.toLowerCase()));
        ticketListStorm = Ticket.getTickets(releasesListStorm, STORM);
        releasesListTajo = Release.getListRelease(TAJO);
        commitListTajo = getAllCommits(releasesListTajo, Paths.get(percorso + TAJO.toLowerCase()));
        ticketListTajo = Ticket.getTickets(releasesListTajo, TAJO);
        releasesListSyncope = Release.getListRelease(SYNCOPE);
        commitListSyncope = getAllCommits(releasesListSyncope, Paths.get(percorso + SYNCOPE.toLowerCase()));
        ticketListSyncope = Ticket.getTickets(releasesListSyncope, SYNCOPE);
        
       //SYNCOPE
        linkFunction();
        removeObsoleteReleasesAndTickets(releasesListSyncope, ticketListSyncope);
        checkTicketSyncope(); 
        FileRepositoryBuilder repositoryBuilderSyncope = new FileRepositoryBuilder();
        repository = repositoryBuilderSyncope.setGitDir(new File(percorso + SYNCOPE.toLowerCase() + endPath)).readEnvironment().findGitDir().setMustExist(true).build();
        Collections.reverse(ticketListSyncope); 
        Ticket.ticketDataset(ticketListSyncope, SYNCOPE);
        logger.log(Level.INFO, "P SYNCOPE: ");
        obtainingPOtherProject(ticketListSyncope);
        
        //TAJO
        linkFunction();
        removeObsoleteReleasesAndTickets(releasesListTajo, ticketListTajo);
        checkTicketTajo(); 
        FileRepositoryBuilder repositoryBuilderTajo = new FileRepositoryBuilder();
        repository = repositoryBuilderTajo.setGitDir(new File(percorso + TAJO.toLowerCase() + endPath)).readEnvironment().findGitDir().setMustExist(true).build();
        Collections.reverse(ticketListTajo); 
        Ticket.ticketDataset(ticketListTajo, TAJO);
        logger.log(Level.INFO, "P TAJO: ");
        obtainingPOtherProject(ticketListTajo);
        
        
        //STORM
        linkFunction();
        removeObsoleteReleasesAndTickets(releasesListStorm, ticketListStorm);
        checkTicketStorm(); 
        FileRepositoryBuilder repositoryBuilderStorm = new FileRepositoryBuilder();
        repository = repositoryBuilderStorm.setGitDir(new File(percorso + "storm" + endPath)).readEnvironment().findGitDir().setMustExist(true).build();
        Collections.reverse(ticketListStorm); 
        Ticket.ticketDataset(ticketListStorm, STORM);
        logger.log(Level.INFO, "P STORM: ");
        obtainingPOtherProject(ticketListStorm);
        
        //AVRO
        linkFunction();
        removeObsoleteReleasesAndTickets(releasesListAvro, ticketListAvro);
        checkTicketAvro(); 
        FileRepositoryBuilder repositoryBuilderAvro = new FileRepositoryBuilder();
        repository = repositoryBuilderAvro.setGitDir(new File(percorso + "avro" + endPath)).readEnvironment().findGitDir().setMustExist(true).build();
        Collections.reverse(ticketListAvro); 
        Ticket.ticketDataset(ticketListAvro, AVRO);
        logger.log(Level.INFO, "P AVRO: ");
        obtainingPOtherProject(ticketListAvro);
        
        //ACCUMULO
        linkFunction();
        removeObsoleteReleasesAndTickets(releasesListAccumulo, ticketListAccumulo);
        checkTicketZookkeeper(); 
        FileRepositoryBuilder repositoryBuilderZookkeeper = new FileRepositoryBuilder();
        repository = repositoryBuilderZookkeeper.setGitDir(new File(percorso + ACCUMULO.toLowerCase() + endPath)).readEnvironment().findGitDir().setMustExist(true).build();
        Collections.reverse(ticketListAccumulo); 
        Ticket.ticketDataset(ticketListAccumulo,ACCUMULO);
        logger.log(Level.INFO, "P ACCUMULO: ");
        obtainingPOtherProject(ticketListAccumulo);
        medianP(ticketListAvro, ticketListAccumulo, ticketListStorm, ticketListTajo,ticketListSyncope);
        
        
        //salvataggio file per proportion
        String filename = percorsoProportion + "proportion.csv";
        writeProjectsToFile(filename);
        
        
        //Bookkeeper
        linkFunction();
        removeObsoleteReleasesAndTickets(releasesListBookkeeper, ticketListBookkeeper);
        checkTicketBookkeeper(); 
        FileRepositoryBuilder repositoryBuilderBookkeeper = new FileRepositoryBuilder();
        repository = repositoryBuilderBookkeeper.setGitDir(new File(percorso + BOOKKEEPER.toLowerCase() + endPath)).readEnvironment().findGitDir().setMustExist(true).build();
        Collections.reverse(ticketListBookkeeper); 

        findProportion(ticketListBookkeeper);
        checkTicketBookkeeper(); 
        Ticket.ticketDataset(ticketListBookkeeper, BOOKKEEPER);

        getJavaFiles(Paths.get(percorso + BOOKKEEPER.toLowerCase()), releasesListBookkeeper);
        isBuggy(releasesListBookkeeper, ticketListBookkeeper); 
        getRepo(releasesListBookkeeper, percorso + BOOKKEEPER.toLowerCase() + endPath);
        createCSV(releasesListBookkeeper, BOOKKEEPER.toLowerCase());
        
        //openjpa
        linkFunction();
        removeObsoleteReleasesAndTickets(releasesListOpenjpa, ticketListOpenjpa);
        checkTicketOpenjpa();
        FileRepositoryBuilder repositoryBuilderOpenjpa = new FileRepositoryBuilder();
        repository = repositoryBuilderOpenjpa.setGitDir(new File(percorso + OPENJPA.toLowerCase() + endPath)).readEnvironment().findGitDir().setMustExist(true).build();              
        Collections.reverse(ticketListOpenjpa);
        Ticket.ticketDataset(ticketListOpenjpa, OPENJPA);

        findProportion(ticketListOpenjpa);
        checkTicketOpenjpa(); 

        getJavaFiles(Paths.get(percorso + OPENJPA.toLowerCase()), releasesListOpenjpa);
        isBuggy(releasesListOpenjpa, ticketListOpenjpa); 
        getRepo(releasesListOpenjpa, percorso + OPENJPA.toLowerCase() + endPath);
        createCSV(releasesListOpenjpa, OPENJPA.toLowerCase());
        logger.log(Level.INFO, "Creando il file .Arff");
        
        //csvLoader openjpa
        CSVLoader loaderOpenjpa = new CSVLoader();
        loaderOpenjpa.setSource(new File(URI_OPENJPA));
        Instances dataOpenjpa = loaderOpenjpa.getDataSet();

        // Salva il file ARFF Openjpa
        ArffSaver saverOpenjpa = new ArffSaver();
        saverOpenjpa.setInstances(dataOpenjpa);
        saverOpenjpa.setFile(new File(uriArffOpenjpa));
        saverOpenjpa.writeBatch();
        logger.log(Level.INFO, "File openjpaDataset.Arff creato");
        
        //csvLoader bookkeeper
        CSVLoader loaderBookkeeper = new CSVLoader();
        loaderBookkeeper.setSource(new File(URI_BOOKKEEPER));
        Instances dataBookkeeper = loaderBookkeeper.getDataSet();
        
        
        // Salva il file ARFF bookkeeper
        ArffSaver saverBookkeeper = new ArffSaver();
        saverBookkeeper.setInstances(dataBookkeeper);
        saverBookkeeper.setFile(new File(uriArffBookkeeper));
        saverBookkeeper.writeBatch();
        logger.log(Level.INFO, "File bookkeeperDataset.Arff creato");
        
        
    
    }
    
  
    //accesso alla repo di git
    public static void getRepo(List<Release> releasesList, String repo) throws IOException {
        FileRepositoryBuilder repositoryBuilder = new FileRepositoryBuilder();
        Repository repository = repositoryBuilder.setGitDir(new File(repo))
            .readEnvironment()
            .findGitDir()
            .setMustExist(true)
            .build();

        analyzeMetrics(releasesList, repository);
    }
    //per ogni file java nella repo calcola metriche
    public static void analyzeMetrics(List<Release> releasesList, Repository repository) {
        releasesList.forEach(release -> {
            List<JavaFile> javaFiles = analyzeRelease(release, repository);
            metricsOfFilesByRelease(javaFiles, release);
        });
    }

    //per ogni commit nella lista dei commit 	
    private static List<JavaFile> analyzeRelease(Release release, Repository repository) {
        return release.getCommitList().stream()
            .map(commit -> {
                try {
                    return processCommit(commit, repository);
                } catch (IOException e) {
                    e.printStackTrace();
                }
                return Collections.<JavaFile>emptyList();
            })
            .flatMap(List::stream)
            .collect(Collectors.toList());
    }
    //analizza le differenze tra un commit e il commit padre utilizzando un DiffFormatter
    //restituisce la lista di javaFiles modificati dai commit
    private static List<JavaFile> processCommit(RevCommit commit, Repository repository) throws IOException {
        try (DiffFormatter diff = new DiffFormatter(DisabledOutputStream.INSTANCE)) {
            diff.setRepository(repository);
            diff.setDiffComparator(RawTextComparator.DEFAULT);
            diff.setContext(0);
            diff.setDetectRenames(true);
            String author = commit.getAuthorIdent().getName();
            List<DiffEntry> diffs = getDiffs(commit);
            if (diffs != null) {
                List<JavaFile> javaFiles = new ArrayList<>();
                diffs.forEach(diffEntry -> {
                    String type = diffEntry.getChangeType().toString();
                    DiffInfo diffInfo = new DiffInfo(diffEntry, type, author, javaFiles, diff);
                    processDiffEntry(diffInfo);
                });
                return javaFiles;
            }
        }
        return Collections.<JavaFile>emptyList();
    }



   
    
    
    //Se la modifica è di tipo MODIFY ed ADD assegna il nuovo percorso del file alla variabile filename
    //se è di tipo DELETE assegna il nuovo percorso del file alla variabile filename
    //se è null break
    public static void processDiffEntry(DiffInfo diffInfo) {
        String fileName = null;
        switch (diffInfo.getType()) {
            case "MODIFY":
                fileName = diffInfo.getDiffEntry().getNewPath();
                break;
            case "ADD":
                fileName = diffInfo.getDiffEntry().getNewPath();
                break;
            case DELETE:
                fileName = diffInfo.getDiffEntry().getOldPath();
                break;
            case "RENAME":
                fileName = diffInfo.getDiffEntry().getNewPath();
                break;
            default:
                fileName = null;
                break;
        }
        //calcola churn
        if (fileName != null && fileName.contains(ENDFILE)) {
            churn(diffInfo.getFileList(), fileName, diffInfo.getAuthName(), diffInfo.getDiffEntry(), diffInfo.getDiff());
        }
    }

//da rivedere
    
    //calcolo del churn con DiffInfo e il numero di linee di codice toccate
    public static void churn(List<JavaFile> fileList, String fileName, String authName, DiffEntry diffEntry, DiffFormatter diff) {
        try {
            FileHeader fileHeader = diff.toFileHeader(diffEntry);
            int addedLines = 0;
            int deletedLines = 0;
            for (Edit edit : fileHeader.toEditList()) {
                addedLines += edit.getLengthB();
                deletedLines += edit.getLengthA();
            }
            int churn = calculateChurn(addedLines, deletedLines);
            int locTouched = calculatelocTouched(addedLines, deletedLines);
            DiffInfo diffInfo = new DiffInfo(diffEntry, diffEntry.getChangeType().toString(), authName, fileList, diff);
            diffInfo.setFileName(fileName);
            JavaFile newJavaFile = new JavaFile(diffInfo.getFileName());
            setMetrics(newJavaFile, addedLines, churn, fileList, authName, locTouched);
            fileList.add(newJavaFile);
        } catch (IOException e) {
            logger.log(Level.SEVERE, "Errore nel calcolo delle linee aggiunte ed eliminate", e);
        }
    }



    private static int calculateChurn(int addedLines, int deletedLines) {
        int churn = 0;
        if (addedLines > deletedLines) {
            churn = addedLines - deletedLines;
        } else if (deletedLines > addedLines) {
            churn = -(deletedLines - addedLines);
        }
        return churn;
    }

    
    


    private static int calculatelocTouched(int addedLines, int deletedLines) {
    	int churn = 0;
        if (addedLines > deletedLines) {
            churn = addedLines + deletedLines;
        } else if (deletedLines > addedLines) {
            churn = +(deletedLines + addedLines);
        }
        return churn;
    }

    

    private static void setNr(JavaFile javaFile) {
        javaFile.setNr(1);
    }

    private static void setNAuth(JavaFile javaFile, String authName) {
        javaFile.setNAuth(Collections.singletonList(authName));
    }

    private static void setLocAdded(JavaFile javaFile, int locAdded) {
        javaFile.setlinesOfCodeadded(locAdded);
        javaFile.setlinesOfCodeAddedList(Collections.singletonList(locAdded));
    }

    private static void setChurn(JavaFile javaFile, int churn) {
        javaFile.setChurn(churn);
        javaFile.setChurnList(Collections.singletonList(churn));
    }

    private static void setLocTouched(JavaFile javaFile, int locTouched) {
        javaFile.setLocTouched(locTouched);
        javaFile.setlocTouchedList(Collections.singletonList(locTouched));
    }

    private static void addToFileList(List<JavaFile> fileList, JavaFile javaFile) {
        fileList.add(javaFile);
    }

    public static void setMetrics(JavaFile javaFile, int locAdded, int churn, List<JavaFile> fileList, String authName, int locTouched) {
        setNr(javaFile);
        setNAuth(javaFile, authName);
        setLocAdded(javaFile, locAdded);
        setChurn(javaFile, churn);
        setLocTouched(javaFile, locTouched);
        addToFileList(fileList, javaFile);
        
    }


    //filtra lista JavaFile per selezionare solo quelli che hanno lo stesso nome nella releaseList
    //aggiorna le metriche 
    public static void metricsOfFilesByRelease(List<JavaFile> fileList, Release release) {
        fileList.stream()
                .filter(javaFile -> release.getFile().stream().anyMatch(file -> javaFile.getName().equals(file.getName())))
                .forEach(javaFile -> release.getFile().stream()
                        .filter(file -> javaFile.getName().equals(file.getName()))
                        .findFirst()
                        .ifPresent(file -> updateReleaseFileMetrics(javaFile, file)));
    }


    private static void updateReleaseFileMetrics(JavaFile javaFile, JavaFile file) {
        updateLOCadded(javaFile, file);
        updateChurn(javaFile, file);
        updateLocTouched(javaFile, file);
        updateNAuth(javaFile, file);
        
    }

    private static void updateLOCadded(JavaFile javaFile, JavaFile file) {
        file.setlinesOfCodeadded(file.getlinesOfCodeadded() + javaFile.getlinesOfCodeadded());
        file.getlinesOfCodeAddedList().addAll(javaFile.getlinesOfCodeAddedList());
    }

    private static void updateChurn(JavaFile javaFile, JavaFile file) {
        file.setChurn(file.getChurn() + javaFile.getChurn());
        file.getChurnList().addAll(javaFile.getChurnList());
    }

    private static void updateLocTouched(JavaFile javaFile, JavaFile file) {
        file.setLocTouched(file.getLocTouched() + javaFile.getLocTouched());
        file.getLocTouchedList().addAll(javaFile.getLocTouchedList());
    }

    private static void updateNAuth(JavaFile javaFile, JavaFile file) {
        file.setNr(file.getNr() + javaFile.getNr());
        
        Set<String> nAuthSet = new HashSet<>(file.getNAuth());
        nAuthSet.addAll(javaFile.getNAuth());
        
        file.setNAuth(new ArrayList<>(nAuthSet));
    }



    

    

    //apertura ObjectReader sulla prima entry del treeWalk e lo carica in ObjectLoader. Apre stream
    //e lo legge tramite BufferedReader contanto il numero di righe di codice. 
    public static int size(TreeWalk treewalk, Repository repository) throws IOException {
        try (ObjectReader reader = repository.newObjectReader()) {
            ObjectLoader loader = reader.open(treewalk.getObjectId(0));
            try (InputStream input = loader.openStream()) {
                BufferedReader readerNew = new BufferedReader(new InputStreamReader(input));
                return (int) readerNew.lines().count();
            }}
        }
        
     private static Repository repository;
        


        
     //Ottenimento commits del repository e li aggiunge alla lista dei commits
     public static List<RevCommit> getAllCommits(List<Release> releases, Path repositoryPath) throws GitAPIException, IOException {
            try (Repository repository = new FileRepositoryBuilder().setGitDir(repositoryPath.resolve(".git").toFile()).build()) {
                List<RevCommit> commits = new ArrayList<>();
                try (Git git = new Git(repository)) {
                    Iterable<RevCommit> logEntries = git.log().all().call();
                    for (RevCommit commit : logEntries) {
                        commits.add(commit);
                        updateReleaseWithCommit(commit, releases);
                    }
                }
                return commits;
            }
       }

     // aggiorno commit associati alla release
     private static void updateReleaseWithCommit(RevCommit commit, List<Release> releases) {
            Release release = getReleaseForCommit(commit, releases);
            if (release != null) {
                release.addCommit(commit);
            }
        }

        

     //identificazione release a cui il commit appartiene ovvero con data di rilascio
     //precedente alla data del commit ma successiva alla data di rilascio della release precedente
     
     private static Release getReleaseForCommit(RevCommit commit, List<Release> releaseList) {
    	    LocalDateTime commitDate = commit.getAuthorIdent().getWhen().toInstant().atZone(ZoneId.systemDefault()).toLocalDateTime();
    	    return releaseList.stream()
    	    		.filter(release -> release.getIndex().equals(afterBeforeDate(commitDate, releaseList)))
    	            .findFirst()
    	            .orElse(null);
    	}



     //inizializzazione repo
     private static Git initGitRepository(Path repoPath) throws IOException, IllegalStateException, GitAPIException {
            Git git = Git.open(repoPath.toFile());
            Repository repo = git.getRepository();
            if (!repo.getDirectory().exists()) {
                Git.init().setDirectory(repoPath.toFile()).call();
            }
            return git;
        }
     //ottenimento file per ogni commit associato alla release
     private static void getJavaFilesForRelease(Git git, Release release) throws IOException,NoSuchMethodException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, SecurityException {
    	    List<String> javaFileNames = new ArrayList<>();

    	    for (RevCommit commit : release.getCommitList()) {
    	        ObjectId treeId = commit.getTree();
    	        try (RevWalk revWalk = new RevWalk(git.getRepository())) {
    	            RevTree tree = revWalk.parseTree(treeId);

    	            analyzeTreeWalk(git.getRepository(), tree, release, javaFileNames);
    	        }
    	    }
    	}
     //file java
    	private static void analyzeTreeWalk(Repository repository, RevTree tree, Release release, List<String> javaFileNames) throws IOException, NoSuchMethodException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, SecurityException {
    	    try (TreeWalk treeWalk = new TreeWalk(repository)) {
    	        treeWalk.addTree(tree);
    	        treeWalk.setRecursive(true);

    	        while (treeWalk.next()) {
    	            if (treeWalk.isSubtree() || !treeWalk.getPathString().endsWith(ENDFILE)) {
    	                continue;
    	            }

    	            addJavaFile(treeWalk, release, javaFileNames);
    	        }
    	    }
    	}



     public static void getJavaFiles(Path repoPath, List<Release> releasesList) throws IOException, IllegalStateException, GitAPIException, NoSuchMethodException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, SecurityException {
            Git git = initGitRepository(repoPath);

            for (Release release : releasesList) {
                getJavaFilesForRelease(git, release);
                setFileListIfNeeded(release, releasesList);
            }
        }

     	//controlla se lista releas è vuota, se si prende ultima release e la sua lista di file
	     private static void setFileListIfNeeded(Release release, List<Release> releasesList) {
	            if (!release.getFile().isEmpty()) {
	                return;
	            }
	
	            int previousReleaseIndex = releasesList.size() - 2;
	            if (previousReleaseIndex < 0) {
	                return;
	            }
	
	            Release previousRelease = releasesList.get(previousReleaseIndex);
	            release.setFileList(previousRelease.getFile());
	        }


       


//da rivedere
	     
	     //aggiunge java file e attributi evitando duplicati
     private static void addJavaFile(TreeWalk treeWalk, Release release, List<String> fileNameList) throws IOException, IllegalAccessException, IllegalArgumentException, InvocationTargetException, NoSuchMethodException, SecurityException {
            while (treeWalk.next()) {
                if (treeWalk.isSubtree() || !treeWalk.getPathString().endsWith(ENDFILE)) {
                    continue;
                }
                String filename = treeWalk.getPathString();
                if (!fileNameList.contains(filename)) {
                    JavaFile file = new JavaFile(filename);
                    setDefaultJavaFileAttributes(treeWalk, file);
                    release.getFile().add(file);
                    fileNameList.add(filename);
                }
            }
        }




     

     
     private static void setDefaultJavaFileAttributes(TreeWalk treeWalk, JavaFile file) throws IOException {
    	// Inizializza le proprietà di JavaFile utilizzando un ciclo for-each
    	for (String property : Arrays.asList("Buggyness", "Nr", "NAuth", "linesOfCodeadded",
    			"linesOfCodeAddedList", "Churn", "ChurnList", "LocTouched", "locTouchedList")) {
    	switch (property) {
    		case "Buggyness":
    			file.setBuggyness("false");
    			break;
    		case "Nr":
    			file.setNr(0);
    			break;
    		case "NAuth":
    			file.setNAuth(new ArrayList<>());
    			break;
    		case "linesOfCodeadded":
    			file.setlinesOfCodeadded(0);
    			break;
    		case "linesOfCodeAddedList":
    			file.setlinesOfCodeAddedList(new ArrayList<>());
    			break;
    		case "Churn":
    			file.setChurn(0);
    		break;
    		case "ChurnList":
    			file.setChurnList(new ArrayList<>());
    			break;
    		case "LocTouched":
    			file.setLocTouched(0);
    			break;
    		case "locTouchedList":
    			file.setlocTouchedList(new ArrayList<>());
    			break;
    		default:
    			break;
    		}
    	}
    	// Calcola la dimensione del file in linee di codice
    	int loc = calculateLinesOfCode(treeWalk);
    		file.setlinesOfCode(loc);
    	}



     private static int calculateLinesOfCode(TreeWalk treeWalk) throws IOException {
        	try (InputStream stream = treeWalk.getObjectReader().open(treeWalk.getObjectId(0)).openStream()) {
        	    return (int) new BufferedReader(new InputStreamReader(stream)).lines().count();
        	}
        }


		

     public static void isBuggy(List<Release> releases, List<Ticket> tickets) {
		    Logger logger = Logger.getLogger("MyLogger");
		    tickets.forEach(ticket -> {
	            List<Integer> av = ticket.getAffectedVersion();

		        try {
		            verify(ticket, releases,av);
		        } catch (IOException e) {
		            logger.log(Level.SEVERE, (Supplier<String>) () -> "Error occurred while verifying ticket " + ticket.getTicketID());
		        }
		    });
		}

     	//per ogni commit nella lista -> getDiffs per ottenere differenze tra commit figlio e padre
        private static void verify(Ticket ticket, List<Release> releaseList,List<Integer> av) throws IOException {
            
            ticket.getCommitList().stream()
                .map(commit -> {
                    try {
                        return getDiffs(commit);
                    } catch (IOException e) {
                        
                        e.printStackTrace();
                    }
                    return null;
                })
                .filter(Objects::nonNull)

                .forEach(diffs -> diff(diffs, releaseList,av));
        }



        private static DiffFormatter initializeDiffFormatter() {
            DiffFormatter diff = new DiffFormatter(DisabledOutputStream.INSTANCE);
            diff.setRepository(repository);
            diff.setContext(0);
            diff.setDetectRenames(true);
            return diff;
        }
        private static List<DiffEntry> getDiffsBetweenCommits(RevCommit parent, RevCommit commit, DiffFormatter diff) throws IOException {
            return diff.scan(parent.getTree(), commit.getTree());
        }
        private static List<DiffEntry> getDiffsWithEmptyTree(RevCommit commit, DiffFormatter diff) throws IOException {
            try (RevWalk rw = new RevWalk(repository)) {
    			return diff.scan(new EmptyTreeIterator(), new CanonicalTreeParser(null, rw.getObjectReader(), commit.getTree()));
    		}
        }
        public static List<DiffEntry> getDiffs(RevCommit commit) throws IOException {
            DiffFormatter diff = initializeDiffFormatter();
            List<DiffEntry> diffs;
            if (commit.getParentCount() != 0) {
                RevCommit parent = (RevCommit) commit.getParent(0).getId();
                diffs = getDiffsBetweenCommits(parent, commit, diff);
            } else {
                diffs = getDiffsWithEmptyTree(commit, diff);
            }
            return diffs;
        }


        //cerca file java modificati o cancellati impostando la buggyness per file in versioni av
        public static void diff(List<DiffEntry> diffs, List<Release> releasesList,List<Integer> av) {
        	  diffs.stream()
        	       .filter(diff -> isBuggyDiffEntry(diff))
        	       .map(diff -> getFilePathFromDiffEntry(diff))
        	       .forEach(file -> setBuggyness(file, releasesList,av));
        	}

        
        private static boolean isBuggyDiffEntry(DiffEntry diff) {
        	  ChangeType changeType = diff.getChangeType();
        	  String path = diff.getNewPath();
        	  return (changeType == ChangeType.MODIFY || changeType == ChangeType.DELETE) && path.endsWith(ENDFILE);
        	}


        private static String getFilePathFromDiffEntry(DiffEntry diff) {
            if (diff.getChangeType() == DiffEntry.ChangeType.DELETE || diff.getChangeType() == DiffEntry.ChangeType.RENAME) {
                return diff.getOldPath();
            } else {
                return diff.getNewPath();
            }
        }


        public static void setBuggyness(String file, List<Release> releasesList,List<Integer> av) {
            releasesList.forEach(release -> setBuggynessForRelease(file, release, av));
        }


        private static void setBuggynessForRelease(String file, Release release, List<Integer> av) {
            release.getFile().stream()
                .filter(javaFile -> javaFile.getName().equals(file))
                .filter(javaFile -> av.contains(release.getIndex()))
                .findFirst()
                .ifPresent(javaFile -> javaFile.setBuggyness(av.contains(release.getIndex()) ? "true" : "false"));
        }



      
        public static void setBuilder(String repo) throws IOException {
            FileRepositoryBuilder repositoryBuilder = new FileRepositoryBuilder();
            repository = repositoryBuilder.setGitDir(new File(repo)).readEnvironment() // scan environment GIT_* variables
                    .findGitDir() // scan up the file system tree
                    .setMustExist(true).build();
        
    }
       
        public static Integer afterBeforeDate(LocalDateTime date, List<Release> releases) {
            Release matchingRelease = releases.stream()
                    .filter(release -> date.isBefore(release.getDate()) || date.isEqual(release.getDate()))
                    .findFirst()
                    .orElseGet(() -> releases.get(releases.size() - 1));

            return matchingRelease.getIndex();
        }


     //----proportion----
        public static void findProportion(List<Ticket> ticketList) {
            List<Ticket> injectedVersion = new ArrayList<>();
            
            findInjectedVersion(ticketList, injectedVersion);

            int total = ticketList.size();
            movingWindowsCount = total*2/100;

            List<Ticket> newProportionTicket = new ArrayList<>();
            processTicketList(ticketList, injectedVersion, newProportionTicket);
        }
        //OV = FV e IV = 0 -> IV = FV 
        private static void findInjectedVersion(List<Ticket> ticketList, List<Ticket> injectedVersion) {
            ticketList.stream()
                .filter(ticket -> ticket.getOpenVersion().equals(ticket.getFixedVersion()) && ticket.getInjectedVersion() == 0)
                .forEach(ticket -> {
                    ticket.setInjectedVersion(ticket.getFixedVersion());
                    injectedVersion.add(ticket);
                
             
                
                });
    }
        
       
        private static void processTicketList(List<Ticket> ticketList, List<Ticket> injectedVersion, List<Ticket> newProportionTicket) {
            ticketList.stream()
                     .filter(ticket -> !injectedVersion.contains(ticket))
                     .forEach(ticket -> {
                         if (ticket.getInjectedVersion() != 0) {
                             movingWindows(newProportionTicket, ticket);
                         } else {
                             injectedProportion(newProportionTicket, ticket);
                         }
                         if(ticket.getOpenVersion() == 1) {
                        	 ticket.setInjectedVersion(1);
                         }
                     });
        }

        //rimuovi quelli maggiori di 2%
        public static void movingWindows(List<Ticket> movingWindow, Ticket ticket) {
            
            
            if (movingWindow.size() < movingWindowsCount ) {
            	movingWindow.add(ticket);
			}
			else if(movingWindow.size() >=  movingWindowsCount) {
				movingWindow.remove(0);
				movingWindow.add(ticket);
			}
        }

        //prendo il min tra IV e OV
        public static void injectedProportion(List<Ticket> newProportionTicket, Ticket ticket) {
        	
            float p = calculateP(newProportionTicket);
            float pNew = p/movingWindowsCount;
            int predictedIv = 0;
            if(newProportionTicket.size() < movingWindowsCount) {
            	
            	predictedIv = calculatePredictedIv(ticket, medianP(ticketListAvro, ticketListAccumulo, ticketListStorm, ticketListTajo, ticketListSyncope));

            }else if(newProportionTicket.size() == movingWindowsCount) {
                predictedIv = calculatePredictedIv(ticket, pNew);



            }
            
            if(predictedIv <= 1) {
            	ticket.setInjectedVersion(1);
            }else if(predictedIv > 1) {
            ticket.setInjectedVersion(Math.min(predictedIv, ticket.getOpenVersion()));}
        }

        private static float calculateP(List<Ticket> newProportionTicket) {

        	return newProportionTicket.stream()
        	.map(RetrieveMetrics::obtainingP)
        	.reduce(0f, Float::sum);
        	}




        
        //calcolo IV 
        private static int calculatePredictedIv(Ticket ticket, float pNew) {
            int fv = ticket.getFixedVersion();
            int ov = ticket.getOpenVersion();
            float predictedIV = (fv - (fv - ov) * pNew);
            
            
            return  (int) predictedIV;
        }


        /**
         * Calcola la proporzione P per un Ticket.
         * @param ticket il Ticket per cui calcolare la proporzione
         * @return la proporzione P calcolata
         */
        private static float obtainingP(Ticket ticket) {
            final float fv = ticket.getFixedVersion();
            final float ov = ticket.getOpenVersion();
            final float iv = ticket.getInjectedVersion();
            float p = 0;

            if(fv!=ov ) { 
	
            p = (fv - iv) / (fv - ov);
            }

            return p;
			
        }
        /*
         * la scelta del'2% dipende dal un trade off tra la capacità di reagire ai cambiamenti: una finestra
         * molto piccola consente di considerare solo i difetti più recenti questo può essere vantaggioso quando si vuole
         * essere sensibili ai cambiamenti nel comportamento dei difetti nel tempo e la resilienza agli outlier, una
         * finestra mobile più grande dei difetti fissati, include un numero maggiore di difetti nel calcolo di P
         * Questo può essere utile per mantenere l'impatto degli outlier o dei difetti anomali che potrebbero influenzare
         * negativamente la stima complessiva di P
         */
        
        
        /*
         * coldstart()
         */
        
        
        private static float obtainingPOtherProject(List<Ticket> tickets) {
            float sumP = 0;
            int count = 0;
            
            for (Ticket ticket : tickets) {
                final float fv = ticket.getFixedVersion();
                final float ov = ticket.getOpenVersion();
                final float iv = ticket.getInjectedVersion();
                
                if (iv != 0 && fv != ov) {
                    float p = (fv - iv) / (fv - ov);
                    sumP += p;
                    count++;
                }
            }
            
            if (count > 0) {
                
				return sumP / count;
            } else {
                return 0;
            }
        }
        
        private static float medianP(List<Ticket> tickets, List<Ticket> tickets2, List<Ticket> tickets3, List<Ticket> tickets4, List<Ticket> tickets5) {
            float[] values = {
                obtainingPOtherProject(tickets),
                obtainingPOtherProject(tickets3),
                obtainingPOtherProject(tickets2),
                obtainingPOtherProject(tickets4),
                obtainingPOtherProject(tickets5)
            };

            Arrays.sort(values);

            int length = values.length;
            int middle = length / 2;

            float median;
            if (length % 2 == 0) {
                // Se la lunghezza è pari, prendi la media dei due valori centrali
                median = (values[middle - 1] + values[middle]) / 2;
            } else {
                // Se la lunghezza è dispari, prendi il valore centrale
                median = values[middle];
            }


            return median;
        }

        
        private static List<String> projects = Arrays.asList(
                AVRO,
                STORM,
                ACCUMULO,
                TAJO,
                SYNCOPE
               
        );
    	private static final String ERROR = "Errore nella crezione del dataset";

        public static void writeProjectsToFile(String fileName) {
        	
            try (FileWriter writer = new FileWriter(fileName)) {
                writer.write("Project,Proportion" + System.lineSeparator());

                for (String project : projects) {
                    List<Ticket> ticketList = getTicketListForProject(project);
                    float proportionValue = obtainingPOtherProject(ticketList);
                    String line = project + "," + proportionValue;
                    writer.write(line + System.lineSeparator());
                }
                
                // Calcolo e scrittura della mediana
                List<Ticket> tickets = getTicketListForProject(projects.get(0));
                List<Ticket> tickets2 = getTicketListForProject(projects.get(1));
                List<Ticket> tickets3 = getTicketListForProject(projects.get(2));
                List<Ticket> tickets4 = getTicketListForProject(projects.get(3));
                List<Ticket> tickets5 = getTicketListForProject(projects.get(4));
                float medianValue = medianP(tickets, tickets2, tickets3, tickets4, tickets5);
                writer.write("Median P ," + medianValue + System.lineSeparator());

            } catch (IOException e) {
  	  		  	logger.info(ERROR);
            }
        }


        private static List<Ticket> getTicketListForProject(String project) {
            
            switch (project) {
                case AVRO:
                    return ticketListAvro;
                case TAJO:
                    return ticketListTajo;
                case STORM:
                    return ticketListStorm;
                case ACCUMULO:
                    return ticketListAccumulo;
                case SYNCOPE:
                    return ticketListSyncope;
                
                default:
                    return Collections.emptyList();
            }
        }
        


        
        









}
