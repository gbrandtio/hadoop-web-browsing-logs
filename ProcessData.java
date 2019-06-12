import java.io.BufferedReader;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.Set;
import java.util.StringTokenizer;

import org.apache.hadoop.conf.Configuration;
import org.apache.hadoop.filecache.DistributedCache;
import org.apache.hadoop.fs.ContentSummary;
import org.apache.hadoop.fs.FileStatus;
import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.LocatedFileStatus;
import org.apache.hadoop.fs.Path;
import org.apache.hadoop.fs.RemoteIterator;
import org.apache.hadoop.io.IntWritable;
import org.apache.hadoop.io.NullWritable;
import org.apache.hadoop.io.Text;
import org.apache.hadoop.mapred.JobConf;
import org.apache.hadoop.mapred.lib.MultipleOutputs;
import org.apache.hadoop.mapreduce.Job;
import org.apache.hadoop.mapreduce.MapContext;
import org.apache.hadoop.mapreduce.Mapper;
import org.apache.hadoop.mapreduce.Reducer;
import org.apache.hadoop.mapreduce.lib.input.FileInputFormat;
import org.apache.hadoop.mapreduce.lib.input.FileSplit;
import org.apache.hadoop.mapreduce.lib.output.FileOutputFormat;
import org.apache.hadoop.mapreduce.lib.output.TextOutputFormat;

public class ProcessData {
	
	public static int team=0;
	
	//Stemming
	static class Stemmer
	{  private char[] b;
	   private int i,    
	               i_end, 
	               j, k;
	   private static final int INC = 50;
	                     
	   public Stemmer()
	   {  b = new char[INC];
	      i = 0;
	      i_end = 0;
	   }

	   /**
	    * Add a character to the word being stemmed.  When you are finished
	    * adding characters, you can call stem(void) to stem the word.
	    */

	   public void add(char ch)
	   {  if (i == b.length)
	      {  char[] new_b = new char[i+INC];
	         for (int c = 0; c < i; c++) new_b[c] = b[c];
	         b = new_b;
	      }
	      b[i++] = ch;
	   }


	   /** Adds wLen characters to the word being stemmed contained in a portion
	    * of a char[] array. This is like repeated calls of add(char ch), but
	    * faster.
	    */

	   public void add(char[] w, int wLen)
	   {  if (i+wLen >= b.length)
	      {  char[] new_b = new char[i+wLen+INC];
	         for (int c = 0; c < i; c++) new_b[c] = b[c];
	         b = new_b;
	      }
	      for (int c = 0; c < wLen; c++) b[i++] = w[c];
	   }

	   /**
	    * After a word has been stemmed, it can be retrieved by toString(),
	    * or a reference to the internal buffer can be retrieved by getResultBuffer
	    * and getResultLength (which is generally more efficient.)
	    */
	   public String toString() { return new String(b,0,i_end); }

	   /**
	    * Returns the length of the word resulting from the stemming process.
	    */
	   public int getResultLength() { return i_end; }

	   /**
	    * Returns a reference to a character buffer containing the results of
	    * the stemming process.  You also need to consult getResultLength()
	    * to determine the length of the result.
	    */
	   public char[] getResultBuffer() { return b; }

	   /* cons(i) is true <=> b[i] is a consonant. */

	   private final boolean cons(int i)
	   {  switch (b[i])
	      {  case 'a': case 'e': case 'i': case 'o': case 'u': return false;
	         case 'y': return (i==0) ? true : !cons(i-1);
	         default: return true;
	      }
	   }

	   /* m() measures the number of consonant sequences between 0 and j. if c is
	      a consonant sequence and v a vowel sequence, and <..> indicates arbitrary
	      presence,

	         <c><v>       gives 0
	         <c>vc<v>     gives 1
	         <c>vcvc<v>   gives 2
	         <c>vcvcvc<v> gives 3
	         ....
	   */

	   private final int m()
	   {  int n = 0;
	      int i = 0;
	      while(true)
	      {  if (i > j) return n;
	         if (! cons(i)) break; i++;
	      }
	      i++;
	      while(true)
	      {  while(true)
	         {  if (i > j) return n;
	               if (cons(i)) break;
	               i++;
	         }
	         i++;
	         n++;
	         while(true)
	         {  if (i > j) return n;
	            if (! cons(i)) break;
	            i++;
	         }
	         i++;
	       }
	   }

	   /* vowelinstem() is true <=> 0,...j contains a vowel */

	   private final boolean vowelinstem()
	   {  int i; for (i = 0; i <= j; i++) if (! cons(i)) return true;
	      return false;
	   }

	   /* doublec(j) is true <=> j,(j-1) contain a double consonant. */

	   private final boolean doublec(int j)
	   {  if (j < 1) return false;
	      if (b[j] != b[j-1]) return false;
	      return cons(j);
	   }

	   /* cvc(i) is true <=> i-2,i-1,i has the form consonant - vowel - consonant
	      and also if the second c is not w,x or y. this is used when trying to
	      restore an e at the end of a short word. e.g.

	         cav(e), lov(e), hop(e), crim(e), but
	         snow, box, tray.

	   */

	   private final boolean cvc(int i)
	   {  if (i < 2 || !cons(i) || cons(i-1) || !cons(i-2)) return false;
	      {  int ch = b[i];
	         if (ch == 'w' || ch == 'x' || ch == 'y') return false;
	      }
	      return true;
	   }

	   private final boolean ends(String s)
	   {  int l = s.length();
	      int o = k-l+1;
	      if (o < 0) return false;
	      for (int i = 0; i < l; i++) if (b[o+i] != s.charAt(i)) return false;
	      j = k-l;
	      return true;
	   }

	   /* setto(s) sets (j+1),...k to the characters in the string s, readjusting
	      k. */

	   private final void setto(String s)
	   {  int l = s.length();
	      int o = j+1;
	      for (int i = 0; i < l; i++) b[o+i] = s.charAt(i);
	      k = j+l;
	   }

	   /* r(s) is used further down. */

	   private final void r(String s) { if (m() > 0) setto(s); }

	   /* step1() gets rid of plurals and -ed or -ing. e.g.

	          caresses  ->  caress
	          ponies    ->  poni
	          ties      ->  ti
	          caress    ->  caress
	          cats      ->  cat

	          feed      ->  feed
	          agreed    ->  agree
	          disabled  ->  disable

	          matting   ->  mat
	          mating    ->  mate
	          meeting   ->  meet
	          milling   ->  mill
	          messing   ->  mess

	          meetings  ->  meet

	   */

	   private final void step1()
	   {  if (b[k] == 's')
	      {  if (ends("sses")) k -= 2; else
	         if (ends("ies")) setto("i"); else
	         if (b[k-1] != 's') k--;
	      }
	      if (ends("eed")) { if (m() > 0) k--; } else
	      if ((ends("ed") || ends("ing")) && vowelinstem())
	      {  k = j;
	         if (ends("at")) setto("ate"); else
	         if (ends("bl")) setto("ble"); else
	         if (ends("iz")) setto("ize"); else
	         if (doublec(k))
	         {  k--;
	            {  int ch = b[k];
	               if (ch == 'l' || ch == 's' || ch == 'z') k++;
	            }
	         }
	         else if (m() == 1 && cvc(k)) setto("e");
	     }
	   }

	   /* step2() turns terminal y to i when there is another vowel in the stem. */

	   private final void step2() { if (ends("y") && vowelinstem()) b[k] = 'i'; }

	   /* step3() maps double suffices to single ones. so -ization ( = -ize plus
	      -ation) maps to -ize etc. note that the string before the suffix must give
	      m() > 0. */

	   private final void step3() { if (k == 0) return; /* For Bug 1 */ switch (b[k-1])
	   {
	       case 'a': if (ends("ational")) { r("ate"); break; }
	                 if (ends("tional")) { r("tion"); break; }
	                 break;
	       case 'c': if (ends("enci")) { r("ence"); break; }
	                 if (ends("anci")) { r("ance"); break; }
	                 break;
	       case 'e': if (ends("izer")) { r("ize"); break; }
	                 break;
	       case 'l': if (ends("bli")) { r("ble"); break; }
	                 if (ends("alli")) { r("al"); break; }
	                 if (ends("entli")) { r("ent"); break; }
	                 if (ends("eli")) { r("e"); break; }
	                 if (ends("ousli")) { r("ous"); break; }
	                 break;
	       case 'o': if (ends("ization")) { r("ize"); break; }
	                 if (ends("ation")) { r("ate"); break; }
	                 if (ends("ator")) { r("ate"); break; }
	                 break;
	       case 's': if (ends("alism")) { r("al"); break; }
	                 if (ends("iveness")) { r("ive"); break; }
	                 if (ends("fulness")) { r("ful"); break; }
	                 if (ends("ousness")) { r("ous"); break; }
	                 break;
	       case 't': if (ends("aliti")) { r("al"); break; }
	                 if (ends("iviti")) { r("ive"); break; }
	                 if (ends("biliti")) { r("ble"); break; }
	                 break;
	       case 'g': if (ends("logi")) { r("log"); break; }
	   } }

	   /* step4() deals with -ic-, -full, -ness etc. similar strategy to step3. */

	   private final void step4() { switch (b[k])
	   {
	       case 'e': if (ends("icate")) { r("ic"); break; }
	                 if (ends("ative")) { r(""); break; }
	                 if (ends("alize")) { r("al"); break; }
	                 break;
	       case 'i': if (ends("iciti")) { r("ic"); break; }
	                 break;
	       case 'l': if (ends("ical")) { r("ic"); break; }
	                 if (ends("ful")) { r(""); break; }
	                 break;
	       case 's': if (ends("ness")) { r(""); break; }
	                 break;
	   } }

	   /* step5() takes off -ant, -ence etc., in context <c>vcvc<v>. */

	   private final void step5()
	   {   if (k == 0) return; /* for Bug 1 */ switch (b[k-1])
	       {  case 'a': if (ends("al")) break; return;
	          case 'c': if (ends("ance")) break;
	                    if (ends("ence")) break; return;
	          case 'e': if (ends("er")) break; return;
	          case 'i': if (ends("ic")) break; return;
	          case 'l': if (ends("able")) break;
	                    if (ends("ible")) break; return;
	          case 'n': if (ends("ant")) break;
	                    if (ends("ement")) break;
	                    if (ends("ment")) break;
	                    /* element etc. not stripped before the m */
	                    if (ends("ent")) break; return;
	          case 'o': if (ends("ion") && j >= 0 && (b[j] == 's' || b[j] == 't')) break;
	                                    /* j >= 0 fixes Bug 2 */
	                    if (ends("ou")) break; return;
	                    /* takes care of -ous */
	          case 's': if (ends("ism")) break; return;
	          case 't': if (ends("ate")) break;
	                    if (ends("iti")) break; return;
	          case 'u': if (ends("ous")) break; return;
	          case 'v': if (ends("ive")) break; return;
	          case 'z': if (ends("ize")) break; return;
	          default: return;
	       }
	       if (m() > 1) k = j;
	   }

	   /* step6() removes a final -e if m() > 1. */

	   private final void step6()
	   {  j = k;
	      if (b[k] == 'e')
	      {  int a = m();
	         if (a > 1 || a == 1 && !cvc(k-1)) k--;
	      }
	      if (b[k] == 'l' && doublec(k) && m() > 1) k--;
	   }

	   /** Stem the word placed into the Stemmer buffer through calls to add().
	    * Returns true if the stemming process resulted in a word different
	    * from the input.  You can retrieve the result with
	    * getResultLength()/getResultBuffer() or toString().
	    */
	   public void stem()
	   {  k = i - 1;
	      if (k > 1) { step1(); step2(); step3(); step4(); step5(); step6(); }
	      i_end = k+1; i = 0;
	   }

	}
	
 //Inverted Index Job	
  public static class TokenizerMapper
       extends Mapper<Object, Text, Text, IntWritable>{

    private Text word = new Text();;
    private Set<String> stopWords = new HashSet<>();
    private Scanner sc;
    
    @SuppressWarnings("deprecation")
	protected void setup(Context context) throws IOException, InterruptedException {
        Configuration conf = context.getConfiguration();
        try{
        	Path[] stopWordsFiles = DistributedCache.getLocalCacheFiles(context.getConfiguration());
        	            if(stopWordsFiles != null && stopWordsFiles.length > 0) {
        	                for(Path stopWordFile : stopWordsFiles) {
        	                    readFile(stopWordFile);
        	
        	                }
        	            }
        }catch(FileNotFoundException e){
        	System.out.println("Folder stopwords is not present in hdfs.");
        }
    }
    
    public void map(Object key, Text value, Context context
                    ) throws IOException, InterruptedException {

      StringTokenizer itr = new StringTokenizer(value.toString());

      String filenameStr = ((FileSplit) context.getInputSplit()).getPath().getName().toString();
      char[] file = filenameStr.toCharArray();

      String id=filenameStr;
      int end=0;
      for (int i=0;i<file.length;i++){
    	  if (file[i]=='.'){
    		  end=i;
    	  }
      }
      
      while (itr.hasMoreTokens()) {
    	  String s =itr.nextToken();
    	  s = s.replaceAll("\\p{P}", "");
    	  String str = s;
          Stemmer stemmer = new Stemmer();
          if (!stopWords.contains(str)){
        	  char[] wor = str.toCharArray();
        	  stemmer.add(wor,wor.length);
        	  stemmer.stem();
        	  str = stemmer.toString();
        	  word.set(str);
          }
 
        if (!stopWords.contains(s)){
           context.write(word, new IntWritable(Integer.parseInt(id.substring(0,end))));
        }
        
      }
    }
    
    private void readFile(Path filePath) {
        try{
        	sc = new Scanner(new FileReader(filePath.toString()));
           //BufferedReader bufferedReader = new BufferedReader(new FileReader(filePath.toString()));
            String stopWord = null;
            while(sc.hasNext()) {
            	stopWord=sc.next();
                stopWords.add(stopWord);
            }
        } catch(IOException ex) {
            System.err.println("Exception while reading stop words file: " + ex.getMessage());
        }
    }
}


  public static class IntSumReducer
       extends Reducer<Text,IntWritable,Text,Text> {
    private Text result = new Text();

    private static ArrayList<String> list ;//= new ArrayList<>();
    private static String count;
    private static int counter;

    protected void setup(Context context) throws IOException, InterruptedException {
        Configuration conf = context.getConfiguration();
         count = conf.get("count");
         counter = Integer.valueOf(count);
         list = new ArrayList<String>(Arrays.asList(conf.getStrings("filenames")));
    }
    
    public void reduce(Text key, Iterable<IntWritable> values,
                       Context context
                       ) throws IOException, InterruptedException {
    	String res="";
    	String[] vals = new String[counter];
    	for (int i=0;i<counter;i++){
    		vals[i]="0";
    	}
    	res+="[";
    	for (IntWritable val:values){ 
    		vals[val.get()-1]="1";
    	}
    	for (int i=0;i<counter;i++){
    		res+=vals[i]+",";
    	}
    	res+="]";
       	result.set(res);
      context.write(key, result);
    }
    
    
  }
  
  //Kmeans Job
  	public static class TokenizerMapper2
  		extends Mapper<Object, Text, Text, Text>{
  		private Text v = new Text();
  		
  		private Text word = new Text();
  		
  		private ArrayList<String> centers = new ArrayList<>();
  		private int no=0;
  		
  		@SuppressWarnings("deprecation")
  		protected void setup(Context context) throws IOException, InterruptedException {
  	        Configuration conf = context.getConfiguration();
  	        String n = conf.get("count");
  	        no=Integer.valueOf(n);
  	        try{
  	        	Path[] centersFile = DistributedCache.getLocalCacheFiles(context.getConfiguration());
  	        	            if(centersFile != null && centersFile.length > 0) {
  	        	                for(Path file : centersFile) {
  	        	                    readFile(file);
  	        	
  	        	                }
  	        	            }
  	        }catch(FileNotFoundException e){
  	        	System.out.println("Folder centers.txt is not present in hdfs.");
  	        }
  	    }
  		
  		
	  	public void map(Object key, Text value, Context context
               ) throws IOException, InterruptedException {
	  	
	  		//take the vector for each word from the output txt file of Inverted Index Job
	  		String itr = new String(value.toString());
	  		String vector="";
	  		char[] cs = itr.toCharArray();
	  		int pos=0;

	  		for (int i=0;i<itr.length();i++){
		    	if (cs[i]=='['){
		    		pos=i;
		    	}
		    }

	  		//calculating the minimum distance
	  		//the distance is calculated for vectors with 3 dimensions
	  		double min=Double.MAX_VALUE;
	  		int pos1=0;
	  		Vector3D vector1 = new Vector3D(itr);
	  		for (int i=0;i<centers.size();i++){
	  			Vector3D currCenter = new Vector3D(centers.get(i));
	  			double dist = vector1.distanceFromVector(currCenter);
	  			if (dist<min)
	  				pos1=i;
	  				min=dist;
	  		}
	  		
	  		word.set(centers.get(pos1));
	  		v.set(itr.substring(0,pos-1));
	  		context.write(word, v);
	  	}
	  	
	  	//class which finds the distance between two 3dimenion-vectors
	  	public class Vector3D {
	        private int x;
	        private int y;
	        private int z;
	        
	        public Vector3D(String string){
	            
	            int indexStart = string.indexOf("[");
	            if(!string.contains("[")){
	                indexStart = 0;
	            }
	            int indexEnd   = string.indexOf("]");
	            String substring = string.substring(indexStart, indexEnd);
	            char[] chars = substring.toCharArray();
	            x = Character.getNumericValue(chars[1]);
	            y = Character.getNumericValue(chars[3]);
	            z = Character.getNumericValue(chars[5]);
	        }
	        public Vector3D(int x, int y, int z){
	            this.x = x;
	            this.y = y;
	            this.z = z;
	        }
	        public int getX(){return this.x;}
	        public int getY(){return this.y;}
	        public int getZ(){return this.z;}
	        
	        public double distanceFromVector(Vector3D another3DVector){
	            int x2 = another3DVector.getX();
	            int y2 = another3DVector.getY();
	            int z2 = another3DVector.getZ();
	            int product = x*x2+y*y2+z*z2;
	            double vector1Length = Math.sqrt(x^2+y^2+z^2);
	            double vector2Length = Math.sqrt(x2^2+y2^2+z2^2);
	            double dist = 1 - (product/(vector1Length*vector2Length));
	            return dist;
	        }
	  }
	  	
	  	private void readFile(Path filePath) {
	  		
		        try{
		            BufferedReader bufferedReader = new BufferedReader(new FileReader(filePath.toString()));
		            String center = null;
		            while((center = bufferedReader.readLine()) != null) {
		                centers.add(center);
		            }
		        } catch(IOException ex) {
		            System.err.println("Exception while reading centers.txt file: " + ex.getMessage());
		        }
		    }
}
  
  
  	public static class IntSumReducer2
  		extends Reducer<Text,Text,Text,Text> {
  			private Text result=new Text();
  			private int cluster=0;
  			
  			@SuppressWarnings("deprecation")
  	  		protected void setup(Context context) throws IOException, InterruptedException {
  	  	        Configuration conf = context.getConfiguration();
  	  	        String reducerID=conf.get("reducerID");
  	  	        cluster = Integer.valueOf(reducerID);
  	  	    }
  			

  			public void reduce(Text key, Iterable<Text> values,
                  Context context
                  ) throws IOException, InterruptedException {
  				
  				String res="";
  				cluster++;
  				for (Text val :values){
  					res+=val.toString() + " ";
  				}
  				result.set(res);
  				context.write(new Text(String.valueOf(cluster)), result);
  			}		
  	}
  


  @SuppressWarnings("deprecation")
public static void main(String[] args) throws Exception {
    Configuration conf = new Configuration();
    
    FileSystem fs = FileSystem.get(conf);
    Path pt = new Path(args[0]);
    ContentSummary cs = fs.getContentSummary(pt);
    long fileCount = cs.getFileCount();
    conf.set("count", String.valueOf(fileCount));
    int id=-1;
    conf.set("id", String.valueOf(id));
    int team=0;
    conf.set("reducerID", String.valueOf(team));
    System.out.println("counter:" + fileCount);
    String[] names = new String[1000];
    int o=0;
    FileStatus[] fileStatus = fs.listStatus(new Path(args[0]));
    for (FileStatus fileStat : fileStatus) {
  	  String fileName = fileStat.getPath().getName().toString(); ;
  	  names[o]=fileName;
  	  System.out.println(o + names[o]);
          		  o++;
    }

    conf.setStrings("filenames", names);


    Job job = Job.getInstance(conf, "Inverted Index Job");
    job.setJarByClass(ProcessData.class);
    job.setMapperClass(TokenizerMapper.class);
    //job.setCombinerClass(IntSumReducer.class);
    job.setReducerClass(IntSumReducer.class);
    DistributedCache.addCacheFile(new Path(args[2]).toUri(), job.getConfiguration());
    job.setOutputKeyClass(Text.class);
    job.setOutputValueClass(IntWritable.class);
    FileInputFormat.addInputPath(job, new Path(args[0]));
    FileOutputFormat.setOutputPath(job, new Path(args[1]));
    Path temp = new Path(args[1]);
    Text name1 = new Text("invind");
    //MultipleOutputs.addNamedOutput(conf, name1, TextOutputFormat.class, NullWritable.class, Text.class);
    
    job.waitForCompletion(true);
    //System.exit(job.waitForCompletion(true) ? 0 : 1);
    
    Job job2 = new Job(conf,"KMeans Job");
    job2.setJarByClass(ProcessData.class);
    job2.setMapperClass(TokenizerMapper2.class);
    job2.setCombinerClass(IntSumReducer2.class);
    job2.setReducerClass(IntSumReducer2.class);
    DistributedCache.addCacheFile(new Path(args[3]).toUri(), job2.getConfiguration());
    job2.setOutputKeyClass(Text.class);
    job2.setOutputValueClass(Text.class);
    FileInputFormat.addInputPath(job2, new Path(args[1]));
    FileOutputFormat.setOutputPath(job2, new Path(args[1]+"/kmeansOutput6"));
    
    System.exit(job2.waitForCompletion(true) ? 0 : 1);
  }

}
