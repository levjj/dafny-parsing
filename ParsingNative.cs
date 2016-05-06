using System.IO;

namespace @_0_Parsing_Compile {
  public partial class @FileSystem {
    public static void ReadFile(char[] fname, out char[] result) {
      string sname = new string(fname);
      result = File.ReadAllText(sname).ToCharArray();
    }
  }
}
