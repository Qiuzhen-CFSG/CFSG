module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar14

/-!
# Exact product checks on rows 896 through 959

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block14

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t896 tb896 ts896 _ _ ts896_sum ts896_parity
  apply product_cons_b t897 tb897 ts897 _ _ ts897_sum ts897_parity
  apply product_cons_b t898 tb898 ts898 _ _ ts898_sum ts898_parity
  apply product_cons_b t899 tb899 ts899 _ _ ts899_sum ts899_parity
  apply product_cons_b t900 tb900 ts900 _ _ ts900_sum ts900_parity
  apply product_cons_b t901 tb901 ts901 _ _ ts901_sum ts901_parity
  apply product_cons_b t902 tb902 ts902 _ _ ts902_sum ts902_parity
  apply product_cons_b t903 tb903 ts903 _ _ ts903_sum ts903_parity
  apply product_cons_b t904 tb904 ts904 _ _ ts904_sum ts904_parity
  apply product_cons_b t905 tb905 ts905 _ _ ts905_sum ts905_parity
  apply product_cons_b t906 tb906 ts906 _ _ ts906_sum ts906_parity
  apply product_cons_b t907 tb907 ts907 _ _ ts907_sum ts907_parity
  apply product_cons_b t908 tb908 ts908 _ _ ts908_sum ts908_parity
  apply product_cons_b t909 tb909 ts909 _ _ ts909_sum ts909_parity
  apply product_cons_b t910 tb910 ts910 _ _ ts910_sum ts910_parity
  apply product_cons_b t911 tb911 ts911 _ _ ts911_sum ts911_parity
  apply product_cons_b t912 tb912 ts912 _ _ ts912_sum ts912_parity
  apply product_cons_b t913 tb913 ts913 _ _ ts913_sum ts913_parity
  apply product_cons_b t914 tb914 ts914 _ _ ts914_sum ts914_parity
  apply product_cons_b t915 tb915 ts915 _ _ ts915_sum ts915_parity
  apply product_cons_b t916 tb916 ts916 _ _ ts916_sum ts916_parity
  apply product_cons_b t917 tb917 ts917 _ _ ts917_sum ts917_parity
  apply product_cons_b t918 tb918 ts918 _ _ ts918_sum ts918_parity
  apply product_cons_b t919 tb919 ts919 _ _ ts919_sum ts919_parity
  apply product_cons_b t920 tb920 ts920 _ _ ts920_sum ts920_parity
  apply product_cons_b t921 tb921 ts921 _ _ ts921_sum ts921_parity
  apply product_cons_b t922 tb922 ts922 _ _ ts922_sum ts922_parity
  apply product_cons_b t923 tb923 ts923 _ _ ts923_sum ts923_parity
  apply product_cons_b t924 tb924 ts924 _ _ ts924_sum ts924_parity
  apply product_cons_b t925 tb925 ts925 _ _ ts925_sum ts925_parity
  apply product_cons_b t926 tb926 ts926 _ _ ts926_sum ts926_parity
  apply product_cons_b t927 tb927 ts927 _ _ ts927_sum ts927_parity
  apply product_cons_b t928 tb928 ts928 _ _ ts928_sum ts928_parity
  apply product_cons_b t929 tb929 ts929 _ _ ts929_sum ts929_parity
  apply product_cons_b t930 tb930 ts930 _ _ ts930_sum ts930_parity
  apply product_cons_b t931 tb931 ts931 _ _ ts931_sum ts931_parity
  apply product_cons_b t932 tb932 ts932 _ _ ts932_sum ts932_parity
  apply product_cons_b t933 tb933 ts933 _ _ ts933_sum ts933_parity
  apply product_cons_b t934 tb934 ts934 _ _ ts934_sum ts934_parity
  apply product_cons_b t935 tb935 ts935 _ _ ts935_sum ts935_parity
  apply product_cons_b t936 tb936 ts936 _ _ ts936_sum ts936_parity
  apply product_cons_b t937 tb937 ts937 _ _ ts937_sum ts937_parity
  apply product_cons_b t938 tb938 ts938 _ _ ts938_sum ts938_parity
  apply product_cons_b t939 tb939 ts939 _ _ ts939_sum ts939_parity
  apply product_cons_b t940 tb940 ts940 _ _ ts940_sum ts940_parity
  apply product_cons_b t941 tb941 ts941 _ _ ts941_sum ts941_parity
  apply product_cons_b t942 tb942 ts942 _ _ ts942_sum ts942_parity
  apply product_cons_b t943 tb943 ts943 _ _ ts943_sum ts943_parity
  apply product_cons_b t944 tb944 ts944 _ _ ts944_sum ts944_parity
  apply product_cons_b t945 tb945 ts945 _ _ ts945_sum ts945_parity
  apply product_cons_b t946 tb946 ts946 _ _ ts946_sum ts946_parity
  apply product_cons_b t947 tb947 ts947 _ _ ts947_sum ts947_parity
  apply product_cons_b t948 tb948 ts948 _ _ ts948_sum ts948_parity
  apply product_cons_b t949 tb949 ts949 _ _ ts949_sum ts949_parity
  apply product_cons_b t950 tb950 ts950 _ _ ts950_sum ts950_parity
  apply product_cons_b t951 tb951 ts951 _ _ ts951_sum ts951_parity
  apply product_cons_b t952 tb952 ts952 _ _ ts952_sum ts952_parity
  apply product_cons_b t953 tb953 ts953 _ _ ts953_sum ts953_parity
  apply product_cons_b t954 tb954 ts954 _ _ ts954_sum ts954_parity
  apply product_cons_b t955 tb955 ts955 _ _ ts955_sum ts955_parity
  apply product_cons_b t956 tb956 ts956 _ _ ts956_sum ts956_parity
  apply product_cons_b t957 tb957 ts957 _ _ ts957_sum ts957_parity
  apply product_cons_b t958 tb958 ts958 _ _ ts958_sum ts958_parity
  apply product_cons_b t959 tb959 ts959 _ _ ts959_sum ts959_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d896 da896 ds896 _ _ ds896_sum ds896_parity
  apply product_cons_a d897 da897 ds897 _ _ ds897_sum ds897_parity
  apply product_cons_a d898 da898 ds898 _ _ ds898_sum ds898_parity
  apply product_cons_a d899 da899 ds899 _ _ ds899_sum ds899_parity
  apply product_cons_a d900 da900 ds900 _ _ ds900_sum ds900_parity
  apply product_cons_a d901 da901 ds901 _ _ ds901_sum ds901_parity
  apply product_cons_a d902 da902 ds902 _ _ ds902_sum ds902_parity
  apply product_cons_a d903 da903 ds903 _ _ ds903_sum ds903_parity
  apply product_cons_a d904 da904 ds904 _ _ ds904_sum ds904_parity
  apply product_cons_a d905 da905 ds905 _ _ ds905_sum ds905_parity
  apply product_cons_a d906 da906 ds906 _ _ ds906_sum ds906_parity
  apply product_cons_a d907 da907 ds907 _ _ ds907_sum ds907_parity
  apply product_cons_a d908 da908 ds908 _ _ ds908_sum ds908_parity
  apply product_cons_a d909 da909 ds909 _ _ ds909_sum ds909_parity
  apply product_cons_a d910 da910 ds910 _ _ ds910_sum ds910_parity
  apply product_cons_a d911 da911 ds911 _ _ ds911_sum ds911_parity
  apply product_cons_a d912 da912 ds912 _ _ ds912_sum ds912_parity
  apply product_cons_a d913 da913 ds913 _ _ ds913_sum ds913_parity
  apply product_cons_a d914 da914 ds914 _ _ ds914_sum ds914_parity
  apply product_cons_a d915 da915 ds915 _ _ ds915_sum ds915_parity
  apply product_cons_a d916 da916 ds916 _ _ ds916_sum ds916_parity
  apply product_cons_a d917 da917 ds917 _ _ ds917_sum ds917_parity
  apply product_cons_a d918 da918 ds918 _ _ ds918_sum ds918_parity
  apply product_cons_a d919 da919 ds919 _ _ ds919_sum ds919_parity
  apply product_cons_a d920 da920 ds920 _ _ ds920_sum ds920_parity
  apply product_cons_a d921 da921 ds921 _ _ ds921_sum ds921_parity
  apply product_cons_a d922 da922 ds922 _ _ ds922_sum ds922_parity
  apply product_cons_a d923 da923 ds923 _ _ ds923_sum ds923_parity
  apply product_cons_a d924 da924 ds924 _ _ ds924_sum ds924_parity
  apply product_cons_a d925 da925 ds925 _ _ ds925_sum ds925_parity
  apply product_cons_a d926 da926 ds926 _ _ ds926_sum ds926_parity
  apply product_cons_a d927 da927 ds927 _ _ ds927_sum ds927_parity
  apply product_cons_a d928 da928 ds928 _ _ ds928_sum ds928_parity
  apply product_cons_a d929 da929 ds929 _ _ ds929_sum ds929_parity
  apply product_cons_a d930 da930 ds930 _ _ ds930_sum ds930_parity
  apply product_cons_a d931 da931 ds931 _ _ ds931_sum ds931_parity
  apply product_cons_a d932 da932 ds932 _ _ ds932_sum ds932_parity
  apply product_cons_a d933 da933 ds933 _ _ ds933_sum ds933_parity
  apply product_cons_a d934 da934 ds934 _ _ ds934_sum ds934_parity
  apply product_cons_a d935 da935 ds935 _ _ ds935_sum ds935_parity
  apply product_cons_a d936 da936 ds936 _ _ ds936_sum ds936_parity
  apply product_cons_a d937 da937 ds937 _ _ ds937_sum ds937_parity
  apply product_cons_a d938 da938 ds938 _ _ ds938_sum ds938_parity
  apply product_cons_a d939 da939 ds939 _ _ ds939_sum ds939_parity
  apply product_cons_a d940 da940 ds940 _ _ ds940_sum ds940_parity
  apply product_cons_a d941 da941 ds941 _ _ ds941_sum ds941_parity
  apply product_cons_a d942 da942 ds942 _ _ ds942_sum ds942_parity
  apply product_cons_a d943 da943 ds943 _ _ ds943_sum ds943_parity
  apply product_cons_a d944 da944 ds944 _ _ ds944_sum ds944_parity
  apply product_cons_a d945 da945 ds945 _ _ ds945_sum ds945_parity
  apply product_cons_a d946 da946 ds946 _ _ ds946_sum ds946_parity
  apply product_cons_a d947 da947 ds947 _ _ ds947_sum ds947_parity
  apply product_cons_a d948 da948 ds948 _ _ ds948_sum ds948_parity
  apply product_cons_a d949 da949 ds949 _ _ ds949_sum ds949_parity
  apply product_cons_a d950 da950 ds950 _ _ ds950_sum ds950_parity
  apply product_cons_a d951 da951 ds951 _ _ ds951_sum ds951_parity
  apply product_cons_a d952 da952 ds952 _ _ ds952_sum ds952_parity
  apply product_cons_a d953 da953 ds953 _ _ ds953_sum ds953_parity
  apply product_cons_a d954 da954 ds954 _ _ ds954_sum ds954_parity
  apply product_cons_a d955 da955 ds955 _ _ ds955_sum ds955_parity
  apply product_cons_a d956 da956 ds956 _ _ ds956_sum ds956_parity
  apply product_cons_a d957 da957 ds957 _ _ ds957_sum ds957_parity
  apply product_cons_a d958 da958 ds958 _ _ ds958_sum ds958_parity
  apply product_cons_a d959 da959 ds959 _ _ ds959_sum ds959_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 896).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 896).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 896).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 896).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 896).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 896).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 896).take 64) RightCertificate.wideSecond ((tbRows.drop 896).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 896).take 64) RightCertificate.wideFirst ((daRows.drop 896).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block14
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
