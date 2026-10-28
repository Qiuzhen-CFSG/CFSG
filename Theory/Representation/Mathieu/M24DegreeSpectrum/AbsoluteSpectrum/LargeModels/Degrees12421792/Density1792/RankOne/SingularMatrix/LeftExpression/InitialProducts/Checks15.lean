module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.CheckArithmetic
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOne.SingularMatrix.LeftExpression.InitialProducts.Scalar15

/-!
# Exact product checks on rows 960 through 1023

Literal masks are connected to the published lists and packed XOR definitions.
The scalar checks therefore apply to precisely the original checker.
See source/README.md.
-/

set_option Elab.async false

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
namespace Block15

private theorem t_raw : Wide.checkRows 1792 t RightCertificate.wideSecond tb = true := by
  apply product_cons_b t960 tb960 ts960 _ _ ts960_sum ts960_parity
  apply product_cons_b t961 tb961 ts961 _ _ ts961_sum ts961_parity
  apply product_cons_b t962 tb962 ts962 _ _ ts962_sum ts962_parity
  apply product_cons_b t963 tb963 ts963 _ _ ts963_sum ts963_parity
  apply product_cons_b t964 tb964 ts964 _ _ ts964_sum ts964_parity
  apply product_cons_b t965 tb965 ts965 _ _ ts965_sum ts965_parity
  apply product_cons_b t966 tb966 ts966 _ _ ts966_sum ts966_parity
  apply product_cons_b t967 tb967 ts967 _ _ ts967_sum ts967_parity
  apply product_cons_b t968 tb968 ts968 _ _ ts968_sum ts968_parity
  apply product_cons_b t969 tb969 ts969 _ _ ts969_sum ts969_parity
  apply product_cons_b t970 tb970 ts970 _ _ ts970_sum ts970_parity
  apply product_cons_b t971 tb971 ts971 _ _ ts971_sum ts971_parity
  apply product_cons_b t972 tb972 ts972 _ _ ts972_sum ts972_parity
  apply product_cons_b t973 tb973 ts973 _ _ ts973_sum ts973_parity
  apply product_cons_b t974 tb974 ts974 _ _ ts974_sum ts974_parity
  apply product_cons_b t975 tb975 ts975 _ _ ts975_sum ts975_parity
  apply product_cons_b t976 tb976 ts976 _ _ ts976_sum ts976_parity
  apply product_cons_b t977 tb977 ts977 _ _ ts977_sum ts977_parity
  apply product_cons_b t978 tb978 ts978 _ _ ts978_sum ts978_parity
  apply product_cons_b t979 tb979 ts979 _ _ ts979_sum ts979_parity
  apply product_cons_b t980 tb980 ts980 _ _ ts980_sum ts980_parity
  apply product_cons_b t981 tb981 ts981 _ _ ts981_sum ts981_parity
  apply product_cons_b t982 tb982 ts982 _ _ ts982_sum ts982_parity
  apply product_cons_b t983 tb983 ts983 _ _ ts983_sum ts983_parity
  apply product_cons_b t984 tb984 ts984 _ _ ts984_sum ts984_parity
  apply product_cons_b t985 tb985 ts985 _ _ ts985_sum ts985_parity
  apply product_cons_b t986 tb986 ts986 _ _ ts986_sum ts986_parity
  apply product_cons_b t987 tb987 ts987 _ _ ts987_sum ts987_parity
  apply product_cons_b t988 tb988 ts988 _ _ ts988_sum ts988_parity
  apply product_cons_b t989 tb989 ts989 _ _ ts989_sum ts989_parity
  apply product_cons_b t990 tb990 ts990 _ _ ts990_sum ts990_parity
  apply product_cons_b t991 tb991 ts991 _ _ ts991_sum ts991_parity
  apply product_cons_b t992 tb992 ts992 _ _ ts992_sum ts992_parity
  apply product_cons_b t993 tb993 ts993 _ _ ts993_sum ts993_parity
  apply product_cons_b t994 tb994 ts994 _ _ ts994_sum ts994_parity
  apply product_cons_b t995 tb995 ts995 _ _ ts995_sum ts995_parity
  apply product_cons_b t996 tb996 ts996 _ _ ts996_sum ts996_parity
  apply product_cons_b t997 tb997 ts997 _ _ ts997_sum ts997_parity
  apply product_cons_b t998 tb998 ts998 _ _ ts998_sum ts998_parity
  apply product_cons_b t999 tb999 ts999 _ _ ts999_sum ts999_parity
  apply product_cons_b t1000 tb1000 ts1000 _ _ ts1000_sum ts1000_parity
  apply product_cons_b t1001 tb1001 ts1001 _ _ ts1001_sum ts1001_parity
  apply product_cons_b t1002 tb1002 ts1002 _ _ ts1002_sum ts1002_parity
  apply product_cons_b t1003 tb1003 ts1003 _ _ ts1003_sum ts1003_parity
  apply product_cons_b t1004 tb1004 ts1004 _ _ ts1004_sum ts1004_parity
  apply product_cons_b t1005 tb1005 ts1005 _ _ ts1005_sum ts1005_parity
  apply product_cons_b t1006 tb1006 ts1006 _ _ ts1006_sum ts1006_parity
  apply product_cons_b t1007 tb1007 ts1007 _ _ ts1007_sum ts1007_parity
  apply product_cons_b t1008 tb1008 ts1008 _ _ ts1008_sum ts1008_parity
  apply product_cons_b t1009 tb1009 ts1009 _ _ ts1009_sum ts1009_parity
  apply product_cons_b t1010 tb1010 ts1010 _ _ ts1010_sum ts1010_parity
  apply product_cons_b t1011 tb1011 ts1011 _ _ ts1011_sum ts1011_parity
  apply product_cons_b t1012 tb1012 ts1012 _ _ ts1012_sum ts1012_parity
  apply product_cons_b t1013 tb1013 ts1013 _ _ ts1013_sum ts1013_parity
  apply product_cons_b t1014 tb1014 ts1014 _ _ ts1014_sum ts1014_parity
  apply product_cons_b t1015 tb1015 ts1015 _ _ ts1015_sum ts1015_parity
  apply product_cons_b t1016 tb1016 ts1016 _ _ ts1016_sum ts1016_parity
  apply product_cons_b t1017 tb1017 ts1017 _ _ ts1017_sum ts1017_parity
  apply product_cons_b t1018 tb1018 ts1018 _ _ ts1018_sum ts1018_parity
  apply product_cons_b t1019 tb1019 ts1019 _ _ ts1019_sum ts1019_parity
  apply product_cons_b t1020 tb1020 ts1020 _ _ ts1020_sum ts1020_parity
  apply product_cons_b t1021 tb1021 ts1021 _ _ ts1021_sum ts1021_parity
  apply product_cons_b t1022 tb1022 ts1022 _ _ ts1022_sum ts1022_parity
  apply product_cons_b t1023 tb1023 ts1023 _ _ ts1023_sum ts1023_parity
  rfl

private theorem d_raw : Wide.checkRows 1792 d RightCertificate.wideFirst da = true := by
  apply product_cons_a d960 da960 ds960 _ _ ds960_sum ds960_parity
  apply product_cons_a d961 da961 ds961 _ _ ds961_sum ds961_parity
  apply product_cons_a d962 da962 ds962 _ _ ds962_sum ds962_parity
  apply product_cons_a d963 da963 ds963 _ _ ds963_sum ds963_parity
  apply product_cons_a d964 da964 ds964 _ _ ds964_sum ds964_parity
  apply product_cons_a d965 da965 ds965 _ _ ds965_sum ds965_parity
  apply product_cons_a d966 da966 ds966 _ _ ds966_sum ds966_parity
  apply product_cons_a d967 da967 ds967 _ _ ds967_sum ds967_parity
  apply product_cons_a d968 da968 ds968 _ _ ds968_sum ds968_parity
  apply product_cons_a d969 da969 ds969 _ _ ds969_sum ds969_parity
  apply product_cons_a d970 da970 ds970 _ _ ds970_sum ds970_parity
  apply product_cons_a d971 da971 ds971 _ _ ds971_sum ds971_parity
  apply product_cons_a d972 da972 ds972 _ _ ds972_sum ds972_parity
  apply product_cons_a d973 da973 ds973 _ _ ds973_sum ds973_parity
  apply product_cons_a d974 da974 ds974 _ _ ds974_sum ds974_parity
  apply product_cons_a d975 da975 ds975 _ _ ds975_sum ds975_parity
  apply product_cons_a d976 da976 ds976 _ _ ds976_sum ds976_parity
  apply product_cons_a d977 da977 ds977 _ _ ds977_sum ds977_parity
  apply product_cons_a d978 da978 ds978 _ _ ds978_sum ds978_parity
  apply product_cons_a d979 da979 ds979 _ _ ds979_sum ds979_parity
  apply product_cons_a d980 da980 ds980 _ _ ds980_sum ds980_parity
  apply product_cons_a d981 da981 ds981 _ _ ds981_sum ds981_parity
  apply product_cons_a d982 da982 ds982 _ _ ds982_sum ds982_parity
  apply product_cons_a d983 da983 ds983 _ _ ds983_sum ds983_parity
  apply product_cons_a d984 da984 ds984 _ _ ds984_sum ds984_parity
  apply product_cons_a d985 da985 ds985 _ _ ds985_sum ds985_parity
  apply product_cons_a d986 da986 ds986 _ _ ds986_sum ds986_parity
  apply product_cons_a d987 da987 ds987 _ _ ds987_sum ds987_parity
  apply product_cons_a d988 da988 ds988 _ _ ds988_sum ds988_parity
  apply product_cons_a d989 da989 ds989 _ _ ds989_sum ds989_parity
  apply product_cons_a d990 da990 ds990 _ _ ds990_sum ds990_parity
  apply product_cons_a d991 da991 ds991 _ _ ds991_sum ds991_parity
  apply product_cons_a d992 da992 ds992 _ _ ds992_sum ds992_parity
  apply product_cons_a d993 da993 ds993 _ _ ds993_sum ds993_parity
  apply product_cons_a d994 da994 ds994 _ _ ds994_sum ds994_parity
  apply product_cons_a d995 da995 ds995 _ _ ds995_sum ds995_parity
  apply product_cons_a d996 da996 ds996 _ _ ds996_sum ds996_parity
  apply product_cons_a d997 da997 ds997 _ _ ds997_sum ds997_parity
  apply product_cons_a d998 da998 ds998 _ _ ds998_sum ds998_parity
  apply product_cons_a d999 da999 ds999 _ _ ds999_sum ds999_parity
  apply product_cons_a d1000 da1000 ds1000 _ _ ds1000_sum ds1000_parity
  apply product_cons_a d1001 da1001 ds1001 _ _ ds1001_sum ds1001_parity
  apply product_cons_a d1002 da1002 ds1002 _ _ ds1002_sum ds1002_parity
  apply product_cons_a d1003 da1003 ds1003 _ _ ds1003_sum ds1003_parity
  apply product_cons_a d1004 da1004 ds1004 _ _ ds1004_sum ds1004_parity
  apply product_cons_a d1005 da1005 ds1005 _ _ ds1005_sum ds1005_parity
  apply product_cons_a d1006 da1006 ds1006 _ _ ds1006_sum ds1006_parity
  apply product_cons_a d1007 da1007 ds1007 _ _ ds1007_sum ds1007_parity
  apply product_cons_a d1008 da1008 ds1008 _ _ ds1008_sum ds1008_parity
  apply product_cons_a d1009 da1009 ds1009 _ _ ds1009_sum ds1009_parity
  apply product_cons_a d1010 da1010 ds1010 _ _ ds1010_sum ds1010_parity
  apply product_cons_a d1011 da1011 ds1011 _ _ ds1011_sum ds1011_parity
  apply product_cons_a d1012 da1012 ds1012 _ _ ds1012_sum ds1012_parity
  apply product_cons_a d1013 da1013 ds1013 _ _ ds1013_sum ds1013_parity
  apply product_cons_a d1014 da1014 ds1014 _ _ ds1014_sum ds1014_parity
  apply product_cons_a d1015 da1015 ds1015 _ _ ds1015_sum ds1015_parity
  apply product_cons_a d1016 da1016 ds1016 _ _ ds1016_sum ds1016_parity
  apply product_cons_a d1017 da1017 ds1017 _ _ ds1017_sum ds1017_parity
  apply product_cons_a d1018 da1018 ds1018 _ _ ds1018_sum ds1018_parity
  apply product_cons_a d1019 da1019 ds1019 _ _ ds1019_sum ds1019_parity
  apply product_cons_a d1020 da1020 ds1020 _ _ ds1020_sum ds1020_parity
  apply product_cons_a d1021 da1021 ds1021 _ _ ds1021_sum ds1021_parity
  apply product_cons_a d1022 da1022 ds1022 _ _ ds1022_sum ds1022_parity
  apply product_cons_a d1023 da1023 ds1023 _ _ ds1023_sum ds1023_parity
  rfl

set_option maxRecDepth 8192 in
private theorem a_rows : ((Data1792.firstRows.toList).drop 960).take 64 = a := by decide +kernel
set_option maxRecDepth 8192 in
private theorem b_rows : ((Data1792.secondRows.toList).drop 960).take 64 = b := by decide +kernel
set_option maxRecDepth 8192 in
private theorem tb_rows : ((tbRows).drop 960).take 64 = tb := by decide +kernel
set_option maxRecDepth 8192 in
private theorem da_rows : ((daRows).drop 960).take 64 = da := by decide +kernel
private theorem t_xor : List.zipWith Nat.xor a b = t := by decide +kernel
private theorem d_xor : List.zipWith Nat.xor t tb = d := by decide +kernel
private theorem t_rows : (tRows.drop 960).take 64 = t := by
  simp only [tRows, List.drop_zipWith, List.take_zipWith, a_rows, b_rows, t_xor]
private theorem d_rows : (dRows.drop 960).take 64 = d := by
  simp only [dRows, List.drop_zipWith, List.take_zipWith, t_rows, tb_rows, d_xor]

theorem tb_checked : Wide.checkRows 1792 ((tRows.drop 960).take 64) RightCertificate.wideSecond ((tbRows.drop 960).take 64) = true := by
  rw [t_rows, tb_rows]
  exact t_raw

theorem da_checked : Wide.checkRows 1792 ((dRows.drop 960).take 64) RightCertificate.wideFirst ((daRows.drop 960).take 64) = true := by
  rw [d_rows, da_rows]
  exact d_raw


end Block15
end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.RankOneCertificate.SingularMatrix.LeftCertificate.InitialProducts
