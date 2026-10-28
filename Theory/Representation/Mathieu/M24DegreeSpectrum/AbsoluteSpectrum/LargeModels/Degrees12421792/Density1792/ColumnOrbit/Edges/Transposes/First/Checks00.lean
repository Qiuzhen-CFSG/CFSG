module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnOrbit.Edges.Transposes.FirstSegments

/-!
# Checked first-matrix rectangles, original rows 0–127

Each short check compares eight original rows with 128 candidate columns.
Concatenation then covers every candidate column for these original rows.
Source and reproduction: `../source/README.md`.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.Transposes.First

private theorem row000_part00 :
    checkRow r000 (nat_lit 1) c00 = true := by
  decide +kernel

private theorem row000_part01 :
    checkRow r000 (nat_lit 1) c01 = true := by
  decide +kernel

private theorem row000_part02 :
    checkRow r000 (nat_lit 1) c02 = true := by
  decide +kernel

private theorem row000_part03 :
    checkRow r000 (nat_lit 1) c03 = true := by
  decide +kernel

private theorem row000_part04 :
    checkRow r000 (nat_lit 1) c04 = true := by
  decide +kernel

private theorem row000_part05 :
    checkRow r000 (nat_lit 1) c05 = true := by
  decide +kernel

private theorem row000_part06 :
    checkRow r000 (nat_lit 1) c06 = true := by
  decide +kernel

private theorem row000_part07 :
    checkRow r000 (nat_lit 1) c07 = true := by
  decide +kernel

private theorem row000_part08 :
    checkRow r000 (nat_lit 1) c08 = true := by
  decide +kernel

private theorem row000_part09 :
    checkRow r000 (nat_lit 1) c09 = true := by
  decide +kernel

private theorem row000_part10 :
    checkRow r000 (nat_lit 1) c10 = true := by
  decide +kernel

private theorem row000_part11 :
    checkRow r000 (nat_lit 1) c11 = true := by
  decide +kernel

private theorem row000_part12 :
    checkRow r000 (nat_lit 1) c12 = true := by
  decide +kernel

private theorem row000_part13 :
    checkRow r000 (nat_lit 1) c13 = true := by
  decide +kernel

theorem row000_checked : checkRow r000 (nat_lit 1) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row000_part00, row000_part01, row000_part02, row000_part03, row000_part04, row000_part05, row000_part06, row000_part07, row000_part08, row000_part09, row000_part10, row000_part11, row000_part12, row000_part13⟩

private theorem row001_part00 :
    checkRow r001 (nat_lit 256) c00 = true := by
  decide +kernel

private theorem row001_part01 :
    checkRow r001 (nat_lit 256) c01 = true := by
  decide +kernel

private theorem row001_part02 :
    checkRow r001 (nat_lit 256) c02 = true := by
  decide +kernel

private theorem row001_part03 :
    checkRow r001 (nat_lit 256) c03 = true := by
  decide +kernel

private theorem row001_part04 :
    checkRow r001 (nat_lit 256) c04 = true := by
  decide +kernel

private theorem row001_part05 :
    checkRow r001 (nat_lit 256) c05 = true := by
  decide +kernel

private theorem row001_part06 :
    checkRow r001 (nat_lit 256) c06 = true := by
  decide +kernel

private theorem row001_part07 :
    checkRow r001 (nat_lit 256) c07 = true := by
  decide +kernel

private theorem row001_part08 :
    checkRow r001 (nat_lit 256) c08 = true := by
  decide +kernel

private theorem row001_part09 :
    checkRow r001 (nat_lit 256) c09 = true := by
  decide +kernel

private theorem row001_part10 :
    checkRow r001 (nat_lit 256) c10 = true := by
  decide +kernel

private theorem row001_part11 :
    checkRow r001 (nat_lit 256) c11 = true := by
  decide +kernel

private theorem row001_part12 :
    checkRow r001 (nat_lit 256) c12 = true := by
  decide +kernel

private theorem row001_part13 :
    checkRow r001 (nat_lit 256) c13 = true := by
  decide +kernel

theorem row001_checked : checkRow r001 (nat_lit 256) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row001_part00, row001_part01, row001_part02, row001_part03, row001_part04, row001_part05, row001_part06, row001_part07, row001_part08, row001_part09, row001_part10, row001_part11, row001_part12, row001_part13⟩

private theorem row002_part00 :
    checkRow r002 (nat_lit 65536) c00 = true := by
  decide +kernel

private theorem row002_part01 :
    checkRow r002 (nat_lit 65536) c01 = true := by
  decide +kernel

private theorem row002_part02 :
    checkRow r002 (nat_lit 65536) c02 = true := by
  decide +kernel

private theorem row002_part03 :
    checkRow r002 (nat_lit 65536) c03 = true := by
  decide +kernel

private theorem row002_part04 :
    checkRow r002 (nat_lit 65536) c04 = true := by
  decide +kernel

private theorem row002_part05 :
    checkRow r002 (nat_lit 65536) c05 = true := by
  decide +kernel

private theorem row002_part06 :
    checkRow r002 (nat_lit 65536) c06 = true := by
  decide +kernel

private theorem row002_part07 :
    checkRow r002 (nat_lit 65536) c07 = true := by
  decide +kernel

private theorem row002_part08 :
    checkRow r002 (nat_lit 65536) c08 = true := by
  decide +kernel

private theorem row002_part09 :
    checkRow r002 (nat_lit 65536) c09 = true := by
  decide +kernel

private theorem row002_part10 :
    checkRow r002 (nat_lit 65536) c10 = true := by
  decide +kernel

private theorem row002_part11 :
    checkRow r002 (nat_lit 65536) c11 = true := by
  decide +kernel

private theorem row002_part12 :
    checkRow r002 (nat_lit 65536) c12 = true := by
  decide +kernel

private theorem row002_part13 :
    checkRow r002 (nat_lit 65536) c13 = true := by
  decide +kernel

theorem row002_checked : checkRow r002 (nat_lit 65536) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row002_part00, row002_part01, row002_part02, row002_part03, row002_part04, row002_part05, row002_part06, row002_part07, row002_part08, row002_part09, row002_part10, row002_part11, row002_part12, row002_part13⟩

private theorem row003_part00 :
    checkRow r003 (nat_lit 16777216) c00 = true := by
  decide +kernel

private theorem row003_part01 :
    checkRow r003 (nat_lit 16777216) c01 = true := by
  decide +kernel

private theorem row003_part02 :
    checkRow r003 (nat_lit 16777216) c02 = true := by
  decide +kernel

private theorem row003_part03 :
    checkRow r003 (nat_lit 16777216) c03 = true := by
  decide +kernel

private theorem row003_part04 :
    checkRow r003 (nat_lit 16777216) c04 = true := by
  decide +kernel

private theorem row003_part05 :
    checkRow r003 (nat_lit 16777216) c05 = true := by
  decide +kernel

private theorem row003_part06 :
    checkRow r003 (nat_lit 16777216) c06 = true := by
  decide +kernel

private theorem row003_part07 :
    checkRow r003 (nat_lit 16777216) c07 = true := by
  decide +kernel

private theorem row003_part08 :
    checkRow r003 (nat_lit 16777216) c08 = true := by
  decide +kernel

private theorem row003_part09 :
    checkRow r003 (nat_lit 16777216) c09 = true := by
  decide +kernel

private theorem row003_part10 :
    checkRow r003 (nat_lit 16777216) c10 = true := by
  decide +kernel

private theorem row003_part11 :
    checkRow r003 (nat_lit 16777216) c11 = true := by
  decide +kernel

private theorem row003_part12 :
    checkRow r003 (nat_lit 16777216) c12 = true := by
  decide +kernel

private theorem row003_part13 :
    checkRow r003 (nat_lit 16777216) c13 = true := by
  decide +kernel

theorem row003_checked : checkRow r003 (nat_lit 16777216) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row003_part00, row003_part01, row003_part02, row003_part03, row003_part04, row003_part05, row003_part06, row003_part07, row003_part08, row003_part09, row003_part10, row003_part11, row003_part12, row003_part13⟩

private theorem row004_part00 :
    checkRow r004 (nat_lit 4294967296) c00 = true := by
  decide +kernel

private theorem row004_part01 :
    checkRow r004 (nat_lit 4294967296) c01 = true := by
  decide +kernel

private theorem row004_part02 :
    checkRow r004 (nat_lit 4294967296) c02 = true := by
  decide +kernel

private theorem row004_part03 :
    checkRow r004 (nat_lit 4294967296) c03 = true := by
  decide +kernel

private theorem row004_part04 :
    checkRow r004 (nat_lit 4294967296) c04 = true := by
  decide +kernel

private theorem row004_part05 :
    checkRow r004 (nat_lit 4294967296) c05 = true := by
  decide +kernel

private theorem row004_part06 :
    checkRow r004 (nat_lit 4294967296) c06 = true := by
  decide +kernel

private theorem row004_part07 :
    checkRow r004 (nat_lit 4294967296) c07 = true := by
  decide +kernel

private theorem row004_part08 :
    checkRow r004 (nat_lit 4294967296) c08 = true := by
  decide +kernel

private theorem row004_part09 :
    checkRow r004 (nat_lit 4294967296) c09 = true := by
  decide +kernel

private theorem row004_part10 :
    checkRow r004 (nat_lit 4294967296) c10 = true := by
  decide +kernel

private theorem row004_part11 :
    checkRow r004 (nat_lit 4294967296) c11 = true := by
  decide +kernel

private theorem row004_part12 :
    checkRow r004 (nat_lit 4294967296) c12 = true := by
  decide +kernel

private theorem row004_part13 :
    checkRow r004 (nat_lit 4294967296) c13 = true := by
  decide +kernel

theorem row004_checked : checkRow r004 (nat_lit 4294967296) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row004_part00, row004_part01, row004_part02, row004_part03, row004_part04, row004_part05, row004_part06, row004_part07, row004_part08, row004_part09, row004_part10, row004_part11, row004_part12, row004_part13⟩

private theorem row005_part00 :
    checkRow r005 (nat_lit 1099511627776) c00 = true := by
  decide +kernel

private theorem row005_part01 :
    checkRow r005 (nat_lit 1099511627776) c01 = true := by
  decide +kernel

private theorem row005_part02 :
    checkRow r005 (nat_lit 1099511627776) c02 = true := by
  decide +kernel

private theorem row005_part03 :
    checkRow r005 (nat_lit 1099511627776) c03 = true := by
  decide +kernel

private theorem row005_part04 :
    checkRow r005 (nat_lit 1099511627776) c04 = true := by
  decide +kernel

private theorem row005_part05 :
    checkRow r005 (nat_lit 1099511627776) c05 = true := by
  decide +kernel

private theorem row005_part06 :
    checkRow r005 (nat_lit 1099511627776) c06 = true := by
  decide +kernel

private theorem row005_part07 :
    checkRow r005 (nat_lit 1099511627776) c07 = true := by
  decide +kernel

private theorem row005_part08 :
    checkRow r005 (nat_lit 1099511627776) c08 = true := by
  decide +kernel

private theorem row005_part09 :
    checkRow r005 (nat_lit 1099511627776) c09 = true := by
  decide +kernel

private theorem row005_part10 :
    checkRow r005 (nat_lit 1099511627776) c10 = true := by
  decide +kernel

private theorem row005_part11 :
    checkRow r005 (nat_lit 1099511627776) c11 = true := by
  decide +kernel

private theorem row005_part12 :
    checkRow r005 (nat_lit 1099511627776) c12 = true := by
  decide +kernel

private theorem row005_part13 :
    checkRow r005 (nat_lit 1099511627776) c13 = true := by
  decide +kernel

theorem row005_checked : checkRow r005 (nat_lit 1099511627776) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row005_part00, row005_part01, row005_part02, row005_part03, row005_part04, row005_part05, row005_part06, row005_part07, row005_part08, row005_part09, row005_part10, row005_part11, row005_part12, row005_part13⟩

private theorem row006_part00 :
    checkRow r006 (nat_lit 281474976710656) c00 = true := by
  decide +kernel

private theorem row006_part01 :
    checkRow r006 (nat_lit 281474976710656) c01 = true := by
  decide +kernel

private theorem row006_part02 :
    checkRow r006 (nat_lit 281474976710656) c02 = true := by
  decide +kernel

private theorem row006_part03 :
    checkRow r006 (nat_lit 281474976710656) c03 = true := by
  decide +kernel

private theorem row006_part04 :
    checkRow r006 (nat_lit 281474976710656) c04 = true := by
  decide +kernel

private theorem row006_part05 :
    checkRow r006 (nat_lit 281474976710656) c05 = true := by
  decide +kernel

private theorem row006_part06 :
    checkRow r006 (nat_lit 281474976710656) c06 = true := by
  decide +kernel

private theorem row006_part07 :
    checkRow r006 (nat_lit 281474976710656) c07 = true := by
  decide +kernel

private theorem row006_part08 :
    checkRow r006 (nat_lit 281474976710656) c08 = true := by
  decide +kernel

private theorem row006_part09 :
    checkRow r006 (nat_lit 281474976710656) c09 = true := by
  decide +kernel

private theorem row006_part10 :
    checkRow r006 (nat_lit 281474976710656) c10 = true := by
  decide +kernel

private theorem row006_part11 :
    checkRow r006 (nat_lit 281474976710656) c11 = true := by
  decide +kernel

private theorem row006_part12 :
    checkRow r006 (nat_lit 281474976710656) c12 = true := by
  decide +kernel

private theorem row006_part13 :
    checkRow r006 (nat_lit 281474976710656) c13 = true := by
  decide +kernel

theorem row006_checked : checkRow r006 (nat_lit 281474976710656) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row006_part00, row006_part01, row006_part02, row006_part03, row006_part04, row006_part05, row006_part06, row006_part07, row006_part08, row006_part09, row006_part10, row006_part11, row006_part12, row006_part13⟩

private theorem row007_part00 :
    checkRow r007 (nat_lit 72057594037927936) c00 = true := by
  decide +kernel

private theorem row007_part01 :
    checkRow r007 (nat_lit 72057594037927936) c01 = true := by
  decide +kernel

private theorem row007_part02 :
    checkRow r007 (nat_lit 72057594037927936) c02 = true := by
  decide +kernel

private theorem row007_part03 :
    checkRow r007 (nat_lit 72057594037927936) c03 = true := by
  decide +kernel

private theorem row007_part04 :
    checkRow r007 (nat_lit 72057594037927936) c04 = true := by
  decide +kernel

private theorem row007_part05 :
    checkRow r007 (nat_lit 72057594037927936) c05 = true := by
  decide +kernel

private theorem row007_part06 :
    checkRow r007 (nat_lit 72057594037927936) c06 = true := by
  decide +kernel

private theorem row007_part07 :
    checkRow r007 (nat_lit 72057594037927936) c07 = true := by
  decide +kernel

private theorem row007_part08 :
    checkRow r007 (nat_lit 72057594037927936) c08 = true := by
  decide +kernel

private theorem row007_part09 :
    checkRow r007 (nat_lit 72057594037927936) c09 = true := by
  decide +kernel

private theorem row007_part10 :
    checkRow r007 (nat_lit 72057594037927936) c10 = true := by
  decide +kernel

private theorem row007_part11 :
    checkRow r007 (nat_lit 72057594037927936) c11 = true := by
  decide +kernel

private theorem row007_part12 :
    checkRow r007 (nat_lit 72057594037927936) c12 = true := by
  decide +kernel

private theorem row007_part13 :
    checkRow r007 (nat_lit 72057594037927936) c13 = true := by
  decide +kernel

theorem row007_checked : checkRow r007 (nat_lit 72057594037927936) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row007_part00, row007_part01, row007_part02, row007_part03, row007_part04, row007_part05, row007_part06, row007_part07, row007_part08, row007_part09, row007_part10, row007_part11, row007_part12, row007_part13⟩

private theorem row008_part00 :
    checkRow r008 (nat_lit 18446744073709551616) c00 = true := by
  decide +kernel

private theorem row008_part01 :
    checkRow r008 (nat_lit 18446744073709551616) c01 = true := by
  decide +kernel

private theorem row008_part02 :
    checkRow r008 (nat_lit 18446744073709551616) c02 = true := by
  decide +kernel

private theorem row008_part03 :
    checkRow r008 (nat_lit 18446744073709551616) c03 = true := by
  decide +kernel

private theorem row008_part04 :
    checkRow r008 (nat_lit 18446744073709551616) c04 = true := by
  decide +kernel

private theorem row008_part05 :
    checkRow r008 (nat_lit 18446744073709551616) c05 = true := by
  decide +kernel

private theorem row008_part06 :
    checkRow r008 (nat_lit 18446744073709551616) c06 = true := by
  decide +kernel

private theorem row008_part07 :
    checkRow r008 (nat_lit 18446744073709551616) c07 = true := by
  decide +kernel

private theorem row008_part08 :
    checkRow r008 (nat_lit 18446744073709551616) c08 = true := by
  decide +kernel

private theorem row008_part09 :
    checkRow r008 (nat_lit 18446744073709551616) c09 = true := by
  decide +kernel

private theorem row008_part10 :
    checkRow r008 (nat_lit 18446744073709551616) c10 = true := by
  decide +kernel

private theorem row008_part11 :
    checkRow r008 (nat_lit 18446744073709551616) c11 = true := by
  decide +kernel

private theorem row008_part12 :
    checkRow r008 (nat_lit 18446744073709551616) c12 = true := by
  decide +kernel

private theorem row008_part13 :
    checkRow r008 (nat_lit 18446744073709551616) c13 = true := by
  decide +kernel

theorem row008_checked : checkRow r008 (nat_lit 18446744073709551616) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row008_part00, row008_part01, row008_part02, row008_part03, row008_part04, row008_part05, row008_part06, row008_part07, row008_part08, row008_part09, row008_part10, row008_part11, row008_part12, row008_part13⟩

private theorem row009_part00 :
    checkRow r009 (nat_lit 4722366482869645213696) c00 = true := by
  decide +kernel

private theorem row009_part01 :
    checkRow r009 (nat_lit 4722366482869645213696) c01 = true := by
  decide +kernel

private theorem row009_part02 :
    checkRow r009 (nat_lit 4722366482869645213696) c02 = true := by
  decide +kernel

private theorem row009_part03 :
    checkRow r009 (nat_lit 4722366482869645213696) c03 = true := by
  decide +kernel

private theorem row009_part04 :
    checkRow r009 (nat_lit 4722366482869645213696) c04 = true := by
  decide +kernel

private theorem row009_part05 :
    checkRow r009 (nat_lit 4722366482869645213696) c05 = true := by
  decide +kernel

private theorem row009_part06 :
    checkRow r009 (nat_lit 4722366482869645213696) c06 = true := by
  decide +kernel

private theorem row009_part07 :
    checkRow r009 (nat_lit 4722366482869645213696) c07 = true := by
  decide +kernel

private theorem row009_part08 :
    checkRow r009 (nat_lit 4722366482869645213696) c08 = true := by
  decide +kernel

private theorem row009_part09 :
    checkRow r009 (nat_lit 4722366482869645213696) c09 = true := by
  decide +kernel

private theorem row009_part10 :
    checkRow r009 (nat_lit 4722366482869645213696) c10 = true := by
  decide +kernel

private theorem row009_part11 :
    checkRow r009 (nat_lit 4722366482869645213696) c11 = true := by
  decide +kernel

private theorem row009_part12 :
    checkRow r009 (nat_lit 4722366482869645213696) c12 = true := by
  decide +kernel

private theorem row009_part13 :
    checkRow r009 (nat_lit 4722366482869645213696) c13 = true := by
  decide +kernel

theorem row009_checked : checkRow r009 (nat_lit 4722366482869645213696) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row009_part00, row009_part01, row009_part02, row009_part03, row009_part04, row009_part05, row009_part06, row009_part07, row009_part08, row009_part09, row009_part10, row009_part11, row009_part12, row009_part13⟩

private theorem row010_part00 :
    checkRow r010 (nat_lit 1208925819614629174706176) c00 = true := by
  decide +kernel

private theorem row010_part01 :
    checkRow r010 (nat_lit 1208925819614629174706176) c01 = true := by
  decide +kernel

private theorem row010_part02 :
    checkRow r010 (nat_lit 1208925819614629174706176) c02 = true := by
  decide +kernel

private theorem row010_part03 :
    checkRow r010 (nat_lit 1208925819614629174706176) c03 = true := by
  decide +kernel

private theorem row010_part04 :
    checkRow r010 (nat_lit 1208925819614629174706176) c04 = true := by
  decide +kernel

private theorem row010_part05 :
    checkRow r010 (nat_lit 1208925819614629174706176) c05 = true := by
  decide +kernel

private theorem row010_part06 :
    checkRow r010 (nat_lit 1208925819614629174706176) c06 = true := by
  decide +kernel

private theorem row010_part07 :
    checkRow r010 (nat_lit 1208925819614629174706176) c07 = true := by
  decide +kernel

private theorem row010_part08 :
    checkRow r010 (nat_lit 1208925819614629174706176) c08 = true := by
  decide +kernel

private theorem row010_part09 :
    checkRow r010 (nat_lit 1208925819614629174706176) c09 = true := by
  decide +kernel

private theorem row010_part10 :
    checkRow r010 (nat_lit 1208925819614629174706176) c10 = true := by
  decide +kernel

private theorem row010_part11 :
    checkRow r010 (nat_lit 1208925819614629174706176) c11 = true := by
  decide +kernel

private theorem row010_part12 :
    checkRow r010 (nat_lit 1208925819614629174706176) c12 = true := by
  decide +kernel

private theorem row010_part13 :
    checkRow r010 (nat_lit 1208925819614629174706176) c13 = true := by
  decide +kernel

theorem row010_checked : checkRow r010 (nat_lit 1208925819614629174706176) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row010_part00, row010_part01, row010_part02, row010_part03, row010_part04, row010_part05, row010_part06, row010_part07, row010_part08, row010_part09, row010_part10, row010_part11, row010_part12, row010_part13⟩

private theorem row011_part00 :
    checkRow r011 (nat_lit 309485009821345068724781056) c00 = true := by
  decide +kernel

private theorem row011_part01 :
    checkRow r011 (nat_lit 309485009821345068724781056) c01 = true := by
  decide +kernel

private theorem row011_part02 :
    checkRow r011 (nat_lit 309485009821345068724781056) c02 = true := by
  decide +kernel

private theorem row011_part03 :
    checkRow r011 (nat_lit 309485009821345068724781056) c03 = true := by
  decide +kernel

private theorem row011_part04 :
    checkRow r011 (nat_lit 309485009821345068724781056) c04 = true := by
  decide +kernel

private theorem row011_part05 :
    checkRow r011 (nat_lit 309485009821345068724781056) c05 = true := by
  decide +kernel

private theorem row011_part06 :
    checkRow r011 (nat_lit 309485009821345068724781056) c06 = true := by
  decide +kernel

private theorem row011_part07 :
    checkRow r011 (nat_lit 309485009821345068724781056) c07 = true := by
  decide +kernel

private theorem row011_part08 :
    checkRow r011 (nat_lit 309485009821345068724781056) c08 = true := by
  decide +kernel

private theorem row011_part09 :
    checkRow r011 (nat_lit 309485009821345068724781056) c09 = true := by
  decide +kernel

private theorem row011_part10 :
    checkRow r011 (nat_lit 309485009821345068724781056) c10 = true := by
  decide +kernel

private theorem row011_part11 :
    checkRow r011 (nat_lit 309485009821345068724781056) c11 = true := by
  decide +kernel

private theorem row011_part12 :
    checkRow r011 (nat_lit 309485009821345068724781056) c12 = true := by
  decide +kernel

private theorem row011_part13 :
    checkRow r011 (nat_lit 309485009821345068724781056) c13 = true := by
  decide +kernel

theorem row011_checked : checkRow r011 (nat_lit 309485009821345068724781056) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row011_part00, row011_part01, row011_part02, row011_part03, row011_part04, row011_part05, row011_part06, row011_part07, row011_part08, row011_part09, row011_part10, row011_part11, row011_part12, row011_part13⟩

private theorem row012_part00 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c00 = true := by
  decide +kernel

private theorem row012_part01 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c01 = true := by
  decide +kernel

private theorem row012_part02 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c02 = true := by
  decide +kernel

private theorem row012_part03 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c03 = true := by
  decide +kernel

private theorem row012_part04 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c04 = true := by
  decide +kernel

private theorem row012_part05 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c05 = true := by
  decide +kernel

private theorem row012_part06 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c06 = true := by
  decide +kernel

private theorem row012_part07 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c07 = true := by
  decide +kernel

private theorem row012_part08 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c08 = true := by
  decide +kernel

private theorem row012_part09 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c09 = true := by
  decide +kernel

private theorem row012_part10 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c10 = true := by
  decide +kernel

private theorem row012_part11 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c11 = true := by
  decide +kernel

private theorem row012_part12 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c12 = true := by
  decide +kernel

private theorem row012_part13 :
    checkRow r012 (nat_lit 79228162514264337593543950336) c13 = true := by
  decide +kernel

theorem row012_checked : checkRow r012 (nat_lit 79228162514264337593543950336) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row012_part00, row012_part01, row012_part02, row012_part03, row012_part04, row012_part05, row012_part06, row012_part07, row012_part08, row012_part09, row012_part10, row012_part11, row012_part12, row012_part13⟩

private theorem row013_part00 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c00 = true := by
  decide +kernel

private theorem row013_part01 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c01 = true := by
  decide +kernel

private theorem row013_part02 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c02 = true := by
  decide +kernel

private theorem row013_part03 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c03 = true := by
  decide +kernel

private theorem row013_part04 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c04 = true := by
  decide +kernel

private theorem row013_part05 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c05 = true := by
  decide +kernel

private theorem row013_part06 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c06 = true := by
  decide +kernel

private theorem row013_part07 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c07 = true := by
  decide +kernel

private theorem row013_part08 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c08 = true := by
  decide +kernel

private theorem row013_part09 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c09 = true := by
  decide +kernel

private theorem row013_part10 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c10 = true := by
  decide +kernel

private theorem row013_part11 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c11 = true := by
  decide +kernel

private theorem row013_part12 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c12 = true := by
  decide +kernel

private theorem row013_part13 :
    checkRow r013 (nat_lit 20282409603651670423947251286016) c13 = true := by
  decide +kernel

theorem row013_checked : checkRow r013 (nat_lit 20282409603651670423947251286016) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row013_part00, row013_part01, row013_part02, row013_part03, row013_part04, row013_part05, row013_part06, row013_part07, row013_part08, row013_part09, row013_part10, row013_part11, row013_part12, row013_part13⟩

private theorem row014_part00 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c00 = true := by
  decide +kernel

private theorem row014_part01 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c01 = true := by
  decide +kernel

private theorem row014_part02 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c02 = true := by
  decide +kernel

private theorem row014_part03 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c03 = true := by
  decide +kernel

private theorem row014_part04 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c04 = true := by
  decide +kernel

private theorem row014_part05 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c05 = true := by
  decide +kernel

private theorem row014_part06 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c06 = true := by
  decide +kernel

private theorem row014_part07 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c07 = true := by
  decide +kernel

private theorem row014_part08 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c08 = true := by
  decide +kernel

private theorem row014_part09 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c09 = true := by
  decide +kernel

private theorem row014_part10 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c10 = true := by
  decide +kernel

private theorem row014_part11 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c11 = true := by
  decide +kernel

private theorem row014_part12 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c12 = true := by
  decide +kernel

private theorem row014_part13 :
    checkRow r014 (nat_lit 5192296858534827628530496329220096) c13 = true := by
  decide +kernel

theorem row014_checked : checkRow r014 (nat_lit 5192296858534827628530496329220096) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row014_part00, row014_part01, row014_part02, row014_part03, row014_part04, row014_part05, row014_part06, row014_part07, row014_part08, row014_part09, row014_part10, row014_part11, row014_part12, row014_part13⟩

private theorem row015_part00 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c00 = true := by
  decide +kernel

private theorem row015_part01 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c01 = true := by
  decide +kernel

private theorem row015_part02 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c02 = true := by
  decide +kernel

private theorem row015_part03 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c03 = true := by
  decide +kernel

private theorem row015_part04 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c04 = true := by
  decide +kernel

private theorem row015_part05 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c05 = true := by
  decide +kernel

private theorem row015_part06 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c06 = true := by
  decide +kernel

private theorem row015_part07 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c07 = true := by
  decide +kernel

private theorem row015_part08 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c08 = true := by
  decide +kernel

private theorem row015_part09 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c09 = true := by
  decide +kernel

private theorem row015_part10 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c10 = true := by
  decide +kernel

private theorem row015_part11 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c11 = true := by
  decide +kernel

private theorem row015_part12 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c12 = true := by
  decide +kernel

private theorem row015_part13 :
    checkRow r015 (nat_lit 1329227995784915872903807060280344576) c13 = true := by
  decide +kernel

theorem row015_checked : checkRow r015 (nat_lit 1329227995784915872903807060280344576) columns = true := by
  rw [columns_split]
  simp only [checkRow_append, Bool.and_eq_true, and_assoc]
  exact ⟨row015_part00, row015_part01, row015_part02, row015_part03, row015_part04, row015_part05, row015_part06, row015_part07, row015_part08, row015_part09, row015_part10, row015_part11, row015_part12, row015_part13⟩

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1792.ColumnEdges.Transposes.First
