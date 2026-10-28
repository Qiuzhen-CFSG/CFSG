module
public import Theory.SpecificGroups.Rudvalis.Model.OrderLevel0Part6Block1.Soundness
/-!
# Division lookup in certified Rudvalis subword tables

Replace recursive shifts by division by powers of two in the subword tables
used by residuals 224–240. Each equality follows from
`Nat.shiftRight_eq_div_pow`, preserving the previously certified interpretation.

Source: `OrderLevel0Part6Block1.Data` and its ATLAS word-composition witnesses.
-/
namespace Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks.Block1DivMaps
open Part6Block1
set_option Elab.async false

@[expose] public def map0 (x : Nat) : Nat :=
  (Part6Tables.aMapBlock (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map0_eq : map0 = Compressed.map0 := by
  funext x
  simp only [map0, Compressed.map0, Part6Nat.gen0, Nat.shiftRight_eq_div_pow]

@[expose] public def map3 (x : Nat) : Nat :=
  (Part6Tables.bInvMapBlock (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map3_eq : map3 = Compressed.map3 := by
  funext x
  simp only [map3, Compressed.map3, Part6Nat.gen0, Nat.shiftRight_eq_div_pow]

@[expose] public def map4 (x : Nat) : Nat :=
  (Part6Tables.L1G0MapBlock (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map4_eq : map4 = Compressed.map4 := by
  funext x
  simp only [map4, Compressed.map4, Part6Nat.gen1, Nat.shiftRight_eq_div_pow]

@[expose] public def map5 (x : Nat) : Nat :=
  (Part6Tables.L1G1MapBlock (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map5_eq : map5 = Compressed.map5 := by
  funext x
  simp only [map5, Compressed.map5, Part6Nat.gen1, Nat.shiftRight_eq_div_pow]

@[expose] public def map6 (x : Nat) : Nat :=
  (Part6Tables.L1G0InvMapBlock (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map6_eq : map6 = Compressed.map6 := by
  funext x
  simp only [map6, Compressed.map6, Part6Nat.gen1, Nat.shiftRight_eq_div_pow]

@[expose] public def map7 (x : Nat) : Nat :=
  (Part6Tables.L1G1InvMapBlock (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map7_eq : map7 = Compressed.map7 := by
  funext x
  simp only [map7, Compressed.map7, Part6Nat.gen1, Nat.shiftRight_eq_div_pow]

@[expose] public def map8 (x : Nat) : Nat :=
  (Compressed.table8 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map8_eq : map8 = Compressed.map8 := by
  funext x
  simp only [map8, Compressed.map8, Nat.shiftRight_eq_div_pow]

@[expose] public def map9 (x : Nat) : Nat :=
  (Compressed.table9 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map9_eq : map9 = Compressed.map9 := by
  funext x
  simp only [map9, Compressed.map9, Nat.shiftRight_eq_div_pow]

@[expose] public def map10 (x : Nat) : Nat :=
  (Compressed.table10 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map10_eq : map10 = Compressed.map10 := by
  funext x
  simp only [map10, Compressed.map10, Nat.shiftRight_eq_div_pow]

@[expose] public def map11 (x : Nat) : Nat :=
  (Compressed.table11 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map11_eq : map11 = Compressed.map11 := by
  funext x
  simp only [map11, Compressed.map11, Nat.shiftRight_eq_div_pow]

@[expose] public def map12 (x : Nat) : Nat :=
  (Compressed.table12 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map12_eq : map12 = Compressed.map12 := by
  funext x
  simp only [map12, Compressed.map12, Nat.shiftRight_eq_div_pow]

@[expose] public def map13 (x : Nat) : Nat :=
  (Compressed.table13 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map13_eq : map13 = Compressed.map13 := by
  funext x
  simp only [map13, Compressed.map13, Nat.shiftRight_eq_div_pow]

@[expose] public def map14 (x : Nat) : Nat :=
  (Compressed.table14 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map14_eq : map14 = Compressed.map14 := by
  funext x
  simp only [map14, Compressed.map14, Nat.shiftRight_eq_div_pow]

@[expose] public def map15 (x : Nat) : Nat :=
  (Compressed.table15 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map15_eq : map15 = Compressed.map15 := by
  funext x
  simp only [map15, Compressed.map15, Nat.shiftRight_eq_div_pow]

@[expose] public def map17 (x : Nat) : Nat :=
  (Compressed.table17 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map17_eq : map17 = Compressed.map17 := by
  funext x
  simp only [map17, Compressed.map17, Nat.shiftRight_eq_div_pow]

@[expose] public def map18 (x : Nat) : Nat :=
  (Compressed.table18 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map18_eq : map18 = Compressed.map18 := by
  funext x
  simp only [map18, Compressed.map18, Nat.shiftRight_eq_div_pow]

@[expose] public def map19 (x : Nat) : Nat :=
  (Compressed.table19 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map19_eq : map19 = Compressed.map19 := by
  funext x
  simp only [map19, Compressed.map19, Nat.shiftRight_eq_div_pow]

@[expose] public def map20 (x : Nat) : Nat :=
  (Compressed.table20 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map20_eq : map20 = Compressed.map20 := by
  funext x
  simp only [map20, Compressed.map20, Nat.shiftRight_eq_div_pow]

@[expose] public def map21 (x : Nat) : Nat :=
  (Compressed.table21 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map21_eq : map21 = Compressed.map21 := by
  funext x
  simp only [map21, Compressed.map21, Nat.shiftRight_eq_div_pow]

@[expose] public def map22 (x : Nat) : Nat :=
  (Compressed.table22 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map22_eq : map22 = Compressed.map22 := by
  funext x
  simp only [map22, Compressed.map22, Nat.shiftRight_eq_div_pow]

@[expose] public def map23 (x : Nat) : Nat :=
  (Compressed.table23 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map23_eq : map23 = Compressed.map23 := by
  funext x
  simp only [map23, Compressed.map23, Nat.shiftRight_eq_div_pow]

@[expose] public def map24 (x : Nat) : Nat :=
  (Compressed.table24 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map24_eq : map24 = Compressed.map24 := by
  funext x
  simp only [map24, Compressed.map24, Nat.shiftRight_eq_div_pow]

@[expose] public def map25 (x : Nat) : Nat :=
  (Compressed.table25 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map25_eq : map25 = Compressed.map25 := by
  funext x
  simp only [map25, Compressed.map25, Nat.shiftRight_eq_div_pow]

@[expose] public def map27 (x : Nat) : Nat :=
  (Compressed.table27 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map27_eq : map27 = Compressed.map27 := by
  funext x
  simp only [map27, Compressed.map27, Nat.shiftRight_eq_div_pow]

@[expose] public def map28 (x : Nat) : Nat :=
  (Compressed.table28 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map28_eq : map28 = Compressed.map28 := by
  funext x
  simp only [map28, Compressed.map28, Nat.shiftRight_eq_div_pow]

@[expose] public def map29 (x : Nat) : Nat :=
  (Compressed.table29 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map29_eq : map29 = Compressed.map29 := by
  funext x
  simp only [map29, Compressed.map29, Nat.shiftRight_eq_div_pow]

@[expose] public def map30 (x : Nat) : Nat :=
  (Compressed.table30 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map30_eq : map30 = Compressed.map30 := by
  funext x
  simp only [map30, Compressed.map30, Nat.shiftRight_eq_div_pow]

@[expose] public def map31 (x : Nat) : Nat :=
  (Compressed.table31 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map31_eq : map31 = Compressed.map31 := by
  funext x
  simp only [map31, Compressed.map31, Nat.shiftRight_eq_div_pow]

@[expose] public def map32 (x : Nat) : Nat :=
  (Compressed.table32 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map32_eq : map32 = Compressed.map32 := by
  funext x
  simp only [map32, Compressed.map32, Nat.shiftRight_eq_div_pow]

@[expose] public def map33 (x : Nat) : Nat :=
  (Compressed.table33 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map33_eq : map33 = Compressed.map33 := by
  funext x
  simp only [map33, Compressed.map33, Nat.shiftRight_eq_div_pow]

@[expose] public def map35 (x : Nat) : Nat :=
  (Compressed.table35 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map35_eq : map35 = Compressed.map35 := by
  funext x
  simp only [map35, Compressed.map35, Nat.shiftRight_eq_div_pow]

@[expose] public def map36 (x : Nat) : Nat :=
  (Compressed.table36 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map36_eq : map36 = Compressed.map36 := by
  funext x
  simp only [map36, Compressed.map36, Nat.shiftRight_eq_div_pow]

@[expose] public def map37 (x : Nat) : Nat :=
  (Compressed.table37 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map37_eq : map37 = Compressed.map37 := by
  funext x
  simp only [map37, Compressed.map37, Nat.shiftRight_eq_div_pow]

@[expose] public def map39 (x : Nat) : Nat :=
  (Compressed.table39 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map39_eq : map39 = Compressed.map39 := by
  funext x
  simp only [map39, Compressed.map39, Nat.shiftRight_eq_div_pow]

@[expose] public def map40 (x : Nat) : Nat :=
  (Compressed.table40 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map40_eq : map40 = Compressed.map40 := by
  funext x
  simp only [map40, Compressed.map40, Nat.shiftRight_eq_div_pow]

@[expose] public def map42 (x : Nat) : Nat :=
  (Compressed.table42 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map42_eq : map42 = Compressed.map42 := by
  funext x
  simp only [map42, Compressed.map42, Nat.shiftRight_eq_div_pow]

@[expose] public def map46 (x : Nat) : Nat :=
  (Compressed.table46 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map46_eq : map46 = Compressed.map46 := by
  funext x
  simp only [map46, Compressed.map46, Nat.shiftRight_eq_div_pow]

@[expose] public def map47 (x : Nat) : Nat :=
  (Compressed.table47 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map47_eq : map47 = Compressed.map47 := by
  funext x
  simp only [map47, Compressed.map47, Nat.shiftRight_eq_div_pow]

@[expose] public def map48 (x : Nat) : Nat :=
  (Compressed.table48 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map48_eq : map48 = Compressed.map48 := by
  funext x
  simp only [map48, Compressed.map48, Nat.shiftRight_eq_div_pow]

@[expose] public def map49 (x : Nat) : Nat :=
  (Compressed.table49 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map49_eq : map49 = Compressed.map49 := by
  funext x
  simp only [map49, Compressed.map49, Nat.shiftRight_eq_div_pow]

@[expose] public def map50 (x : Nat) : Nat :=
  (Compressed.table50 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map50_eq : map50 = Compressed.map50 := by
  funext x
  simp only [map50, Compressed.map50, Nat.shiftRight_eq_div_pow]

@[expose] public def map51 (x : Nat) : Nat :=
  (Compressed.table51 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map51_eq : map51 = Compressed.map51 := by
  funext x
  simp only [map51, Compressed.map51, Nat.shiftRight_eq_div_pow]

@[expose] public def map52 (x : Nat) : Nat :=
  (Compressed.table52 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map52_eq : map52 = Compressed.map52 := by
  funext x
  simp only [map52, Compressed.map52, Nat.shiftRight_eq_div_pow]

@[expose] public def map53 (x : Nat) : Nat :=
  (Compressed.table53 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map53_eq : map53 = Compressed.map53 := by
  funext x
  simp only [map53, Compressed.map53, Nat.shiftRight_eq_div_pow]

@[expose] public def map56 (x : Nat) : Nat :=
  (Compressed.table56 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map56_eq : map56 = Compressed.map56 := by
  funext x
  simp only [map56, Compressed.map56, Nat.shiftRight_eq_div_pow]

@[expose] public def map58 (x : Nat) : Nat :=
  (Compressed.table58 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map58_eq : map58 = Compressed.map58 := by
  funext x
  simp only [map58, Compressed.map58, Nat.shiftRight_eq_div_pow]

@[expose] public def map59 (x : Nat) : Nat :=
  (Compressed.table59 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map59_eq : map59 = Compressed.map59 := by
  funext x
  simp only [map59, Compressed.map59, Nat.shiftRight_eq_div_pow]

@[expose] public def map60 (x : Nat) : Nat :=
  (Compressed.table60 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map60_eq : map60 = Compressed.map60 := by
  funext x
  simp only [map60, Compressed.map60, Nat.shiftRight_eq_div_pow]

@[expose] public def map61 (x : Nat) : Nat :=
  (Compressed.table61 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map61_eq : map61 = Compressed.map61 := by
  funext x
  simp only [map61, Compressed.map61, Nat.shiftRight_eq_div_pow]

@[expose] public def map62 (x : Nat) : Nat :=
  (Compressed.table62 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map62_eq : map62 = Compressed.map62 := by
  funext x
  simp only [map62, Compressed.map62, Nat.shiftRight_eq_div_pow]

@[expose] public def map63 (x : Nat) : Nat :=
  (Compressed.table63 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map63_eq : map63 = Compressed.map63 := by
  funext x
  simp only [map63, Compressed.map63, Nat.shiftRight_eq_div_pow]

@[expose] public def map64 (x : Nat) : Nat :=
  (Compressed.table64 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map64_eq : map64 = Compressed.map64 := by
  funext x
  simp only [map64, Compressed.map64, Nat.shiftRight_eq_div_pow]

@[expose] public def map65 (x : Nat) : Nat :=
  (Compressed.table65 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map65_eq : map65 = Compressed.map65 := by
  funext x
  simp only [map65, Compressed.map65, Nat.shiftRight_eq_div_pow]

@[expose] public def map66 (x : Nat) : Nat :=
  (Compressed.table66 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map66_eq : map66 = Compressed.map66 := by
  funext x
  simp only [map66, Compressed.map66, Nat.shiftRight_eq_div_pow]

@[expose] public def map67 (x : Nat) : Nat :=
  (Compressed.table67 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map67_eq : map67 = Compressed.map67 := by
  funext x
  simp only [map67, Compressed.map67, Nat.shiftRight_eq_div_pow]

@[expose] public def map68 (x : Nat) : Nat :=
  (Compressed.table68 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map68_eq : map68 = Compressed.map68 := by
  funext x
  simp only [map68, Compressed.map68, Nat.shiftRight_eq_div_pow]

@[expose] public def map69 (x : Nat) : Nat :=
  (Compressed.table69 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map69_eq : map69 = Compressed.map69 := by
  funext x
  simp only [map69, Compressed.map69, Nat.shiftRight_eq_div_pow]

@[expose] public def map70 (x : Nat) : Nat :=
  (Compressed.table70 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map70_eq : map70 = Compressed.map70 := by
  funext x
  simp only [map70, Compressed.map70, Nat.shiftRight_eq_div_pow]

@[expose] public def map71 (x : Nat) : Nat :=
  (Compressed.table71 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map71_eq : map71 = Compressed.map71 := by
  funext x
  simp only [map71, Compressed.map71, Nat.shiftRight_eq_div_pow]

@[expose] public def map73 (x : Nat) : Nat :=
  (Compressed.table73 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map73_eq : map73 = Compressed.map73 := by
  funext x
  simp only [map73, Compressed.map73, Nat.shiftRight_eq_div_pow]

@[expose] public def map74 (x : Nat) : Nat :=
  (Compressed.table74 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map74_eq : map74 = Compressed.map74 := by
  funext x
  simp only [map74, Compressed.map74, Nat.shiftRight_eq_div_pow]

@[expose] public def map75 (x : Nat) : Nat :=
  (Compressed.table75 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map75_eq : map75 = Compressed.map75 := by
  funext x
  simp only [map75, Compressed.map75, Nat.shiftRight_eq_div_pow]

@[expose] public def map77 (x : Nat) : Nat :=
  (Compressed.table77 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map77_eq : map77 = Compressed.map77 := by
  funext x
  simp only [map77, Compressed.map77, Nat.shiftRight_eq_div_pow]

@[expose] public def map78 (x : Nat) : Nat :=
  (Compressed.table78 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map78_eq : map78 = Compressed.map78 := by
  funext x
  simp only [map78, Compressed.map78, Nat.shiftRight_eq_div_pow]

@[expose] public def map79 (x : Nat) : Nat :=
  (Compressed.table79 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map79_eq : map79 = Compressed.map79 := by
  funext x
  simp only [map79, Compressed.map79, Nat.shiftRight_eq_div_pow]

@[expose] public def map80 (x : Nat) : Nat :=
  (Compressed.table80 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map80_eq : map80 = Compressed.map80 := by
  funext x
  simp only [map80, Compressed.map80, Nat.shiftRight_eq_div_pow]

@[expose] public def map82 (x : Nat) : Nat :=
  (Compressed.table82 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map82_eq : map82 = Compressed.map82 := by
  funext x
  simp only [map82, Compressed.map82, Nat.shiftRight_eq_div_pow]

@[expose] public def map83 (x : Nat) : Nat :=
  (Compressed.table83 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map83_eq : map83 = Compressed.map83 := by
  funext x
  simp only [map83, Compressed.map83, Nat.shiftRight_eq_div_pow]

@[expose] public def map84 (x : Nat) : Nat :=
  (Compressed.table84 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map84_eq : map84 = Compressed.map84 := by
  funext x
  simp only [map84, Compressed.map84, Nat.shiftRight_eq_div_pow]

@[expose] public def map85 (x : Nat) : Nat :=
  (Compressed.table85 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map85_eq : map85 = Compressed.map85 := by
  funext x
  simp only [map85, Compressed.map85, Nat.shiftRight_eq_div_pow]

@[expose] public def map86 (x : Nat) : Nat :=
  (Compressed.table86 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map86_eq : map86 = Compressed.map86 := by
  funext x
  simp only [map86, Compressed.map86, Nat.shiftRight_eq_div_pow]

@[expose] public def map88 (x : Nat) : Nat :=
  (Compressed.table88 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map88_eq : map88 = Compressed.map88 := by
  funext x
  simp only [map88, Compressed.map88, Nat.shiftRight_eq_div_pow]

@[expose] public def map89 (x : Nat) : Nat :=
  (Compressed.table89 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map89_eq : map89 = Compressed.map89 := by
  funext x
  simp only [map89, Compressed.map89, Nat.shiftRight_eq_div_pow]

@[expose] public def map90 (x : Nat) : Nat :=
  (Compressed.table90 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map90_eq : map90 = Compressed.map90 := by
  funext x
  simp only [map90, Compressed.map90, Nat.shiftRight_eq_div_pow]

@[expose] public def map91 (x : Nat) : Nat :=
  (Compressed.table91 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map91_eq : map91 = Compressed.map91 := by
  funext x
  simp only [map91, Compressed.map91, Nat.shiftRight_eq_div_pow]

@[expose] public def map93 (x : Nat) : Nat :=
  (Compressed.table93 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map93_eq : map93 = Compressed.map93 := by
  funext x
  simp only [map93, Compressed.map93, Nat.shiftRight_eq_div_pow]

@[expose] public def map94 (x : Nat) : Nat :=
  (Compressed.table94 (x / 64) / 2 ^ (12 * (x % 64))) % 4096 % 4060

public theorem map94_eq : map94 = Compressed.map94 := by
  funext x
  simp only [map94, Compressed.map94, Nat.shiftRight_eq_div_pow]

end Rudvalis.OrderCertificate.ForwardReduction.Part5Residual.Residual3Checks.Block1DivMaps
