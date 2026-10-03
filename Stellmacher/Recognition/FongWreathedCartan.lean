module

public import Stellmacher.Recognition.FongWreathedCentralizerQuotients
public import Stellmacher.Recognition.FongWreathedOddCentralizers
public import Stellmacher.Recognition.FongWreathedCentralizers
public import Theory.Character.ModularBlock.LocalColumnNorm
public import Theory.Character.ModularBlock.Cartan
public import Theory.Character.ModularBlock.SmallQuotientCartan

/-!
# Local Cartan data for Fong's wreathed Sylow subgroup

The local column-norm identity applies to every element of the actual Sylow
two-subgroup, using the centralizer datum at the ambient modular place.
The Cartan quadratic-form identity then converts genuine local decomposition
data into that column norm. Both statements are independent of the orientation
chosen for the wreathed presentation.

The odd-core quotients at F, F³ and XF² are two-groups of orders 8, 8 and 16.
The quotient at J is a central order-four extension of S₄, and the quotient
at F² is isomorphic to it. Genuine quotient transfer therefore gives the
singleton matrices (8), (8), (16), and the two-character matrix
`[[16,8],[8,12]]` at both F² and J. Their modular degrees are respectively
one and `(1,2)`, so their ordinary block dimensions are 8, 8, 16, 96 and 96.
All data use the ambient modular place. The final theorem chooses the same
actual presentation as the compatible fusion and centralizer computation.

Source: Fong, *Some Sylow subgroups of order 32 and a characterization of
U(3,3)*, J. Algebra 6 (1967), printed p. 71, equations (6)–(7).
-/

public section
noncomputable section

namespace Stellmacher.Recognition.FongWreathedIntrinsic

open scoped BigOperators
open ModularBlock PrincipalBlockConstruction CompatibleBrauerBlock

variable {G : Type*} [Group G] [Finite G] (S : Sylow 2 G)

/-- The ambient principal-block column at a Sylow element is the sum of
squared ordinary degrees in its compatible local principal block. -/
theorem sylow_principalBlock_local_column_norm
    (d : PrincipalCongruenceBlockData G) (y : S) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk (y : G)) *
        star (d.chi i (ConjClasses.mk (y : G))) =
      ∑ j ∈ (localData d (Subgroup.centralizer ({(y : G)} : Set G))).block,
        (localData d (Subgroup.centralizer ({(y : G)} : Set G))).chi j
          (ConjClasses.mk 1) ^ 2 := by
  obtain ⟨n, hn⟩ := S.isPGroup' y
  apply LocalColumnNorm.principalBlock_local_column_norm
  exact ⟨n, congrArg Subtype.val hn⟩

/-- A genuine local decomposition matrix computes the ambient column norm
by its Cartan quadratic form on the irreducible modular degrees. -/
theorem sylow_principalBlock_column_norm_eq_cartan
    (d : PrincipalCongruenceBlockData G) (y : S) {n : ℕ}
    (a : Cartan.PrincipalDecompositionData
      (localData d (Subgroup.centralizer ({(y : G)} : Set G))) n) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk (y : G)) *
        star (d.chi i (ConjClasses.mk (y : G))) =
      ∑ j, ∑ k, (a.cartan j k : ℂ) *
        (a.family.degree j : ℂ) * (a.family.degree k : ℂ) :=
  (sylow_principalBlock_local_column_norm S d y).trans a.sum_degree_sq

open ABG Cartan CompatibleLocalBlock

variable [IsSimpleGroup G] (P : Wreathed.Presentation S 2)

local notation "CF" => Subgroup.centralizer ({((F P : S) : G)} : Set G)
local notation "CF3" => Subgroup.centralizer ({((F P ^ 3 : S) : G)} : Set G)
local notation "CF2" => Subgroup.centralizer ({((F P ^ 2 : S) : G)} : Set G)
local notation "CXF2" => Subgroup.centralizer ({((X P * F P ^ 2 : S) : G)} : Set G)
local notation "CJ" => Subgroup.centralizer ({((J P : S) : G)} : Set G)

variable (x : G) (hx : orderOf x = 2)
  [Group.IsSolvable (Subgroup.centralizer ({x} : Set G))]

include x hx in
/-- The actual compatible principal block of `C(F)` has its singleton
Cartan matrix and the corresponding ordinary block dimension. -/
theorem centralizerF_principal_cartan (d : PrincipalCongruenceBlockData G) :
    let l := localData d CF
    ∃ a : PrincipalDecompositionData l 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = 8 ∧
      ∑ i ∈ l.block, l.chi i (ConjClasses.mk 1) ^ 2 = (8 : ℂ) := by
  dsimp only
  have hodd : Odd (Nat.card (pPrimeCore 2 CF)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := CF))
  obtain ⟨a, hd, hc⟩ := exists_twoGroup_oddQuotient_cartan
    (localData d CF) (pPrimeCore 2 CF) hodd
    (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 CF
      (centralizerF_hasNormalPComplement S P x hx))
  rw [centralizerF_oddCore_card S P x hx] at hc
  exact ⟨a, hd, hc, singleton_sum_degree_sq _ a hd hc⟩

include x hx in
/-- The actual compatible principal block of `C(F³)` has its singleton
Cartan matrix and the corresponding ordinary block dimension. -/
theorem centralizerF_cube_principal_cartan (d : PrincipalCongruenceBlockData G) :
    let l := localData d CF3
    ∃ a : PrincipalDecompositionData l 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = 8 ∧
      ∑ i ∈ l.block, l.chi i (ConjClasses.mk 1) ^ 2 = (8 : ℂ) := by
  dsimp only
  have hodd : Odd (Nat.card (pPrimeCore 2 CF3)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := CF3))
  obtain ⟨a, hd, hc⟩ := exists_twoGroup_oddQuotient_cartan
    (localData d CF3) (pPrimeCore 2 CF3) hodd
    (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 CF3
      (centralizerF_cube_hasNormalPComplement S P x hx))
  rw [centralizerF_cube_oddCore_card S P x hx] at hc
  exact ⟨a, hd, hc, singleton_sum_degree_sq _ a hd hc⟩

include x hx in
/-- The actual compatible principal block of `C(XF²)` has its singleton
Cartan matrix and the corresponding ordinary block dimension. -/
theorem centralizerXF_sq_principal_cartan (d : PrincipalCongruenceBlockData G) :
    let l := localData d CXF2
    ∃ a : PrincipalDecompositionData l 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = 16 ∧
      ∑ i ∈ l.block, l.chi i (ConjClasses.mk 1) ^ 2 = (16 : ℂ) := by
  dsimp only
  have hodd : Odd (Nat.card (pPrimeCore 2 CXF2)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := CXF2))
  obtain ⟨a, hd, hc⟩ := exists_twoGroup_oddQuotient_cartan
    (localData d CXF2) (pPrimeCore 2 CXF2) hodd
    (isPGroup_quotient_pPrimeCore_of_hasNormalPComplement 2 CXF2
      (centralizerXF_sq_hasNormalPComplement S P x hx))
  rw [centralizerXF_sq_oddCore_card S P x hx] at hc
  exact ⟨a, hd, hc, singleton_sum_degree_sq _ a hd hc⟩

include x hx in
/-- The central order-four extension in the odd-core quotient of `C(J)`
has the genuine two-character principal Cartan matrix. This works at any
prescribed datum on that quotient, allowing transport from `C(F²)`. -/
theorem centralizerJ_oddCore_principal_cartan
    (d : PrincipalCongruenceBlockData (CJ ⧸ pPrimeCore 2 CJ)) :
    ∃ a : PrincipalDecompositionData d 2,
      a.family.degree 0 = 1 ∧ a.family.degree 1 = 2 ∧
      a.cartan 0 0 = 16 ∧ a.cartan 0 1 = 8 ∧
      a.cartan 1 0 = 8 ∧ a.cartan 1 1 = 12 := by
  let Z := Subgroup.zpowers
    (QuotientGroup.mk' (pPrimeCore 2 CJ) (squareInCentralizerJ S P))
  let _ : Z.Normal := squareInCentralizerJ_quotient_zpowers_normal S P
  obtain ⟨e⟩ := centralizerJ_oddCore_square_quotient_equiv S P x hx
  exact exists_centralFour_symmetricFour_cartan d Z
    (Subgroup.zpowers_le.mpr (squareInCentralizerJ_quotient_mem_center S P))
    (squareInCentralizerJ_quotient_zpowers_card S P) e

include x hx in
/-- The actual compatible principal block of `C(J)` has simple modular
degrees `1,2`, Cartan matrix `[[16,8],[8,12]]`, and ordinary dimension 96. -/
theorem centralizerJ_principal_cartan (d : PrincipalCongruenceBlockData G) :
    let l := localData d CJ
    ∃ a : PrincipalDecompositionData l 2,
      a.family.degree 0 = 1 ∧ a.family.degree 1 = 2 ∧
      a.cartan 0 0 = 16 ∧ a.cartan 0 1 = 8 ∧
      a.cartan 1 0 = 8 ∧ a.cartan 1 1 = 12 ∧
      ∑ i ∈ l.block, l.chi i (ConjClasses.mk 1) ^ 2 = (96 : ℂ) := by
  dsimp only
  let l := localData d CJ
  let q := compatibleQuotientPrincipalCongruenceBlockData l (pPrimeCore 2 CJ)
  have hodd : Odd (Nat.card (pPrimeCore 2 CJ)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := CJ))
  obtain ⟨aQ, hd0, hd1, hc00, hc01, hc10, hc11⟩ :=
    centralizerJ_oddCore_principal_cartan S P x hx q
  let a := aQ.ofOddQuotient l (pPrimeCore 2 CJ) hodd
  have hd : a.family.degree = aQ.family.degree := rfl
  have hc (j k : Fin 2) : a.cartan j k = aQ.cartan j k :=
    aQ.ofOddQuotient_cartan l (pPrimeCore 2 CJ) hodd j k
  have h0 : a.family.degree 0 = 1 := (congrFun hd 0).trans hd0
  have h1 : a.family.degree 1 = 2 := (congrFun hd 1).trans hd1
  have h00 := (hc 0 0).trans hc00
  have h01 := (hc 0 1).trans hc01
  have h10 := (hc 1 0).trans hc10
  have h11 := (hc 1 1).trans hc11
  exact ⟨a, h0, h1, h00, h01, h10, h11,
    twoCharacter_sum_degree_sq l a h0 h1 h00 h01 h10 h11⟩

include x hx in
/-- The actual compatible principal block of `C(F²)` has simple modular
degrees `1,2`, Cartan matrix `[[16,8],[8,12]]`, and ordinary dimension 96. -/
theorem centralizerF2_principal_cartan (d : PrincipalCongruenceBlockData G) :
    let l := localData d CF2
    ∃ a : PrincipalDecompositionData l 2,
      a.family.degree 0 = 1 ∧ a.family.degree 1 = 2 ∧
      a.cartan 0 0 = 16 ∧ a.cartan 0 1 = 8 ∧
      a.cartan 1 0 = 8 ∧ a.cartan 1 1 = 12 ∧
      ∑ i ∈ l.block, l.chi i (ConjClasses.mk 1) ^ 2 = (96 : ℂ) := by
  dsimp only
  let l := localData d CF2
  let q := compatibleQuotientPrincipalCongruenceBlockData l (pPrimeCore 2 CF2)
  have hodd : Odd (Nat.card (pPrimeCore 2 CF2)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := CF2))
  let e := centralizerF2OddCoreEquiv S P
  obtain ⟨aQ, hd0, hd1, hc00, hc01, hc10, hc11⟩ :=
    centralizerJ_oddCore_principal_cartan S P x hx (q.transport e)
  obtain ⟨a, hd, hc⟩ := exists_oddNormalQuotient_of_equiv l
    (pPrimeCore 2 CF2) hodd e aQ
  have h0 : a.family.degree 0 = 1 := (congrFun hd 0).trans hd0
  have h1 : a.family.degree 1 = 2 := (congrFun hd 1).trans hd1
  have h00 := (hc 0 0).trans hc00
  have h01 := (hc 0 1).trans hc01
  have h10 := (hc 1 0).trans hc10
  have h11 := (hc 1 1).trans hc11
  exact ⟨a, h0, h1, h00, h01, h10, h11,
    twoCharacter_sum_degree_sq l a h0 h1 h00 h01 h10 h11⟩

/-- All five compatible local computations, retaining the genuine decomposition
matrices and the ordinary degree-square sums at one ambient modular place. -/
structure LocalPrincipalCartanData (d : PrincipalCongruenceBlockData G) : Prop where
  F_computation :
    ∃ a : PrincipalDecompositionData (localData d CF) 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = 8 ∧
      ∑ i ∈ (localData d CF).block,
        (localData d CF).chi i (ConjClasses.mk 1) ^ 2 = (8 : ℂ)
  F_cube_computation :
    ∃ a : PrincipalDecompositionData (localData d CF3) 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = 8 ∧
      ∑ i ∈ (localData d CF3).block,
        (localData d CF3).chi i (ConjClasses.mk 1) ^ 2 = (8 : ℂ)
  XF_sq_computation :
    ∃ a : PrincipalDecompositionData (localData d CXF2) 1,
      a.family.degree 0 = 1 ∧ a.cartan 0 0 = 16 ∧
      ∑ i ∈ (localData d CXF2).block,
        (localData d CXF2).chi i (ConjClasses.mk 1) ^ 2 = (16 : ℂ)
  F_sq_computation :
    ∃ a : PrincipalDecompositionData (localData d CF2) 2,
      a.family.degree 0 = 1 ∧ a.family.degree 1 = 2 ∧
      a.cartan 0 0 = 16 ∧ a.cartan 0 1 = 8 ∧
      a.cartan 1 0 = 8 ∧ a.cartan 1 1 = 12 ∧
      ∑ i ∈ (localData d CF2).block,
        (localData d CF2).chi i (ConjClasses.mk 1) ^ 2 = (96 : ℂ)
  J_computation :
    ∃ a : PrincipalDecompositionData (localData d CJ) 2,
      a.family.degree 0 = 1 ∧ a.family.degree 1 = 2 ∧
      a.cartan 0 0 = 16 ∧ a.cartan 0 1 = 8 ∧
      a.cartan 1 0 = 8 ∧ a.cartan 1 1 = 12 ∧
      ∑ i ∈ (localData d CJ).block,
        (localData d CJ).chi i (ConjClasses.mk 1) ^ 2 = (96 : ℂ)

include x hx in
/-- The local Cartan computations hold for every actual height-two presentation;
fusion orientation is not an additional premise. -/
theorem localPrincipalCartanData (d : PrincipalCongruenceBlockData G) :
    LocalPrincipalCartanData S P d where
  F_computation := centralizerF_principal_cartan S P x hx d
  F_cube_computation := centralizerF_cube_principal_cartan S P x hx d
  XF_sq_computation := centralizerXF_sq_principal_cartan S P x hx d
  F_sq_computation := centralizerF2_principal_cartan S P x hx d
  J_computation := centralizerJ_principal_cartan S P x hx d

include x hx in
/-- One compatible set of actual representatives simultaneously realizes Fong's
fusion/centralizer data and all the local principal-block Cartan computations. -/
theorem exists_compatible_localPrincipalCartanData
    (hS : IsWreathedOfHeight S 2) (d : PrincipalCongruenceBlockData G) :
    ∃ P : Wreathed.Presentation S 2,
      LocalCentralizerData S P ∧ LocalPrincipalCartanData S P d := by
  obtain ⟨P, hc⟩ := exists_localCentralizerData S hS x hx
  exact ⟨P, hc, localPrincipalCartanData S P x hx d⟩

end Stellmacher.Recognition.FongWreathedIntrinsic
