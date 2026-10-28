module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction.Thompson
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Source
public import Theory.GroupTheory.ConjugateSpanNormalizer
public import Theory.GroupTheory.ReducedNormal.CentralSeedOvergroup

/-!
# The escaping Thompson commutator and its reduced omega closure

Keep the original R=C_T(L/O∞(L)), L_R=N_L(R)^∞ and the Y constructed
by the escape theorem. A controlled Thompson subgroup J_j(R) gives an
escaping K=[Y,J_j(R)] by the Frattini theorem. The original relative
normality proves L_R T-invariance of K and KR, the Sylow assertion for R,
and [L_R,KR]≤O₂(L_R)∩O₂(KR).

The candidate overgroup's core lies in R=O₂(L_R T). Thus KR inherits
characteristic two from that overgroup. B.2.14 applies to the literal
D=⟨Ω₁Z(R)^{KR}⟩ and proves that D is elementary, lies in R, and has a
two-reduced centralizer quotient inside KR. No whole-radical cyclicity
or identification of the radical omega subgroup is used.

These are intermediate source steps. Choosing j, proving K=[K,J], and
constructing and analyzing the common chief action remain in
qt-d-1319-ff-contradiction; qt-d-1317-supplements owns discharge of the
earlier canonical geometry and the final uniqueness/movement assembly.
Source: Aschbacher--Smith 13.1.9, printed p.870, and B.2.14, p.78.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin ChapterB
open scoped Pointwise

namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.RadicalNormalizers Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

/-- The source commutator, at the literal section centralizer R. -/
@[expose] noncomputable def thompsonCommutator (T L Y : Subgroup G) (j : ℕ) : Subgroup G :=
  ⁅Y,thompsonJ (radicalSylowCentralizer T L) j⁆

/-- The same Y from the refined escape theorem supplies both noncontainments
and the original noncentral action of the Thompson commutator. -/
theorem thompson_commutator_escape {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    {j : ℕ}
    (hN : normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G) ≤
      normalizer (L : Set G))
    (hZ : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G)) :
    Y = thompsonCommutator T L Y j ⊔
        (Y ⊓ normalizer (thompsonJ (radicalSylowCentralizer T L) j : Set G)) ∧
      ¬ thompsonCommutator T L Y j ≤ Y.pCoreIn 2 ∧
      ¬ thompsonCommutator T L Y j ≤ normalizer (L : Set G) ∧
      ⁅omegaOneCenterAmbient (T : Subgroup G),thompsonCommutator T L Y j⁆ ≠ ⊥ := by
  have hj := thompson_index_lt_of_normalizer_control Y (radicalSylowCentralizer T L)
    (normalizer (L : Set G)) w.witness.outside hN
  have hHY := (normal_subgroupOf_iff_le_normalizer w.witness.le_overgroup).mp w.witness.normal
  have hRY := (radicalSylowCentralizer_le T L).trans (hTH.trans hHY)
  have hout := relative_thompson_commutator_outside Y (radicalSylowCentralizer T L)
    (normalizer (L : Set G)) hRY w.sylow hj w.witness.outside hN
  refine ⟨relative_thompson_commutator_factorization Y _ hRY w.sylow hj,
    thompson_commutator_not_le_core Y _ _ hj w.core_le w.witness.outside hN,hout,?_⟩
  intro hc
  rw [commutator_comm] at hc
  exact hout ((commutator_eq_bot_iff_le_centralizer.mp hc).trans hZ)

omit [Finite G] in
private theorem normalizes_commutator (A B Q : Subgroup G)
    (hA : Q ≤ normalizer (A : Set G)) (hB : Q ≤ normalizer (B : Set G)) :
    Q ≤ normalizer ((⁅A,B⁆ : Subgroup G) : Set G) := by
  intro q hq
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (⁅A,B⁆ : Subgroup G).map (MulAut.conj q).toMonoidHom = ⁅A,B⁆
  have ha : A.map (MulAut.conj q).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp (hA hq)
  have hb : B.map (MulAut.conj q).toMonoidHom = B := mem_normalizer_iff_map_conj_eq.mp (hB hq)
  rw [map_commutator,ha,hb]

/-- Relative normality, the common L_R T action, and the Sylow assertion
for the literal KR. No ambient normality of Y or K is asserted. -/
theorem thompson_commutator_invariance {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (j : ℕ) :
    thompsonCommutator T L Y j ≤ Y ∧
      ((thompsonCommutator T L Y j).subgroupOf Y).Normal ∧
      canonicalSupplement T L ⊔ (T : Subgroup G) ≤
        normalizer (thompsonCommutator T L Y j : Set G) ∧
      canonicalSupplement T L ⊔ (T : Subgroup G) ≤
        normalizer ((thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L : Subgroup G) : Set G) ∧
      IsSylowIn 2 (radicalSylowCentralizer T L)
        (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L) := by
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let J := thompsonJ R j
  let K := thompsonCommutator (T : Subgroup G) L Y j
  let B := canonicalSupplement (T : Subgroup G) L ⊔ (T : Subgroup G)
  have hHY := (normal_subgroupOf_iff_le_normalizer w.witness.le_overgroup).mp w.witness.normal
  have hKY : K ≤ Y := le_normalizer_iff_commutator_le_left.mp
    ((thompsonJ_le R j).trans ((radicalSylowCentralizer_le T L).trans (hTH.trans hHY)))
  have hBR : B ≤ normalizer (R : Set G) := sup_le
    (normalizerResidual_le_normalizer L R) (sylow_normalizes_radicalSylowCentralizer hTL)
  have hBK : B ≤ normalizer (K : Set G) := normalizes_commutator Y J B
    ((sup_le hAH hTH).trans hHY) (hBR.trans (normalizer_le_thompson R j))
  exact ⟨hKY,normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left Y J),hBK,
    (le_inf hBK hBR).trans (normalizer_inf_normalizer_le_normalizer_sup K R),
    w.sylow.restrict le_sup_right (sup_le_sup_right hKY R)⟩

/-- The common commutator lies in both literal two-cores. Consequently the
canonical supplement centralizes KR modulo O₂(KR), as used in the hat action. -/
theorem thompson_commutator_core_bound {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H) (hAC : canonicalSupplement T L ≤ C)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (j : ℕ) :
    ⁅canonicalSupplement T L,
        thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L⁆ ≤
      (canonicalSupplement T L).pCoreIn 2 ⊓
        (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L).pCoreIn 2 := by
  let A := canonicalSupplement (T : Subgroup G) L
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let K := thompsonCommutator (T : Subgroup G) L Y j
  have hi := thompson_commutator_invariance w hTH hAH hTL j
  have hRY : IsPGroup 2 R := T.isPGroup'.to_le (radicalSylowCentralizer_le T L)
  have hKA : K ≤ normalizer (A : Set G) := hi.1.trans w.normalizes
  have hRA : R ≤ normalizer (A : Set G) :=
    (radicalSylowCentralizer_le T L).trans (sylow_normalizes_canonicalSupplement hTL)
  have hAR : A ≤ normalizer (R : Set G) := normalizerResidual_le_normalizer L R
  have hAK : ⁅A,K⁆ ≤ A.pCoreIn 2 := by
    apply le_pCoreIn_of_normalizes
      ((isPGroup_pCoreIn 2 Y).to_le ?_)
      (le_normalizer_iff_commutator_le_left.mp hKA) (normalizer_commutator_ge_left A K)
    rw [commutator_comm]
    exact (commutator_mono hi.1 hAC).trans w.commutator_le
  have hARcore : ⁅A,R⁆ ≤ A.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      (hRY.to_le (le_normalizer_iff_commutator_le_right.mp hAR))
      (le_normalizer_iff_commutator_le_left.mp hRA) (normalizer_commutator_ge_left A R)
  have hKRA : K ⊔ R ≤ normalizer (A : Set G) := sup_le hKA hRA
  have hbound : ⁅A,K ⊔ R⁆ ≤ A.pCoreIn 2 := by
    rw [commutator_comm]
    apply commutator_sup_le_of_relative_normal (K ⊔ R) K R A (A.pCoreIn 2)
      (hKRA.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A)))
      le_sup_left le_sup_right
    · rwa [commutator_comm]
    · rwa [commutator_comm]
  exact le_inf hbound (le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 A).to_le hbound)
    (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hi.2.2.2.1))
    (normalizer_commutator_ge_right A (K ⊔ R)))

/-- D is generated by the KR-conjugates of the actual omega-center of R. -/
@[expose] noncomputable def omegaClosure (T L Y : Subgroup G) (j : ℕ) : Subgroup G :=
  conjugateSpanBy (omegaOneCenterAmbient (radicalSylowCentralizer T L))
    (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)

omit [Finite G] in
private theorem normalizer_le_omegaCenter (R : Subgroup G) :
    normalizer (R : Set G) ≤ normalizer (omegaOneCenterAmbient R : Set G) := by
  intro g hg
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (omegaOneCenterAmbient R).map (MulAut.conj g).toMonoidHom = omegaOneCenterAmbient R
  have he : R.map (MulAut.conj g).toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp hg
  rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective,he]

/-- The seed, its KR-closure, and the canonical action use the same subgroups.
Elementary abelianness and two-reducedness of this closure are later steps. -/
theorem omegaClosure_geometry {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) (j : ℕ) :
    omegaOneCenterAmbient (radicalSylowCentralizer T L) ≤ omegaClosure T L Y j ∧
      omegaClosure T L Y j ≤ thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L ∧
      (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L) ≤
        normalizer (omegaClosure T L Y j : Set G) ∧
      canonicalSupplement T L ⊔ (T : Subgroup G) ≤
        normalizer (omegaClosure T L Y j : Set G) := by
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let K := thompsonCommutator (T : Subgroup G) L Y j
  have hi := thompson_commutator_invariance w hTH hAH hTL j
  have hseed : omegaOneCenterAmbient R ≤ R := fun x hx =>
    ((mem_omegaOneCenterAmbient_iff R x).mp hx).1
  have hBR : canonicalSupplement T L ⊔ (T : Subgroup G) ≤ normalizer (R : Set G) :=
    sup_le (normalizerResidual_le_normalizer L R) (sylow_normalizes_radicalSylowCentralizer hTL)
  exact ⟨le_conjugateSpanBy _ _,conjugateSpanBy_le_self (hseed.trans le_sup_right),
    le_normalizer_conjugateSpanBy _ _,normalizes_conjugateSpanBy _ _ _
      (hBR.trans (normalizer_le_omegaCenter R)) hi.2.2.2.1⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction

namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
open Chapter1 Chapter1.Section02 Chapter12.Section02 ChapterA.Section04 Escape
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

omit [Finite G] in
/-- The candidate's two-core is contained in the literal R, because it is
normal in L_R T and lies in T. -/
theorem candidate_core_le_radical {L H : Subgroup G}
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) : H.pCoreIn 2 ≤ radicalSylowCentralizer T L := by
  have hQT := pCoreIn_le_sylow H (T.subtype hTH)
  rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] at hQT
  exact (le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 H) (hQT.trans le_sup_right)
    ((sup_le hAH hTH).trans (H.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image H (pCore 2 H))))).trans_eq hcore

/-- B.2.14 for the actual D inside KR. Its centralizer quotient, rather
than an unrelated action image, has trivial two-core. -/
theorem omegaClosure_reduced (h : Hypothesis1311 T) {L H C Y : Subgroup G}
    (w : RefinedWitness T L H C Y) (hH : IsMaximalTwoLocal H)
    (hTH : (T : Subgroup G) ≤ H) (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) :
    IsPReduced 2 ((omegaClosure T L Y j).subgroupOf
      (thompsonCommutator T L Y j ⊔ radicalSylowCentralizer T L)) := by
  let R := radicalSylowCentralizer (T : Subgroup G) L
  let K := thompsonCommutator (T : Subgroup G) L Y j
  let B := K ⊔ R
  let Z := omegaOneCenterAmbient R
  have hi := thompson_commutator_invariance w hTH hAH hTL j
  have hBH : B ≤ H := sup_le (hi.1.trans w.witness.le_overgroup)
    ((radicalSylowCentralizer_le T L).trans hTH)
  have hQB : H.pCoreIn 2 ≤ B := (candidate_core_le_radical hTH hAH hcore).trans le_sup_right
  have hHe : H ∈ He G := mem_He_iff.mpr (h.simpleQTKE.evenCharacteristic T H hH hTH)
  have hBe : B ∈ He G :=
    pCoreIn_selfCentralizing_of_core_centralizer_le hHe hBH (inf_le_left.trans hQB)
  obtain ⟨S,hS⟩ := hi.2.2.2.2
  have hZR : Z ≤ R := fun z hz => ((mem_omegaOneCenterAmbient_iff R z).mp hz).1
  have hZB : Z ≤ B := hZR.trans le_sup_right
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian R
  let : IsElementaryAbelian 2 (Z.subgroupOf B) := IsElementaryAbelian.subgroupOf hZB
  have hZS : Z.subgroupOf B ≤ (S : Subgroup B) := by
    apply (map_le_map_iff_of_injective B.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hZB,hS]
    exact hZR
  have hZC : Z.subgroupOf B ≤ centralizer (S : Set B) := by
    intro z hz s hs
    apply Subtype.ext
    exact ((mem_omegaOneCenterAmbient_iff R (z : G)).mp hz).2.2 s
      (by
        have hm := mem_map_of_mem B.subtype hs
        change (s : G) ∈ (S : Subgroup B).map B.subtype at hm
        rwa [hS] at hm)
  have hr := centralSeed_normalClosure_reduced S (Z.subgroupOf B) hZS hZC (mem_He_iff.mp hBe)
  rwa [normalClosure_subgroupOf_eq_conjugateSpanBy Z B hZB] at hr

/-- In ambient notation the actual D is elementary and lies in R. These
are the hypotheses needed for the later B.2.4 rank comparison. -/
theorem omegaClosure_elementary_le_radical (h : Hypothesis1311 T)
    {L H C Y : Subgroup G} (w : RefinedWitness T L H C Y)
    (hH : IsMaximalTwoLocal H) (hTH : (T : Subgroup G) ≤ H)
    (hAH : canonicalSupplement T L ≤ H)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hcore : (canonicalSupplement T L ⊔ (T : Subgroup G)).pCoreIn 2 =
      radicalSylowCentralizer T L) (j : ℕ) :
    IsElementaryAbelian 2 (omegaClosure T L Y j) ∧
      omegaClosure T L Y j ≤ radicalSylowCentralizer T L := by
  let D := omegaClosure (T : Subgroup G) L Y j
  let B := thompsonCommutator (T : Subgroup G) L Y j ⊔ radicalSylowCentralizer T L
  have hDB : D ≤ B := (omegaClosure_geometry w hTH hAH hTL j).2.1
  have hr := omegaClosure_reduced h w hH hTH hAH hTL hcore j
  let := hr.elementary
  have he : IsElementaryAbelian 2 D := IsElementaryAbelian.of_injective
    (subgroupOfEquivOfLe hDB).symm.toMonoidHom (subgroupOfEquivOfLe hDB).symm.injective
  have hc : D ≤ B.pCoreIn 2 := by
    have hm := map_mono (f := B.subtype) hr.le_pCore
    rwa [map_subgroupOf_eq_of_le hDB] at hm
  obtain ⟨S,hS⟩ := (thompson_commutator_invariance w hTH hAH hTL j).2.2.2.2
  exact ⟨he,hc.trans ((pCoreIn_le_sylow B S).trans_eq hS)⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.FFContradiction
