module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.MovedSize
public import CFSG.Quasithin.ChapterE.Section03.Parameters.UniformOutsideFixed

/-!
# The fixed quotient of an arbitrary small offender

Write W=[V,L] and A=Wᵍ∩M. A corank bound k for Vᵍ∩M gives
|Wᵍ:A|≤2ᵏ. Consequently |W:C_W(L)|≥2ᵐ implies
|A:C_A(Lᵍ)|≥2^(m-k). The two-factor permutation action then supplies
a nonfixed element normalizing W whenever m>k+1. Uniform fixed spaces
outside C_A(Lᵍ) give the same lower bound m-k for the full local moduleA
parameter. None of these calculations assumes an A₅ marking.

Source: Aschbacher--Smith, proof of 10.2.12, printed pp.754--755.
The module bounds and the uniform-fixed-space geometry remain separate inputs.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10.SmallOffender.Recognition
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

private theorem relIndex_ne_zero (P Q : Subgroup G) : P.relIndex Q ≠ 0 := by
  change Nat.card (Q ⧸ P.subgroupOf Q) ≠ 0
  exact Nat.card_ne_zero.mpr ⟨inferInstance,inferInstance⟩

/-- The literal moved intersection loses at most the full offender's corank. -/
theorem moved_intersection_index_le {g : G} {k : ℕ}
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom) ⊓
      D.maximalLocal).relIndex ((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom) ≤
        2 ^ k := by
  let V := D.fullModule.map (MulAut.conj g).toMonoidHom
  let W := (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  let := D.fullModule_elementary hu
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hLV : L ≤ normalizer (D.fullModule : Set G) :=
    ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule
  have hWV : W ≤ V := map_mono (le_normalizer_iff_commutator_le_left.mp hLV)
  have he : D.maximalLocal.relIndex V = 2 ^ subgroupCorank V (V ⊓ D.maximalLocal) := by
    rw [subgroupCorank_eq_quotient_finrank, relIndex_eq_two_pow_quotient_finrank V D.maximalLocal]
    congr 1
    rw [inf_subgroupOf_left]
  rw [inf_relIndex_left]
  exact (relIndex_le_of_le_right hWV (relIndex_ne_zero _ _)).trans
    (he.le.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hsmall))

/-- The fixed-quotient index estimate, with an arbitrary model dimension m. -/
theorem offender_fixed_index {g : G} {m k : ℕ} (hkm : k ≤ m)
    (hsize : 2 ^ m ≤ (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    2 ^ (m-k) ≤ (centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      ((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) := by
  let W := (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom
  let A := W ⊓ D.maximalLocal
  let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
  have hCW : 2 ^ m ≤ C.relIndex W := by
    change 2 ^ m ≤ (centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      ((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    rw [← Theory.Quasithin.map_centralizer (MulAut.conj g) L,
      relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hsize
  have hmul := relIndex_inf_mul_relIndex C A W
  rw [inf_of_le_left (show A ≤ W from inf_le_left)] at hmul
  have hprod : 2 ^ m ≤ C.relIndex A * A.relIndex W :=
    hCW.trans ((relIndex_le_of_le_left (show C ⊓ A ≤ C from inf_le_left)
      (relIndex_ne_zero _ _)).trans_eq hmul.symm)
  have hb : 2 ^ m ≤ C.relIndex A * 2 ^ k :=
    hprod.trans (Nat.mul_le_mul_left _ (moved_intersection_index_le D hsmall))
  apply Nat.le_of_mul_le_mul_right ?_ (by positivity : 0 < 2 ^ k)
  rwa [← pow_add, Nat.sub_add_cancel hkm]

/-- The original two-factor normalizer contains a nonfixed offender element
as soon as the moved fixed quotient has size greater than 2^(k+1). -/
theorem exists_nonfixed_normalizing_element
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) {g : G} {k : ℕ}
    (hsize : 2 ^ (k+1) < (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    ∃ b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom,
      b ∈ D.maximalLocal ∧ b ∈ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) ∧
      b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) := by
  let W := (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom
  let A := W ⊓ D.maximalLocal
  let B := A ⊓ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G)
  let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
  have hBA : B.relIndex A ≤ 2 := by
    rw [show B = A ⊓ normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G) from rfl,
      inf_relIndex_left]
    exact source_nonnormal_moved_normalizer_index_le_two D hn inf_le_right
  have hBW : B.relIndex W ≤ 2 ^ (k+1) := by
    calc
      B.relIndex W = B.relIndex A * A.relIndex W :=
        (relIndex_mul_relIndex B A W inf_le_left inf_le_left).symm
      _ ≤ 2 * 2 ^ k := Nat.mul_le_mul hBA (moved_intersection_index_le D hsmall)
      _ = 2 ^ (k+1) := by rw [pow_succ, Nat.mul_comm]
  have hCW : 2 ^ (k+1) < C.relIndex W := by
    change 2 ^ (k+1) < (centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)).relIndex
      ((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom)
    rw [← Theory.Quasithin.map_centralizer (MulAut.conj g) L,
      relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hsize
  have hnBC : ¬ B ≤ C := by
    intro hBC
    have hi := relIndex_le_of_le_left hBC (relIndex_ne_zero B W)
    omega
  obtain ⟨b,hb,hbc⟩ := Set.not_subset.mp hnBC
  exact ⟨b,hb.1.1,hb.1.2,hb.2,hbc⟩

/-- Uniform fixed spaces supply the full local automizer's lower bound.
The action is the literal conjugation action on W, including its fixed part. -/
theorem offender_moduleA_lower {g : G} {m k : ℕ} (hkm : k < m)
    (hsize : 2 ^ m ≤ (centralizer (L : Set G)).relIndex ⁅D.fullModule,L⁆)
    (hsmall : subgroupCorank (D.fullModule.map (MulAut.conj g).toMonoidHom)
      (D.fullModule.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal) ≤ k) :
    let W := ⁅D.fullModule,L⁆
    let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
    let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
    let _ := source_full_moved_elementary D
    A ≤ normalizer (W : Set G) → ¬ A ≤ centralizer (W : Set G) →
    (∀ a ∈ A, a ∉ C → W ⊓ centralizer ({a} : Set G) ≤ centralizer (A : Set G)) →
    ((m-k : ℕ) : ℕ∞) ≤ moduleA
      ((automizerRepresentation W).comp (inducedAutomizer W D.maximalLocal).subtype) := by
  dsimp only
  let W := ⁅D.fullModule,L⁆
  let A := W.map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal
  let C := centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)
  let := source_full_moved_elementary D
  let : IsElementaryAbelian 2 (W.map (MulAut.conj g).toMonoidHom) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 A := offender_elementary_of_le
    (show A ≤ W.map (MulAut.conj g).toMonoidHom from inf_le_left)
  intro hAN hactive hfix
  exact moduleA_localAutomizer_ge_of_uniform_outside W A C D.maximalLocal hAN inf_le_right
    hactive (Nat.sub_pos_of_lt hkm) (offender_fixed_index D hkm.le hsize hsmall) hfix

end CFSG.Quasithin.Chapter10.SmallOffender.Recognition
