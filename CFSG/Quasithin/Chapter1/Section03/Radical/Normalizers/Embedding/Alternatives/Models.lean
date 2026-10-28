module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.Alternatives.OddCore
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity
public import Theory.Mathieu.M22.Properties.Simplicity
public import Theory.Mathieu.M24.Properties.Simplicity
public import BenderSuzuki.External.Huppert.XI.theorem_3_6
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# Quasisimplicity of the small models in A.3.12

Perfectness is inherited from the genuine local-family subgroup and its
quotients. The concrete simplicity theorems then imply quasisimplicity for
the alternating, PSL, Suzuki and Mathieu models. Covers already include
quasisimplicity in their mathematical definition. For each nonsplit extension
with a two-group kernel, removing the two-core gives the same quotient as
removing the two-core of its displayed quasisimple quotient.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
A.3.12(2)–(20), printed p.47; proof of 1.3.8, printed p.513.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin CFSG.Quasithin.Chapter1.Section02
open CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
universe u
variable {A : Type u} [Group A]

/-- A perfect simple group is quasisimple. -/
theorem quasisimple_of_perfect_simple [Group.IsPerfect A] [IsSimpleGroup A] :
    IsQuasisimple A := by
  have hc : center A = ⊥ := by
    rcases (inferInstance : (center A).Normal).eq_bot_or_eq_top with h | h
    · exact h
    · exact (Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp h)).elim
  refine { simple := ?_ }
  exact (MulEquiv.isSimpleGroup_congr
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)).mpr
      inferInstance

/-- Removing the two-core of a finite quasisimple group preserves quasisimplicity. -/
theorem core_quasisimple [Finite A] (h : IsQuasisimple A) :
    IsQuasisimple (A ⧸ pCore 2 A) := by
  let := h
  let : IsSimpleGroup (A ⧸ center A) := h.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  let : Nontrivial (A ⧸ pCore 2 A) := QuotientGroup.nontrivial_iff.mpr (by
    intro he
    let : Group.IsNilpotent (pCore 2 A) := pCore_isNilpotent
    let : Group.IsSolvable (⊤ : Subgroup A) := he ▸ inferInstance
    let : Group.IsSolvable A := Group.isSolvable_of_surjective
      (f := (topEquiv : (⊤ : Subgroup A) ≃* A).toMonoidHom) topEquiv.surjective
    exact Group.IsPerfect.not_isSolvable A inferInstance)
  exact IsQuasisimple.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)

/-- Perfect alternating models of degree at least five are quasisimple. -/
theorem alternating_quasisimple [Group.IsPerfect A] {n : ℕ}
    (h : LocalModels.IsAlternating A n) (hn : 5 ≤ n) : IsQuasisimple A := by
  obtain ⟨e⟩ := h
  let : IsSimpleGroup (alternatingGroup (Fin n)) := alternatingGroup.isSimpleGroup (by simpa)
  let : IsSimpleGroup A := e.isSimpleGroup
  exact quasisimple_of_perfect_simple

/-- Perfect PSL models in the simple parameter range are quasisimple. -/
theorem psl_quasisimple [Group.IsPerfect A] {n q : ℕ}
    (h : ClassicalGroup.IsPSL A n q) (hn : 3 ≤ n ∨ n = 2 ∧ 4 ≤ q) :
    IsQuasisimple A := by
  obtain ⟨F, _, _, hc, ⟨e⟩⟩ := h
  have hs : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) := by
    rcases hn with hn | ⟨rfl, hq⟩
    · exact Atlas.psl_simple_high_rank n hn
    · exact Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let := hs
  let : IsSimpleGroup A := e.isSimpleGroup
  exact quasisimple_of_perfect_simple

/-- The nondegenerate concrete Suzuki models are quasisimple when perfect. -/
theorem suzuki_quasisimple [Group.IsPerfect A] {m : ℕ}
    (h : Nonempty (A ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m)) (hm : 1 ≤ m) :
    IsQuasisimple A := by
  let := (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let : IsSimpleGroup A := h.some.isSimpleGroup
  exact quasisimple_of_perfect_simple

/-- The actual M₂₂ model is quasisimple when perfect. -/
theorem m22_quasisimple [Group.IsPerfect A]
    (h : Nonempty (A ≃* Sporadic.Mathieu.M22)) : IsQuasisimple A := by
  let := Sporadic.Mathieu.m22_isSimpleGroup
  let : IsSimpleGroup A := h.some.isSimpleGroup
  exact quasisimple_of_perfect_simple

/-- The actual M₂₄ model is quasisimple when perfect. -/
theorem m24_quasisimple [Group.IsPerfect A]
    (h : Nonempty (A ≃* Sporadic.Mathieu.M24)) : IsQuasisimple A := by
  let := Sporadic.Mathieu.m24_isSimpleGroup
  let : IsSimpleGroup A := h.some.isSimpleGroup
  exact quasisimple_of_perfect_simple

/-- The elementary binary extension kernels are two-groups. -/
theorem elementary_twoGroup {r : ℕ} (h : LocalModels.ElementaryModel 2 r A) :
    IsPGroup 2 A := by
  apply IsPGroup.of_card (n := r)
  rw [Nat.card_congr h.some.toEquiv]
  simp

/-- The extraspecial binary extension kernels are two-groups. -/
theorem extraspecial_twoGroup {r : ℕ} (h : LocalModels.ExtraspecialModel 2 r A) :
    IsPGroup 2 A := IsPGroup.of_card h.2

/-- The commuting cyclic-four central-product kernel is a two-group. -/
theorem cyclicFourProduct_twoGroup {r : ℕ} (h : LocalModels.CyclicFourCentralProduct r A) :
    IsPGroup 2 A := by
  obtain ⟨C, E, hC, hE, hgen, hcomm, _⟩ := h
  have hc : IsPGroup 2 C := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr hC.some.toEquiv]
    norm_num
  have he := extraspecial_twoGroup hE
  have hp := hc.to_sup_of_normal_right' he
    ((commutator_eq_bot_iff_le_centralizer.mp hcomm).trans (centralizer_le_normalizer _))
  rw [hgen] at hp
  exact hp.of_equiv topEquiv

/-- The homocyclic kernel of order 64 is a two-group. -/
theorem fourCube_twoGroup (h : Nonempty (A ≃* Multiplicative (Fin 3 → ZMod 4))) :
    IsPGroup 2 A := by
  apply IsPGroup.of_card (n := 6)
  rw [Nat.card_congr h.some.toEquiv]
  simp

/-- An extension of a quasisimple group by a two-group has quasisimple two-core quotient. -/
theorem extension_core_quasisimple [Finite A] [Group.IsPerfect A]
    {kernel quotient : GroupClass.{u}}
    (h : LocalModels.HasExtension A kernel quotient)
    (hk : ∀ (U : Type u) [Group U], kernel U → IsPGroup 2 U)
    (hq : ∀ (U : Type u) [Group U] [Group.IsPerfect U], quotient U → IsQuasisimple U) :
    IsQuasisimple (A ⧸ pCore 2 A) := by
  obtain ⟨D, _, hD, hQ⟩ := h
  have hker : IsPGroup 2 (QuotientGroup.mk' D).ker := by
    rw [QuotientGroup.ker_mk']
    exact hk D hD
  let := core_quasisimple (hq (A ⧸ D) hQ)
  exact IsQuasisimple.of_mulEquiv
    (coreQuotientEquiv (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D) hker).symm
end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.Alternatives
