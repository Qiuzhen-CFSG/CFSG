module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.Parity

/-!
# Choosing the swapping involution and its centralizer

An elementary actor outside the diagram kernel contains an actual swapping
involution. Outer reduction supplies its exact graph cocycle, and a separate
conditional theorem uses a genuine coboundary to obtain marked conjugacy.
No descent assertion is inferred from equality of outer classes.

For the source simple-socle extension, the two-core is trivial, so ambient
tau centralizes every element of the actor. Both the actor and its tau
therefore lie in the chosen involution centralizer. If that centralizer's
two-core is supported on the involution, a rank greater than one prevents
the actor from vanishing in its core quotient.

Source: Aschbacher--Smith E.1.1--2 and E.1.14(1), printed pp.209--210,214;
GLS3, Theorems 2.5.1 and 2.5.12(e), for the exceptional outer action.
-/

public section

open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
open DiagramAutomorphisms DiagramAutomorphisms.InvolutionNormalForms
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

omit [Finite G] in
/-- Choose an actual swapping involution from the given elementary actor.
Its induced action is an explicit cocycle twist of the exceptional graph power. -/
theorem exists_swapping_involution (L : Subgroup G) [L.Normal]
    (e : Sp F ≃* L) {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (hq : 2 < Nat.card F) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAH : ¬ A ≤ diagramKernel L e hq) :
    ∃ t ∈ A, t ∉ diagramKernel L e hq ∧ orderOf t = 2 ∧
      ∃ g : Sp F, extensionAction L e t =
        MulAut.conj g * ExceptionalGraph.graphAut ^ f ∧
        g * (ExceptionalGraph.graphAut ^ f) g = 1 := by
  obtain ⟨t, htA, htH⟩ := SetLike.not_le_iff_exists.mp hAH
  have htne : t ≠ 1 := by
    intro h
    exact htH (h ▸ (diagramKernel L e hq).one_mem)
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime_iff.mpr ⟨elemPow_eq_one_of_isElementaryAbelian t htA, htne⟩
  have hasq : (extensionAction L e t) ^ 2 = 1 := by
    rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian t htA, map_one]
  have hane : extensionAction L e t ≠ 1 := by
    intro h
    apply htH
    change (parabolicClassAction hq) (extensionAction L e t) = 1
    rw [h, map_one]
  refine ⟨t, htA, htH, htorder, ?_⟩
  rcases involution_inner_or_twist hF hf
      SemilinearClassification.inner_field_of_preservesDiagram _
      (orderOf_eq_prime_iff.mpr ⟨hasq, hane⟩) with hi | hg
  · obtain ⟨g, _, hg⟩ := hi
    exact (htH ((mem_diagramKernel_iff L e hq t).mpr
      (hg ▸ inner_preservesDiagram g))).elim
  · exact hg

omit [Finite G] in
/-- Descent is used only at its genuine missing equation; it is not inferred
from the outer coset. This supplies a marked conjugacy for the chosen actor. -/
theorem exists_normalized_swapping_involution (L : Subgroup G) [L.Normal]
    (e : Sp F ≃* L) {f : ℕ} (hF : Nat.card F = 2 ^ f) (hf : 1 < f)
    (hq : 2 < Nat.card F) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hAH : ¬ A ≤ diagramKernel L e hq)
    (hdescent : ∀ g : Sp F, g * (ExceptionalGraph.graphAut ^ f) g = 1 →
      ∃ h : Sp F, g = h * ((ExceptionalGraph.graphAut ^ f) h)⁻¹) :
    ∃ t ∈ A, t ∉ diagramKernel L e hq ∧ orderOf t = 2 ∧
      ∃ h : Sp F, extensionAction L e t =
        MulAut.conj h * ExceptionalGraph.graphAut ^ f * (MulAut.conj h)⁻¹ := by
  obtain ⟨t, htA, htH, htorder, g, hga, hgc⟩ :=
    exists_swapping_involution L e hF hf hq A hAH
  obtain ⟨h, hh⟩ := hdescent g hgc
  exact ⟨t, htA, htH, htorder, h, hga.trans (inner_twist_eq_conjugate _ g h hh)⟩

omit [Finite G] [Field F] [Finite F] [CharP F 2] in
/-- Every element of the elementary actor commutes with its chosen involution. -/
theorem actor_le_centralizer (A : Subgroup G) [IsElementaryAbelian 2 A]
    {t : G} (htA : t ∈ A) : A ≤ centralizer ({t} : Set G) := by
  intro a ha
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : A) ⟨t, htA⟩)

/-- Triviality of the ambient two-core makes tau centralize the chosen actor
literally, so it is contained in the candidate involution centralizer. -/
theorem tau_le_centralizer [IsSimpleGroup (generalizedFitting G)]
    (e : Sp F ≃* generalizedFitting G) (hq : 2 < Nat.card F)
    (T : Sylow 2 G) (hLT : generalizedFitting G ⊔ (T : Subgroup G) = ⊤)
    (A : Subgroup G) {t : G} (htA : t ∈ A) :
    tau (T : Subgroup G) A ≤ centralizer ({t} : Set G) := by
  have hcore := (SimpleSocle.structure_of_sylow_supplement
    (symplectic_socle_nonabelian e hq) T hLT).2.2.1
  intro x hx
  apply mem_centralizer_singleton_iff.mpr
  have hh := (mem_centralizerModulo_iff.mp hx).2 t htA
  rw [hcore, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hh
  exact hh.symm

omit [Field F] [Finite F] [CharP F 2] in
/-- A large elementary actor cannot be absorbed by a core supported on one
involution. The containment is in the intrinsic local subgroup carrier. -/
theorem actor_not_le_core_of_core_le_involution
    (A K : Subgroup G) [IsElementaryAbelian 2 A] (hAK : A ≤ K)
    {t : G} (htorder : orderOf t = 2) (hrank : 1 < Group.rank A)
    (hcore : pCore 2 K ≤ (zpowers t).subgroupOf K) :
    ¬ A.subgroupOf K ≤ pCore 2 K := by
  intro hA
  have hAz : A ≤ zpowers t := by
    intro a ha
    exact hcore (hA (show (⟨a, hAK ha⟩ : K) ∈ A.subgroupOf K from ha))
  have hc : Nat.card A ≤ 2 ^ 1 := by
    calc
      Nat.card A ≤ Nat.card (zpowers t) :=
        Nat.card_le_card_of_injective (inclusion hAz) (inclusion_injective hAz)
      _ = 2 ^ 1 := by rw [Nat.card_zpowers, htorder, pow_one]
  exact (Nat.not_le_of_gt hrank) (IsElementaryAbelian.rank_le_of_card_le A hc)

end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.SymplecticFour.Swapping.ExternalMembers
