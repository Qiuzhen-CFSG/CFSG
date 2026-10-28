module
public import CFSG.Quasithin.ChapterD.Section02.CyclicSource.ElementaryNineCore
public import CFSG.Quasithin.ChapterD.Section02.FittingOffenders.NineSupport
/-!
# Reducibility of the inverted elementary-nine endpoint

Each of the two cubic moved planes is stabilized by the nine-kernel and
by its inverting involution. It is therefore a proper nonzero invariant
subspace of the original order-eighteen endpoint. This distinguishes that
endpoint from its irreducible ambient extension in 15.1.2(5), printed p.1086.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.CyclicSource
universe u
variable {G V : Type u} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] {ρ : Representation (ZMod 2) G V}
set_option synthInstance.maxSize 10000

theorem LocalGeneration.not_irreducible_of_elementary_nine
    (l : LocalGeneration ρ) (hf : Function.Injective ρ) :
    letI := BinaryGroupAction.action ρ
    letI : Finite V := Module.finite_of_finite (ZMod 2)
    letI : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
    letI := l.normal
    Section02.ElementaryNineEndpoint (V := Multiplicative V) l.kernel l.involution →
    ¬ IsIrreducible ρ := by
  let := BinaryGroupAction.action ρ
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : IsElementaryAbelian 2 (Multiplicative V) := BinaryGroupAction.elementary
  let := l.normal
  intro h9 hi
  let := h9.kernel_elementary
  have hdim : Module.finrank (ZMod 2) V = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have hc : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
    exact hc.symm.trans ((Nat.card_congr (Multiplicative.toAdd (α := V))).symm.trans h9.card_module)
  obtain ⟨d⟩ := FittingConfigurations.supportFactors_of_nine_four_moved
    ρ hf l.kernel h9.card_kernel hdim l.moved
  let A := d.ambient 0
  have hAR : A ≤ l.kernel := map_subtype_le _
  let : CommGroup l.kernel := IsMulCommutative.instCommGroup
  have hRN : l.kernel ≤ normalizer (A : Set G) := by
    change l.kernel ≤ normalizer ((d.factor 0).map l.kernel.subtype : Set G)
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype]
      using (d.factor 0).le_normalizer_map l.kernel.subtype
  have htN : l.involution ∈ normalizer (A : Set G) := by
    apply mem_normalizer_iff.mpr
    intro a
    constructor
    · intro ha
      rw [h9.inverts ⟨a,hAR ha⟩]
      exact A.inv_mem ha
    · intro ha
      have htR : l.involution ∈ normalizer (l.kernel : Set G) := le_normalizer_of_normal (mem_top _)
      have haR : a ∈ l.kernel := (mem_normalizer_iff.mp htR a).mpr (hAR ha)
      rw [h9.inverts ⟨a,haR⟩] at ha
      exact A.inv_mem_iff.mp ha
  have hN : (⊤ : Subgroup G) ≤ normalizer (A : Set G) := by
    rw [←l.generated]
    exact sup_le hRN (zpowers_le.mpr htN)
  let C : Subrepresentation ρ := ⟨subspaceCommutator ρ ⊤ A,by
    intro g v hv
    exact (subspaceCommutator_invariant_normalizer ρ
      (le_subspaceStabilizer ρ ⊤ (by simp)) hN (mem_top g) v).2 hv⟩
  have hd : Module.finrank (ZMod 2) C.toSubmodule = 2 := d.support_dim 0
  let := hi
  rcases eq_bot_or_eq_top C with h | h
  · have hz : C.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    rw [hz] at hd
    simp at hd
  · have hz : C.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule h
    rw [hz,finrank_top,hdim] at hd
    omega
end CFSG.Quasithin.ChapterD.CyclicSource
