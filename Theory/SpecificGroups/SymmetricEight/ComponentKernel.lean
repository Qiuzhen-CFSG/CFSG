module

public import Theory.SpecificGroups.SymmetricEight.ComponentMarking
public import Theory.SpecificGroups.SymmetricEight.EvenPairCentralizer
public import Mathlib.GroupTheory.Index

/-!
# The A₆-fixing actor kernel on an A₈ component

A proper component of order 360 in the fixed subgroup of an involution of A₈
has the compatible six-point marking. Thus its full automorphism fixer has
order at most two. A group of normalizing actors centralizing this component
has centralizer kernel of index two as soon as one actor acts nontrivially.

Source: Aschbacher–Smith, 2.5.19, printed pp.561–563, the A₈ case of the
index-two centralizer kernel in the proof of the first claim.
-/

public noncomputable section
open Subgroup Equiv Theory.GroupTheory
namespace Theory.SpecificGroups.SymmetricEight.ComponentKernel
variable {G : Type*} [Group G] {X K R : Subgroup G} {t : G}

/-- The full fixer of the literal A₆ component of an A₈ involution centralizer. -/
theorem component_fixer_card_le_two (eX : X ≃* alternatingGroup (Fin 8))
    (htN : t ∈ normalizer (X : Set G)) (ht : orderOf t = 2)
    (hKX : K < X) (hK : IsComponentIn K (X ⊓ centralizer ({t} : Set G)))
    (hcard : Nat.card K = 360) :
    Nat.card (fixingSubgroup (MulAut X) (K.subgroupOf X : Set X)) ≤ 2 := by
  obtain ⟨f, _, hX, hL⟩ := ComponentMarking.exists_marked_equiv eX htN ht hKX hK hcard
  let e : X ≃* alternatingGroup (Fin 8) :=
    ((subgroupOfEquivOfLe (le_sup_left : X ≤ X ⊔ zpowers t)).symm.trans
      (f.subgroupMap (X.subgroupOf (X ⊔ zpowers t)))).trans (MulEquiv.subgroupCongr hX)
  have hmap : (K.subgroupOf X).map
      ((alternatingGroup (Fin 8)).subtype.comp e.toMonoidHom) =
      EvenPairCentralizer.evenPair := by
    change _ = alternatingGroup (Fin 8) ⊓ _
    rw [← hL]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, mem_sup_left x.property⟩, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hKX.le hx⟩, hx, rfl⟩
  exact EvenPairCentralizer.automorphismFixer_card_le_two e (K.subgroupOf X) hmap

/-- Pointwise fixing actors have exactly two cosets of the literal centralizer
kernel when their action contains a nontrivial actor. -/
theorem actor_centralizer_index_two [Finite G]
    (hRN : R ≤ normalizer (X : Set G)) (hRC : R ≤ centralizer (K : Set G))
    (hfix : Nat.card (fixingSubgroup (MulAut X) (K.subgroupOf X : Set X)) ≤ 2)
    (htR : t ∈ R) (htC : t ∉ centralizer (X : Set G)) :
    ((R ⊓ centralizer (X : Set G)).subgroupOf R).index = 2 := by
  let f : R →* MulAut X := X.normalizerMonoidHom.comp (inclusion hRN)
  have hker : f.ker = (R ⊓ centralizer (X : Set G)).subgroupOf R := by
    ext r
    change X.normalizerMonoidHom ⟨r, hRN r.property⟩ = 1 ↔ _
    change (⟨r, hRN r.property⟩ : normalizer (X : Set G)) ∈ X.normalizerMonoidHom.ker ↔ _
    rw [normalizerMonoidHom_ker]
    exact ⟨fun h => ⟨r.property, h⟩, fun h => h.2⟩
  have hfixing : f.range ≤ fixingSubgroup (MulAut X) (K.subgroupOf X : Set X) := by
    rintro _ ⟨r, rfl⟩ k
    apply Subtype.ext
    change (r : G) * (k.val : G) * (r : G)⁻¹ = (k.val : G)
    rw [← hRC r.property k.val k.property, mul_inv_cancel_right]
  have hupper : f.ker.index ≤ 2 := by
    rw [index_ker]
    exact (Nat.card_le_card_of_injective (inclusion hfixing)
      (inclusion_injective hfixing)).trans hfix
  have hproper : f.ker ≠ ⊤ := by
    intro he
    have hm : (⟨t,htR⟩ : R) ∈ f.ker := he ▸ mem_top _
    rw [hker] at hm
    exact htC hm.2
  have hlower := f.ker.one_lt_index_of_ne_top hproper
  rw [hker] at hupper hlower
  omega

end Theory.SpecificGroups.SymmetricEight.ComponentKernel
