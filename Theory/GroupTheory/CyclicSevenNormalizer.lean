module
public import Mathlib.GroupTheory.SchurZassenhaus
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.Tactic

/-!
# The self-centralizing order-seven normalizer

An order-seven subgroup of relative index two in its normalizer has
normalizer order 14. Schur--Zassenhaus splits its normalizer as the subgroup
semidirect a cyclic group of order two. Self-centralization makes the
complement action faithful. The isomorphism retains the actual inclusion
of the order-seven subgroup, so character restrictions can be transported.

Source: Fong (1967), printed p.75, citing Brauer (1942).
Adapted from `Theory.GroupTheory.CyclicThirteenNormalizer`,
whose source is Alperin--Brauer--Gorenstein, III.8, pp.116--117.
-/

public section
noncomputable section
namespace CyclicSevenNormalizer
variable {G : Type*} [Group G]
/-- The actual normalizer in the ambient group. -/
abbrev Normalizer (P : Subgroup G) := (Subgroup.normalizer (P : Set G))
/-- A fixed cyclic group of order two. -/
abbrev Two := Multiplicative (ZMod 2)
/-- The canonical inclusion into the normalizer. -/
abbrev inclusion (P : Subgroup G) : P →* Normalizer P :=
  Subgroup.inclusion P.le_normalizer

/-- The subgroup order and relative index determine the normalizer order. -/
theorem normalizer_card (P : Subgroup G) (hP : Nat.card P = 7)
    (hindex : P.relIndex (Subgroup.normalizer (P : Set G)) = 2) : Nat.card (Normalizer P) = 14 := by
  have h := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) P (Subgroup.normalizer (P : Set G))
    bot_le P.le_normalizer
  simpa [Subgroup.relIndex_bot_left, hP, hindex] using h.symm

/-- Split the actual normalizer, preserving its distinguished normal subgroup. -/
theorem exists_semidirect (P : Subgroup G) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = P)
    (hindex : P.relIndex (Subgroup.normalizer (P : Set G)) = 2) :
    ∃ (α : Two →* MulAut P) (e : P ⋊[α] Two ≃* Normalizer P),
      Function.Injective α ∧ ∀ p : P, e (SemidirectProduct.inl p) = inclusion P p := by
  classical
  let O := P.subgroupOf (Subgroup.normalizer (P : Set G))
  let eO : O ≃* P := Subgroup.subgroupOfEquivOfLe P.le_normalizer
  have hO : Nat.card O = 7 := (Nat.card_congr eO.toEquiv).trans hP
  have hi : O.index = 2 := hindex
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime
    (show Nat.Coprime (Nat.card O) O.index by rw [hO, hi]; decide)
  have hKcard : Nat.card K = 2 := hK.symm.index_eq_card.symm.trans hi
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  let : IsCyclic K := isCyclic_of_prime_card hKcard
  let eK : K ≃* Two := mulEquivOfCyclicCardEq
    (hKcard.trans (by simp [Two, Nat.card_eq_fintype_card]))
  let γ : K →* MulAut P := P.normalizerMonoidHom.comp K.subtype
  have hγ : Function.Injective γ := by
    apply (MonoidHom.ker_eq_bot_iff γ).mp
    apply bot_unique
    intro k hk
    have hkO : (k : Normalizer P) ∈ O := by
      have hh : (k : Normalizer P) ∈ P.normalizerMonoidHom.ker := hk
      rw [P.normalizerMonoidHom_ker, hC] at hh
      exact hh
    exact Subtype.ext (Subgroup.disjoint_def.mp hK.disjoint hkO k.property)
  let α := γ.comp eK.symm.toMonoidHom
  let γO : K →* MulAut O :=
    O.normalizerMonoidHom.comp (Subgroup.inclusion (O.normalizer_eq_top ▸ le_top))
  let f : O ⋊[γO] K ≃* P ⋊[α] Two :=
    SemidirectProduct.congr eO eK (by
      intro k
      ext p
      simp only [α, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, eK.symm_apply_apply]
      rfl)
  let e := f.symm.trans (SemidirectProduct.mulEquivSubgroup hK)
  refine ⟨α, e, hγ.comp eK.symm.injective, ?_⟩
  intro p
  apply Subtype.ext
  change ((eO.symm p : O) : Normalizer P).val * (eK.symm 1 : Normalizer P).val = _
  simp [eO, inclusion]
  rfl

/-- The abstract normalizer is the faithful semidirect product of the literal
cyclic groups C7 and C2. -/
theorem exists_cyclic_semidirect (P : Subgroup G) (hP : Nat.card P = 7)
    (hC : Subgroup.centralizer (P : Set G) = P)
    (hindex : P.relIndex (Normalizer P) = 2) :
    ∃ α : Two →* MulAut (Multiplicative (ZMod 7)),
      Function.Injective α ∧
        Nonempty (Normalizer P ≃* Multiplicative (ZMod 7) ⋊[α] Two) := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let eP : P ≃* Multiplicative (ZMod 7) :=
    mulEquivOfCyclicCardEq (hP.trans (by simp [Nat.card_eq_fintype_card]))
  obtain ⟨α, e, hα, _⟩ := exists_semidirect P hP hC hindex
  let β := (MulAut.congr eP).toMonoidHom.comp
    (α.comp (MulEquiv.refl Two).symm.toMonoidHom)
  refine ⟨β, (MulAut.congr eP).injective.comp
    (hα.comp (MulEquiv.refl Two).symm.injective), ?_⟩
  exact ⟨e.symm.trans (SemidirectProduct.congr' eP (MulEquiv.refl Two))⟩

end CyclicSevenNormalizer
