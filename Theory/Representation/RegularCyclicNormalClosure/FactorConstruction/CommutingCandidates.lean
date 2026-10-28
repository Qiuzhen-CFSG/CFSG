module

public import Theory.Representation.RegularCyclicNormalClosure.FactorConstruction.LocalCandidate
public import Theory.SpecificGroups.Frobenius21.BinaryOvergroups

/-!
# Cross-fixation for commuting exceptional factors

The restriction of an exceptional factor to its moved space is faithful.
Its order-twenty-one image is self-normalizing in the actual binary GL3,
so the centralizer is its center, which is trivial. Thus an actor commuting
with the factor fixes its moved space. Applying this to a conjugate gives
the exact cross-fixation clause required by FactorSeed.

The remaining hypothesis that distinct exceptional conjugates commute is
explicit; it is not proved here. This is the compatibility reduction for
Aschbacher–Smith E.6.24, printed p.255, using the existing binary-normalizer
calculation supporting E.6.25.
-/

public section

open Module Subgroup Representation.BinaryOffender
namespace Representation.RegularCyclicNormalClosure.FactorConstruction

private theorem model_center : ∀ z : Frobenius21.Model,
    (∀ x : Frobenius21.Model, x * z = z * x) → z = 1 := by decide +kernel

/-- A nonabelian group of order twenty-one has trivial center. -/
theorem central_eq_one_of_card_twenty_one {G : Type*} [Group G] [Finite G]
    (hcard : Nat.card G = 21) (hnab : ¬ ∀ x y : G, x * y = y * x)
    (z : G) (hz : ∀ x : G, x * z = z * x) : z = 1 := by
  obtain ⟨e⟩ := Frobenius21.nonempty_mulEquiv_of_card_eq hcard hnab
  apply e.injective
  rw [map_one]
  apply model_center
  intro x
  simpa only [map_mul, e.apply_symm_apply] using congrArg e (hz (e.symm x))

variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) A W}

/-- An actor centralizing a nonabelian order-twenty-one factor fixes that
factor's three-dimensional moved space pointwise. The faithful restriction
is self-normalizing in the actual binary general linear group. -/
theorem fixes_moved_of_centralizes_exceptional
    (hfaith : Function.Injective ρ) (B : Subgroup A)
    (hsplit : IsCompl (fixedSpace ρ B) (displacementSpan ρ B ⊤))
    (hcard : Nat.card B = 21) (hnab : ¬ ∀ x y : B, x * y = y * x)
    (hdim : finrank (ZMod 2) (displacementSpan ρ B ⊤) = 3)
    (d : A) (hd : ∀ b ∈ B, Commute b d) :
    ∀ v ∈ displacementSpan ρ B ⊤, ρ d v = v := by
  let S := displacementSpan ρ B ⊤
  let N := normalizer (B : Set A)
  let τ : Representation (ZMod 2) N S :=
    Representation.subrepresentation (ρ.comp N.subtype) S (by
      intro n v hv
      change ρ (n : A) v ∈ S
      have hm := displacementSpan_map_of_normalized ρ B n
        (mem_normalizer_iff_map_conj_eq.mp n.property)
      change S.map (ρ (n : A)) = S at hm
      rw [← hm]
      exact Submodule.mem_map_of_mem hv)
  let μ : B →* LinearMap.GeneralLinearGroup (ZMod 2) S :=
    τ.asGroupHom.comp (Subgroup.inclusion B.le_normalizer)
  have hμ : Function.Injective μ := by
    apply (injective_iff_map_eq_one μ).mpr
    intro b hb
    apply Subtype.ext
    apply hfaith
    ext v
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fixedSpace ρ B ⊔ S by rw [hsplit.sup_eq_top]; trivial)
    have he := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) S =>
      ((g : Module.End (ZMod 2) S) ⟨w, hw⟩ : S)) hb
    have he' := congrArg Subtype.val he
    change ρ (b : A) w = w at he'
    simp only [Subgroup.coe_one, map_one, Module.End.one_apply, map_add, show ρ (b : A) u = u from hu b, he']
  have hμcard : Nat.card μ.range = 21 :=
    (Nat.card_congr (Equiv.ofInjective μ hμ)).symm.trans hcard
  have hdN : d ∈ N := centralizer_le_normalizer (B : Set A)
    (mem_centralizer_iff.mpr (fun b hb => (hd b hb).eq))
  let δ := τ.asGroupHom ⟨d, hdN⟩
  have hcomm (b : B) : Commute (μ b) δ := by
    have he : Commute (Subgroup.inclusion B.le_normalizer b : N) ⟨d, hdN⟩ := by
      change (Subgroup.inclusion B.le_normalizer b : N) * ⟨d, hdN⟩ =
        ⟨d, hdN⟩ * (Subgroup.inclusion B.le_normalizer b : N)
      exact Subtype.ext (hd b b.property).eq
    exact he.map τ.asGroupHom
  have hδcent : δ ∈ centralizer (μ.range : Set _) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨b, rfl⟩
    exact (hcomm b).eq
  have hδ : δ ∈ μ.range := by
    rw [← Frobenius21.binary_normalizer_of_card S hdim μ.range hμcard]
    exact centralizer_le_normalizer _ hδcent
  obtain ⟨b, hb⟩ := hδ
  have hb1 : b = 1 := central_eq_one_of_card_twenty_one hcard hnab b (by
    intro c
    apply hμ
    simpa only [map_mul, hb] using (hcomm c).eq)
  have hδ1 : δ = 1 := by rw [← hb, hb1, map_one]
  intro v hv
  have he := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) S =>
    ((g : Module.End (ZMod 2) S) ⟨v, hv⟩ : S)) hδ1
  exact congrArg Subtype.val he

end Representation.RegularCyclicNormalClosure.FactorConstruction

namespace Representation.RegularCyclicNormalClosure
open FactorConstruction
variable {A W : Type*} [Group A] [Finite A] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W] {ρ : Representation (ZMod 2) A W} {C B : Subgroup A}

/-- Commuting exceptional candidates automatically satisfy the required
cross-fixation in the original ambient representation. -/
theorem ExceptionalCandidate.cross_fixed_of_commuting_conjugate
    (h : ExceptionalCandidate ρ C B) (hfaith : Function.Injective ρ) (a : A)
    (hcomm : ∀ b ∈ B, ∀ d ∈ B.map (MulAut.conj a).toMonoidHom, Commute b d) :
    ∀ b ∈ B, ∀ v ∈ displacementSpan ρ (B.map (MulAut.conj a).toMonoidHom) ⊤,
      ρ b v = v := by
  let D := B.map (MulAut.conj a).toMonoidHom
  have hDcard : Nat.card D = 21 :=
    (Subgroup.card_map_of_injective (MulAut.conj a).injective).trans h.factor_card
  have hDodd : Odd (Nat.card D) := by rw [hDcard]; decide
  have hDsplit : IsCompl (fixedSpace ρ D) (displacementSpan ρ D ⊤) :=
    GoldschmidtONan.isCompl_fixed_moved_of_odd hDodd
  have hDnab : ¬ ∀ x y : D, x * y = y * x := by
    intro hc
    apply h.nonabelian
    intro x y
    let e := (MulAut.conj a).subgroupMap B
    apply e.injective
    exact (map_mul e x y).trans ((hc (e x) (e y)).trans (map_mul e y x).symm)
  have hDdim : finrank (ZMod 2) (displacementSpan ρ D ⊤) = 3 := by
    have he := displacementSpan_conjugate ρ B ⊤ a
    rw [map_top_action] at he
    change finrank (ZMod 2) (displacementSpan ρ (B.map (MulAut.conj a).toMonoidHom) ⊤) = 3
    rw [he, ← (Submodule.equivMapOfInjective (ρ a) (ρ.apply_bijective a).injective
      (displacementSpan ρ B ⊤)).finrank_eq]
    exact h.moved_dimension
  intro b hb
  exact fixes_moved_of_centralizes_exceptional hfaith D hDsplit hDcard hDnab hDdim b
    (fun d hd => (hcomm b hb d hd).symm)

/-- The exceptional local candidate becomes a full seed once its distinct
actual conjugates are proved to commute. This remaining global condition
is not asserted here. -/
theorem ExceptionalCandidate.factorSeed_of_commuting_conjugates
    (h : ExceptionalCandidate ρ C B) (hfaith : Function.Injective ρ)
    (hcomm : ∀ a : A, B.map (MulAut.conj a).toMonoidHom ≠ B →
      ∀ b ∈ B, ∀ d ∈ B.map (MulAut.conj a).toMonoidHom, Commute b d) :
    FactorSeed ρ C B where
  contained := h.contained
  in_normalClosure := h.in_normalClosure
  split := h.split
  cross_fixed := fun a ha => h.cross_fixed_of_commuting_conjugate hfaith a (hcomm a ha)
  alternatives := Or.inr ⟨h.cyclic_card, h.factor_card, h.nonabelian, h.moved_dimension⟩

end Representation.RegularCyclicNormalClosure
