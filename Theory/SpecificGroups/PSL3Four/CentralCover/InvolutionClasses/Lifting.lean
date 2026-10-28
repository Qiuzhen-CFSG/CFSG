module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InvolutionClasses.ProjectiveField
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.Geometry
public import Theory.GroupTheory.KleinFourKernelInvolutionFusion

/-!
# Lifting projective field-coset conjugacy to the perfect four-cover

Perfectness and the exact central kernel make the base's inner action
faithful. The projective cocycle calculation therefore gives the quotient
fusion premise for the actual overgroup conjugation map. Transport through
an automorphism of the projective group explicitly preserves that equation,
allowing the chosen field representative to use different coordinates.

The final step lifts the quotient conjugator through the Klein four kernel.
The nontrivial center action is supplied by `InvolutionClasses.CenterAction`.
Source: Aschbacher--Smith, proof of 15.3.38, printed p.1137,
combined manuscript of 1 March 2004.
-/

public section

namespace Matrix.PSL3Four.InvolutionClasses
open Subgroup

private theorem autMap_conj {E : Type*} [Group E] (c : FourCover E) (x : E) :
    c.toCover.autMap c.ker_eq_center (MulAut.conj x) = MulAut.conj (c.toMonoidHom x) := by
  ext y
  obtain ⟨z, rfl⟩ := c.surjective y
  rw [c.toCover.autMap_apply]
  change c.toMonoidHom (x * z * x⁻¹) = c.toMonoidHom x * c.toMonoidHom z * (c.toMonoidHom x)⁻¹
  simp only [map_mul, map_inv]

/-- Perfectness and the exact central kernel make inner automorphisms of the base faithful. -/
theorem projective_inner_injective {E : Type*} [Group E] (c : FourCover E) :
    Function.Injective (MulAut.conj : PSL →* MulAut PSL) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨z, rfl⟩ := c.surjective x
  have he : MulAut.conj z = 1 := by
    apply c.toCover.autMap_injective c.ker_eq_center
    rw [autMap_conj, map_one]
    exact hx
  have hz : z ∈ center E := by
    apply mem_center_iff.mpr
    intro a
    have h := DFunLike.congr_fun he a
    change z * a * z⁻¹ = a at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  exact (c.ker_eq_center.symm ▸ hz : z ∈ c.toMonoidHom.ker)

private theorem aut_conjugates_inner {B : Type*} [Group B] (a : MulAut B) (x : B) :
    a * MulAut.conj x * a⁻¹ = MulAut.conj (a x) := by
  ext y
  simp [MulAut.conj_apply]

private theorem inner_coset_fusion {B : Type*} [Group B]
    (hinj : Function.Injective (MulAut.conj : B →* MulAut B))
    (σ : MulAut B) (hσ : σ ^ 2 = 1)
    (hco : ∀ x : B, x * σ x = 1 → ∃ b : B, x = b * (σ b)⁻¹)
    (y : MulAut B) (hy : y ^ 2 = 1)
    (hyi : y * σ⁻¹ ∈ MulAut.innerSubgroup B) :
    ∃ b ∈ MulAut.innerSubgroup B, b * σ * b⁻¹ = y := by
  obtain ⟨x, hx⟩ := hyi
  have hyform : y = MulAut.conj x * σ := (eq_mul_inv_iff_mul_eq.mp hx).symm
  have hcomm : σ * MulAut.conj x = MulAut.conj (σ x) * σ :=
    mul_inv_eq_iff_eq_mul.mp (aut_conjugates_inner σ x)
  have hs : (MulAut.conj x * σ) ^ 2 = MulAut.conj (x * σ x) := by
    calc
      _ = MulAut.conj x * (σ * MulAut.conj x) * σ := by simp only [pow_two]; group
      _ = MulAut.conj x * (MulAut.conj (σ x) * σ) * σ := by rw [hcomm]
      _ = MulAut.conj (x * σ x) * σ ^ 2 := by rw [map_mul]; simp only [pow_two]; group
      _ = _ := by rw [hσ, mul_one]
  have hxx : x * σ x = 1 := by
    apply hinj
    rw [map_one, ← hs, ← hyform, hy]
  obtain ⟨b, hb⟩ := hco x hxx
  refine ⟨MulAut.conj b, ⟨b, rfl⟩, ?_⟩
  rw [hyform, hb, map_mul, map_inv, ← aut_conjugates_inner σ b]
  group

/-- Cocycle triviality is invariant under the actual change of projective coordinates. -/
theorem projective_coboundary_of_isConj (σ : MulAut PSL) (hσ : IsConj pslFrobenius σ)
    (x : PSL) (hx : x * σ x = 1) : ∃ b : PSL, x = b * (σ b)⁻¹ := by
  obtain ⟨a, ha⟩ := isConj_iff.mp hσ
  change a * pslFrobenius * a⁻¹ = σ at ha
  have hcompat (z : PSL) : σ (a z) = a (pslFrobenius z) := by
    rw [← ha]
    simp
  have hx' : a.symm x * pslFrobenius (a.symm x) = 1 := by
    apply a.injective
    rw [map_mul, map_one, a.apply_symm_apply, ← hcompat, a.apply_symm_apply, hx]
  obtain ⟨b, hb⟩ := projective_field_coboundary (a.symm x) hx'
  refine ⟨a b, ?_⟩
  have he := congrArg a hb
  rw [a.apply_symm_apply, map_mul, map_inv, ← hcompat] at he
  exact he

variable {I : Type*} [Group I] {L : Subgroup I} [L.Normal]
open ExtendedCentralizer

/-- Descent of an element of L is conjugation by its image under the same cover. -/
theorem projectiveAction_on_cover (c : FourCover L) (x : L) :
    projectiveAction L c (x : I) = MulAut.conj (c.toMonoidHom x) := by
  rw [projectiveAction, MonoidHom.comp_apply, MulAut.conjNormal_val]
  exact autMap_conj c x

/-- The quotient image of L is exactly the inner projective subgroup. -/
theorem projectiveAction_map_cover (c : FourCover L) :
    L.map (projectiveAction L c) = MulAut.innerSubgroup PSL := by
  ext a
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨c.toMonoidHom ⟨x,hx⟩, (projectiveAction_on_cover c ⟨x,hx⟩).symm⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨l, rfl⟩ := c.surjective x
    exact ⟨l, l.property, projectiveAction_on_cover c l⟩

/-- The precise quotient fusion premise for the actual projective-action map. -/
theorem projectiveAction_field_fusion (c : FourCover L) (f : I) (hf : f ^ 2 = 1)
    (hfield : IsConj pslFrobenius (projectiveAction L c f))
    (y : MulAut PSL) (hy : y ^ 2 = 1)
    (hyi : y * (projectiveAction L c f)⁻¹ ∈ L.map (projectiveAction L c)) :
    ∃ b ∈ L.map (projectiveAction L c), b * projectiveAction L c f * b⁻¹ = y := by
  rw [projectiveAction_map_cover] at hyi ⊢
  exact inner_coset_fusion (projective_inner_injective c) _
    (by rw [← map_pow, hf, map_one])
    (projective_coboundary_of_isConj _ hfield) y hy hyi

/-- The center action and projective calculation lift fusion with a conjugator in L. -/
theorem field_coset_conjugate (d : Overgroup L) (f : I) (hf : f ^ 2 = 1)
    (hfield : IsConj pslFrobenius (projectiveAction L d.cover f))
    (hcenter : ∃ z : center L, f * ((z : L) : I) * f⁻¹ ≠ ((z : L) : I))
    (x : I) (hx : x ^ 2 = 1) (hxL : x * f⁻¹ ∈ L) :
    ∃ b : L, (b : I) * f * (b : I)⁻¹ = x := by
  let q := projectiveAction L d.cover
  have hk : q.ker = (center L).map L.subtype := d.projectiveAction_ker
  let e : center L ≃* q.ker :=
    ((center L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr hk.symm)
  let : IsKleinFour (center L) := d.cover.center_isKleinFour
  let : IsKleinFour q.ker :=
    { card_four := (Nat.card_congr e.symm.toEquiv).trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv e.symm).trans IsKleinFour.exponent_two }
  have hact : ∃ z : q.ker, f * (z : I) * f⁻¹ ≠ (z : I) := by
    obtain ⟨z, hz⟩ := hcenter
    exact ⟨e z, hz⟩
  exact involution_coset_conjugate_of_kleinFour_kernel q L
    (by rw [hk]; exact map_subtype_le _) f hf hact
    (projectiveAction_field_fusion d.cover f hf hfield) x hx hxL

/-- The kernel of the actual projective action is a Klein four-group. -/
theorem projectiveAction_kernel_isKleinFour (d : Overgroup L) :
    IsKleinFour (projectiveAction L d.cover).ker := by
  let e : center L ≃* (projectiveAction L d.cover).ker :=
    ((center L).equivMapOfInjective L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr d.projectiveAction_ker.symm)
  let : IsKleinFour (center L) := d.cover.center_isKleinFour
  exact
    { card_four := (Nat.card_congr e.symm.toEquiv).trans IsKleinFour.card_four
      exponent_two := (Monoid.exponent_eq_of_mulEquiv e.symm).trans IsKleinFour.exponent_two }

/-- Nontrivial center action is nontrivial action on the same quotient kernel. -/
theorem projectiveAction_moves_kernel (d : Overgroup L) (f : I)
    (hcenter : ∃ z : center L, f * ((z : L) : I) * f⁻¹ ≠ ((z : L) : I)) :
    ∃ z : (projectiveAction L d.cover).ker, f * (z : I) * f⁻¹ ≠ (z : I) := by
  obtain ⟨z, hz⟩ := hcenter
  exact ⟨⟨((z : L) : I), by
    rw [d.projectiveAction_ker]
    exact mem_map_of_mem L.subtype z.property⟩, hz⟩

end Matrix.PSL3Four.InvolutionClasses
