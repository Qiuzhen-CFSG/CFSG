module

public import Theory.GroupAction.C4SquareMaximalTwoAction
public import Theory.GroupTheory.PGroup.C4SquareSelfCentralizing

/-!
# Involution lifts in maximal C₄-square extensions

When conjugation on a normal self-centralizing C₄-square has image of order
32, its central transvection has an involution lift. Start with any lift x.
The lifts of two commuting base automorphisms have conjugation differences
in the abelian base. Comparing their action on x shows that its square
satisfies the finite obstruction certificate in `C4SquareMaximalTwoAction`.
Consequently x² has square one. The norm map of the transvection covers all
such base elements, so multiplying x by a base element makes its square one.

The extension identities are proved in an arbitrary group with abelian kernel;
no splitting or classification theorem is assumed. This is the maximal-action
case needed in Janko–Thompson, Math. Z. 113 (1970), 1.4, printed p.386.
-/

namespace C4SquareExtension
open Subgroup

-- An extension with an abelian kernel, written in kernel coordinates.
private theorem square_of_displacement {P V : Type*} [Group P] [CommGroup V]
    (τ : V →* P) (F : P →* MulAut V)
    (hact : ∀ g v, τ (F g v) = g * τ v * g⁻¹)
    (x : P) (s d : V) (hs : τ s = x ^ 2) :
    (τ d * x) ^ 2 = τ (d * F x d * s) := by
  rw [map_mul, map_mul, hact, hs]
  simp only [pow_two]
  group

private theorem displacement_equation {P V : Type*} [Group P] [CommGroup V]
    (τ : V →* P) (hτ : Function.Injective τ) (F : P →* MulAut V)
    (hact : ∀ g v, τ (F g v) = g * τ v * g⁻¹)
    (x y : P) (s d : V) (hs : τ s = x ^ 2)
    (hd : τ d = y * x * y⁻¹ * x⁻¹) :
    F y s = d * F x d * s := by
  apply hτ
  rw [← square_of_displacement τ F hact x s d hs, hact, hs, hd]
  simp only [pow_two]
  group

private theorem commuting_displacements {P V : Type*} [Group P] [CommGroup V]
    (τ : V →* P) (hτ : Function.Injective τ) (F : P →* MulAut V)
    (hact : ∀ g v, τ (F g v) = g * τ v * g⁻¹)
    (x y t : P) (d e k : V)
    (hd : τ d = y * x * y⁻¹ * x⁻¹)
    (he : τ e = t * x * t⁻¹ * x⁻¹)
    (hk : τ k = y * t * (t * y)⁻¹) :
    F y e * d = F t d * e * (k * (F x k)⁻¹) := by
  apply hτ
  have hcomm : τ k * τ (F t d * e) = τ (F t d * e) * τ k := by
    rw [← map_mul, ← map_mul, mul_comm k]
  calc
    τ (F y e * d) = τ k * τ (F t d * e) * x * (τ k)⁻¹ * x⁻¹ := by
      simp only [map_mul, hact, hd, he, hk]
      group
    _ = τ (F t d * e) * (τ k * (x * τ k * x⁻¹)⁻¹) := by
      rw [hcomm]
      group
    _ = τ (F t d * e * (k * (F x k)⁻¹)) := by
      simp only [map_mul, map_inv, hact]

/-- An elementary kernel-coordinate certificate forces an involution lift. -/
private theorem lift_from_obstruction {P V : Type*} [Group P] [CommGroup V]
    (τ : V →* P) (hτ : Function.Injective τ) (F : P →* MulAut V)
    (hker : F.ker = τ.range)
    (hact : ∀ g v, τ (F g v) = g * τ v * g⁻¹)
    (a b c : MulAut V) (z : V)
    (ha : a ∈ F.range) (hb : b ∈ F.range) (hc : c ∈ F.range)
    (ha2 : a ^ 2 = 1) (hcentral : ∀ g, Commute (F g) a)
    (hbc : Commute b c)
    (hdisp : ∀ v : V, v * (a v)⁻¹ = 1 ∨ v * (a v)⁻¹ = z)
    (hnorm : ∀ v : V, v ^ 2 = 1 → ∃ d : V, d * a d = v)
    (hobs : ∀ s d e : V, a s = s → b s = d * a d * s → c s = e * a e * s →
      (b e * d = c d * e ∨ b e * d = c d * e * z) → s ^ 2 = 1) :
    ∃ x : P, x ^ 2 = 1 ∧ F x = a := by
  obtain ⟨x, hx⟩ := ha
  obtain ⟨y, hy⟩ := hb
  obtain ⟨t, ht⟩ := hc
  have hsD : x ^ 2 ∈ τ.range := by
    rw [← hker, MonoidHom.mem_ker]
    rw [map_pow, hx, ha2]
  obtain ⟨s, hs⟩ := hsD
  have diff (g : P) : g * x * g⁻¹ * x⁻¹ ∈ τ.range := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hx]
    rw [(hcentral g).eq]
    group
  obtain ⟨d, hd⟩ := diff y
  obtain ⟨e, he⟩ := diff t
  have hkD : y * t * (t * y)⁻¹ ∈ τ.range := by
    rw [← hker, MonoidHom.mem_ker]
    simp only [map_mul, map_inv, hy, ht]
    rw [hbc.eq]
    group
  obtain ⟨k, hk⟩ := hkD
  have has : a s = s := by
    apply hτ
    rw [← hx, hact, hs]
    simp only [pow_two]
    group
  have hbs : b s = d * a d * s := by
    rw [← hy, ← hx]
    exact displacement_equation τ hτ F hact x y s d hs hd
  have hcs : c s = e * a e * s := by
    rw [← ht, ← hx]
    exact displacement_equation τ hτ F hact x t s e hs he
  have heq : b e * d = c d * e * (k * (a k)⁻¹) := by
    rw [← hy, ← ht, ← hx]
    exact commuting_displacements τ hτ F hact x y t d e k hd he hk
  have hcases : b e * d = c d * e ∨ b e * d = c d * e * z := by
    rcases hdisp k with h | h
    · left
      simpa only [h, mul_one] using heq
    · right
      simpa only [h] using heq
  have hs2 := hobs s d e has hbs hcs hcases
  obtain ⟨v, hv⟩ := hnorm s⁻¹ (by rw [inv_pow, hs2, inv_one])
  refine ⟨τ v * x, ?_, ?_⟩
  · rw [square_of_displacement τ F hact x s v hs, hx, hv, inv_mul_cancel, map_one]
  · rw [map_mul, hx]
    have hvk : τ v ∈ F.ker := by rw [hker]; exact ⟨v, rfl⟩
    rw [MonoidHom.mem_ker.mp hvk, one_mul]


/-- The central transvection of a maximal two-action has an involution lift. -/
public theorem exists_involution_central_binary_action {P : Type*} [Group P]
    (hP : IsPGroup 2 P) (D : Subgroup P) [D.Normal] [IsMulCommutative D]
    (hDC : centralizer (D : Set P) ≤ D)
    (model : Nonempty (D ≃* Model))
    (hc : Nat.card (MulAut.conjNormal : P →* MulAut D).range = 32) :
    ∃ x : P, x ^ 2 = 1 ∧ x ∉ D ∧
      (∀ d : D, d ^ 2 = 1 → MulAut.conjNormal (H := D) x d = d) ∧
      (∀ g : P, Commute (MulAut.conjNormal (H := D) g) (MulAut.conjNormal (H := D) x)) ∧
      (∀ d : D, MulAut.conjNormal (H := D) x d = d⁻¹ → d ^ 2 = 1) := by
  obtain ⟨e⟩ := model
  let τ : Model →* P := D.subtype.comp e.symm.toMonoidHom
  let F : P →* MulAut Model :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal : P →* MulAut D)
  have hτ : Function.Injective τ := D.subtype_injective.comp e.symm.injective
  have hrange : τ.range = D := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩
      exact (e.symm v).property
    · intro hx
      refine ⟨e ⟨x, hx⟩, ?_⟩
      change (e.symm (e ⟨x, hx⟩) : P) = x
      rw [e.symm_apply_apply]
  have hkerD : F.ker = D := by
    rw [show F = (MulAut.congr e).toMonoidHom.comp
      (MulAut.conjNormal : P →* MulAut D) from rfl,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e).injective,
      conjNormal_ker_eq_of_selfCentralizing_abelian D hDC]
  have hker : F.ker = τ.range := hkerD.trans hrange.symm
  have hact (g : P) (v : Model) : τ (F g v) = g * τ v * g⁻¹ := by
    change (e.symm (e (MulAut.conjNormal g (e.symm v))) : P) = g * τ v * g⁻¹
    rw [e.symm_apply_apply]
    rfl
  have hFc : Nat.card F.range = 32 := by
    rw [← index_ker, hkerD]
    rw [← index_ker, conjNormal_ker_eq_of_selfCentralizing_abelian D hDC] at hc
    exact hc
  have hFp : IsPGroup 2 F.range :=
    hP.of_surjective F.rangeRestrict F.rangeRestrict_surjective
  obtain ⟨a, b, c, z, ha, hb, hc', hne, ha2, hfix, hcent, hinv, hbc, hdisp, hnorm, hobs⟩ :=
    model_exists_lift_obstruction F.range hFp hFc
  obtain ⟨x, hx2, hx⟩ := lift_from_obstruction τ hτ F hker hact a b c z ha hb hc'
    ha2 (fun g => hcent _ ⟨g, rfl⟩) hbc hdisp hnorm hobs
  refine ⟨x, hx2, ?_, ?_, ?_, ?_⟩
  · intro hxd
    have hk : x ∈ F.ker := hkerD ▸ hxd
    exact hne (hx ▸ MonoidHom.mem_ker.mp hk)
  · intro d hd
    apply e.injective
    have hh := hfix (e d) (by rw [← map_pow, hd, map_one])
    rw [← hx] at hh
    simpa [F] using hh
  · intro g
    apply Commute.of_map (MulAut.congr e).injective
    change Commute (F g) (F x)
    rw [hx]
    exact hcent _ ⟨g, rfl⟩
  · intro d hd
    apply e.injective
    have hh : a (e d) = (e d)⁻¹ := by
      rw [← hx]
      simpa [F] using congrArg e hd
    simpa only [map_pow, map_one] using hinv (e d) hh

end C4SquareExtension
