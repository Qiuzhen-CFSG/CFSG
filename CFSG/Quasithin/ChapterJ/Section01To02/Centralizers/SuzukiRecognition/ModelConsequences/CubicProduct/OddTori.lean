module
public import CFSG.Quasithin.ChapterJ.Section01To02.Centralizers.SuzukiRecognition.ModelConsequences.CubicProduct
public import Theory.SpecificGroups.Suzuki.EightOuterTori.ModelTransport
public import Theory.GroupTheory.OddCentralizerProduct

/-!
# Odd tori in the local cubic extension

For the actual E₄ × Sz(8) base and its outer cubic supplement, conjugation
on the Suzuki factor realizes its full automorphism group. A torus fixer
acts innerly on that factor, so the outer-action hypothesis forces it into
the base. The intrinsic Suzuki centralizer then gives C_K(Y) = YE.
Every torus automorphism extends to the Suzuki factor and is therefore
realized by an element of the literal normalizer in K.

Source: Aschbacher–Smith, J.2.9–10, printed p.438 (PDF p.449),
refs/quasithin.pdf. The parent ModelConsequences module applies these
calculations to the original subgroups inside N_G(S₀).
-/

@[expose] public section
open Subgroup BenderSuzuki.MatrixGroups
namespace CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition.CubicProduct
variable {K : Type*} [Group K] [Finite K] (c : CubicProduct K)

omit [Finite K] in
private theorem inner_mem_base (x : K)
    (h : letI := c.normal_L
      ∃ l : c.L, MulAut.conjNormal x = MulAut.conj l) :
    x ∈ c.E ⊔ c.L := by
  let := c.normal_E
  let := c.normal_L
  let f : K →* MulAut c.L := MulAut.conjNormal
  let I := (MulAut.conj : c.L →* MulAut c.L).range
  have hE (e : K) (he : e ∈ c.E) : f e = 1 := by
    ext l
    change e * (l : K) * e⁻¹ = l
    rw [← c.central he l l.property, mul_inv_cancel_right]
  have hx : x ∈ (c.E ⊔ c.L) ⊔ c.B := by rw [c.generate]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_left.mp hx
  obtain ⟨e, he, l, hl, rfl⟩ := mem_sup_of_normal_left.mp ha
  have hfl : f l ∈ I := ⟨⟨l, hl⟩, MulAut.conjNormal_val.symm⟩
  have hfb : f b ∈ I := by
    have hxI : f (e * l * b) ∈ I := by
      obtain ⟨z, hz⟩ := h
      exact ⟨z, hz.symm⟩
    rw [map_mul, map_mul, hE e he, one_mul] at hxI
    exact (I.mul_mem_cancel_left hfl).mp hxI
  have hb1 : b = 1 := by
    by_contra hn
    obtain ⟨z, hz⟩ := hfb
    apply c.outer b hb hn
    refine ⟨z, z.property, ?_⟩
    intro y hy
    exact congrArg (fun α : MulAut c.L => (α ⟨y, hy⟩ : K)) hz.symm
  rw [hb1, mul_one]
  exact (c.E ⊔ c.L).mul_mem ((show c.E ≤ c.E ⊔ c.L from le_sup_left) he)
    ((show c.L ≤ c.E ⊔ c.L from le_sup_right) hl)

/-- The actual conjugation action on the Suzuki factor realizes every automorphism. -/
theorem factor_action_surjective :
    letI := c.normal_L
    Function.Surjective (MulAut.conjNormal : K →* MulAut c.L) := by
  let := c.normal_L
  let f : K →* MulAut c.L := MulAut.conjNormal
  let g := (MulAut.congr c.model).toMonoidHom.comp f
  have htop : g.range = ⊤ := by
    apply suzuki_eight_aut_subgroup_eq_top
    · rintro _ ⟨x, rfl⟩
      refine ⟨(c.model.symm x : K), ?_⟩
      change MulAut.congr c.model (MulAut.conjNormal (c.model.symm x : K)) = _
      rw [MulAut.conjNormal_val, MulAut.congr_conj, c.model.apply_symm_apply]
    · let : Nontrivial c.B := Finite.one_lt_card_iff_nontrivial.mp (by rw [c.card_B]; decide)
      obtain ⟨b, hb⟩ := exists_ne (1 : c.B)
      refine ⟨g b, ⟨b, rfl⟩, ?_⟩
      rintro ⟨x, hx⟩
      have hinner : ∃ l : c.L, f b = MulAut.conj l :=
        (MulAut.congr_inner_iff c.model (f b)).mp ⟨x, hx.symm⟩
      obtain ⟨l, hl⟩ := hinner
      apply c.outer b b.property (fun he => hb (Subtype.ext he))
      exact ⟨l, l.property, fun y hy =>
        congrArg (fun α : MulAut c.L => (α ⟨y, hy⟩ : K)) hl⟩
  intro α
  obtain ⟨x, hx⟩ := MonoidHom.range_eq_top.mp htop (MulAut.congr c.model α)
  exact ⟨x, (MulAut.congr c.model).injective hx⟩

/-- The literal image of an odd Suzuki Sylow subgroup has prime order. -/
theorem odd_sylow_image_card {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p c.L) :
    Nat.card ((Y : Subgroup c.L).map c.L.subtype) = p := by
  rw [card_map_of_injective c.L.subtype_injective]
  exact (suzuki_eight_sylow_odd_model c.model hp Y).1

/-- The cubic outer action leaves no extra elements in the odd-torus centralizer. -/
theorem odd_sylow_centralizer {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p c.L) :
    centralizer ((Y : Subgroup c.L).map c.L.subtype : Set K) =
      (Y : Subgroup c.L).map c.L.subtype ⊔ c.E := by
  let := c.normal_L
  have hle : centralizer ((Y : Subgroup c.L).map c.L.subtype : Set K) ≤ c.E ⊔ c.L := by
    intro x hx
    apply c.inner_mem_base x
    obtain ⟨y, hy⟩ := suzuki_eight_sylow_odd_fixing_inner_model c.model hp Y (MulAut.conjNormal x) (by
      intro y
      apply Subtype.ext
      change x * (y.val : K) * x⁻¹ = y.val
      rw [← mem_centralizer_iff.mp hx y.val ⟨y.val, y.property, rfl⟩,
        mul_inv_cancel_right])
    exact ⟨y.val, hy⟩
  rw [← inf_eq_left.mpr hle]
  exact centralizer_inf_commuting_product c.E c.L Y c.central
    (suzuki_eight_sylow_odd_model c.model hp Y).2

/-- Every automorphism of the literal odd-torus image is induced by its normalizer in K. -/
theorem odd_sylow_normalizer_surjective {p : ℕ} [Fact p.Prime]
    (hp : p = 7 ∨ p = 13) (Y : Sylow p c.L) :
    Function.Surjective ((Y : Subgroup c.L).map c.L.subtype).normalizerMonoidHom := by
  let := c.normal_L
  let U := (Y : Subgroup c.L).map c.L.subtype
  let e : Y ≃* U := (Y : Subgroup c.L).equivMapOfInjective c.L.subtype c.L.subtype_injective
  intro β
  obtain ⟨α, hα⟩ := suzuki_eight_sylow_odd_aut_extend_model c.model hp Y (MulAut.congr e.symm β)
  obtain ⟨x, hx⟩ := c.factor_action_surjective α
  have hact (y : U) : x * (y : K) * x⁻¹ = β y := by
    obtain ⟨z, rfl⟩ := e.surjective y
    have he := congrArg (fun w : c.L => (w : K)) (hα z)
    rw [← hx] at he
    change x * ((e z : U) : K) * x⁻¹ = ((e (e.symm (β (e z))) : U) : K) at he
    simpa only [e.apply_symm_apply] using he
  have hnorm : x ∈ normalizer (U : Set K) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      change x * y * x⁻¹ ∈ U
      rw [hact ⟨y, hy⟩]
      exact (β ⟨y, hy⟩).property
    · exact le_of_eq (card_map_of_injective (K := U) (MulAut.conj x).injective).symm
  refine ⟨⟨x, hnorm⟩, ?_⟩
  ext y
  exact hact y

end CFSG.Quasithin.ChapterJ.Centralizers.SuzukiRecognition.CubicProduct
