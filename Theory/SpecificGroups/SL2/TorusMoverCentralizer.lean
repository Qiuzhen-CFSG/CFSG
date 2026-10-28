module
public import Theory.SpecificGroups.SL2.SylowTorusAutomorphisms
public import Theory.SpecificGroups.SL2.OddBorelMarking

/-!
# Rigidity of an automorphism fixing a full split torus

In characteristic two, an automorphism preserving a Sylow subgroup and
fixing its full split torus pointwise is conjugation by a diagonal element.
Fixing one element outside the Sylow normalizer then makes that diagonal
element trivial. The arbitrary-Sylow theorem transports the same argument
through simultaneous Sylow and odd-torus coordinates.

Source: the automorphism step in DGS, *Groups and Graphs* (1985),
(10.8), printed p.160; the underlying semilinear classification is imported.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
open BenderSuzuki.ZD.Linear
namespace Matrix.SpecialLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
local notation "diag" => fun z : Fˣ => diag2 (z:F) (Units.ne_zero z)

/-- Fixing the full split torus pointwise removes the field component. -/
theorem sylow_preserving_diagonal_fixed_inner (hF : 2 < Nat.card F)
    (α : MulAut SL(2,F))
    (hU : (upperUnipotent F).map α.toMonoidHom = upperUnipotent F)
    (hD : ∀ z : Fˣ, α (diag z) = diag z) :
    ∃ d : Fˣ, α = MulAut.conj (diag d) := by
  obtain ⟨d,σ,hα⟩ := sylow_torus_preserving_semilinear hF α hU
    (fun z => ⟨z,hD z⟩)
  have hσ : σ = 1 := by
    ext x
    by_cases hx : x = 0
    · simp [hx]
    · have hh := hD (Units.mk0 x hx)
      rw [hα,diagonal_field_apply_diagonal] at hh
      have he := congrArg (fun g : SL(2,F) => g.val 0 0) hh
      simpa [diag2_coe'] using he
  refine ⟨d,?_⟩
  rw [hα,hσ]
  have hfield : sl2FieldAut (1 : F ≃+* F) = 1 := by
    ext g i j
    rfl
  rw [hfield,mul_one]

/-- Fixing the full torus and one nontrivial standard root element kills
the remaining diagonal inner automorphism. -/
theorem sylow_torus_and_root_fixed_eq_one (hF : 2 < Nat.card F)
    (α : MulAut SL(2,F))
    (hU : (upperUnipotent F).map α.toMonoidHom = upperUnipotent F)
    (hD : ∀ z : Fˣ, α (diag z) = diag z)
    (hroot : α (transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (1:F)) =
      transvection zero_ne_one (1:F)) : α = 1 := by
  obtain ⟨d,rfl⟩ := sylow_preserving_diagonal_fixed_inner hF α hU hD
  have hc : diag d * transvection zero_ne_one (1:F) =
      transvection zero_ne_one (1:F) * diag d := mul_inv_eq_iff_eq_mul.mp hroot
  have he := congrArg (fun g : SL(2,F) => g.val 0 1) hc
  have hinv : (d:F) = (d:F)⁻¹ := by
    simpa [mul_apply,Fin.sum_univ_two,diag2_coe',transvection_coe] using he
  have hs : (d:F)^2 = 1 := by
    calc (d:F)^2 = (d:F) * (d:F)⁻¹ := by rw [pow_two,←hinv]
         _ = 1 := mul_inv_cancel₀ d.ne_zero
  have hd1 : d = 1 := Units.ext (by
    change (d:F) = 1
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h)
  subst d
  have he1 : diag (1:Fˣ) = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe']
  rw [he1,map_one]

/-- A Sylow-preserving automorphism fixing the full split torus and an
element outside the Sylow normalizer is trivial. -/
theorem sylow_torus_and_mover_fixed_eq_one (hF : 2 < Nat.card F)
    (α : MulAut SL(2,F))
    (hU : (upperUnipotent F).map α.toMonoidHom = upperUnipotent F)
    (hD : ∀ z : Fˣ, α (diag z) = diag z)
    (g : SL(2,F)) (hg : g ∉ rankOneBorel F) (hfix : α g = g) : α = 1 := by
  obtain ⟨d,rfl⟩ := sylow_preserving_diagonal_fixed_inner hF α hU hD
  have hdg : diag d * g = g * diag d := mul_inv_eq_iff_eq_mul.mp hfix
  have h10 : g.val 1 0 ≠ 0 := fun hh => hg ((mem_rankOneBorel_iff g).mpr hh)
  have he := congrArg (fun x : SL(2,F) => x.val 1 0) hdg
  have hinv : (d:F)⁻¹ = (d:F) := by
    apply mul_right_cancel₀ h10
    simpa [mul_apply,Fin.sum_univ_two,diag2_coe',mul_comm] using he
  have hs : (d:F)^2 = 1 := by
    calc (d:F)^2 = (d:F)⁻¹ * (d:F) := by rw [pow_two,hinv]
         _ = 1 := inv_mul_cancel₀ d.ne_zero
  have hd1 : d = 1 := Units.ext (by
    change (d:F) = 1
    rcases sq_eq_one_iff.mp hs with h | h
    · exact h
    · simpa only [CharTwo.neg_eq] using h)
  subst d
  have he1 : diag (1:Fˣ) = 1 := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [diag2_coe']
  rw [he1,map_one]

/-- The same rigidity in arbitrary Sylow and full odd torus coordinates. -/
theorem odd_torus_and_mover_fixed_eq_one (hF : 2 < Nat.card F)
    (S : Sylow 2 SL(2,F)) (C : Subgroup SL(2,F))
    (hC : C ≤ normalizer (S : Set SL(2,F)))
    (ho : Odd (Nat.card C)) (hcard : Nat.card C = Nat.card Fˣ)
    (α : MulAut SL(2,F))
    (hS : (S : Subgroup SL(2,F)).map α.toMonoidHom = S)
    (hfixC : ∀ c ∈ C, α c = c)
    (g : SL(2,F)) (hg : g ∉ normalizer (S : Set SL(2,F)))
    (hfix : α g = g) : α = 1 := by
  obtain ⟨m,d,hm,hd⟩ := sylow_odd_subgroup_diagonal_coordinates S C hC ho
  have hdi : Function.Injective d := by
    intro x y hxy
    apply Subtype.ext
    apply (MulAut.conj m).injective
    change m * x * m⁻¹ = m * y * m⁻¹
    rw [hd x,hd y,hxy]
  have hds : Function.Surjective d := by
    let _ : Fintype C := Fintype.ofFinite C
    let _ : Fintype Fˣ := Fintype.ofFinite Fˣ
    exact ((Fintype.bijective_iff_injective_and_card d).mpr
      ⟨hdi,by simpa only [←Nat.card_eq_fintype_card] using hcard⟩).2
  let e := MulAut.conj m
  let β := MulAut.congr e α
  have hβ (x : SL(2,F)) : β (e x) = e (α x) := by
    change e (α (e.symm (e x))) = _
    rw [e.symm_apply_apply]
  have hβU : (upperUnipotent F).map β.toMonoidHom = upperUnipotent F := by
    rw [←hm,Subgroup.map_map]
    have he : β.toMonoidHom.comp e.toMonoidHom =
        e.toMonoidHom.comp α.toMonoidHom := MonoidHom.ext hβ
    change (S : Subgroup SL(2,F)).map (β.toMonoidHom.comp e.toMonoidHom) = _
    rw [he,←Subgroup.map_map,hS]
  have hβD (z : Fˣ) : β (diag z) = diag z := by
    obtain ⟨x,rfl⟩ := hds z
    change β (diag2 (d x : F) _) = diag2 (d x : F) _
    rw [←hd x]
    change β (e x) = e x
    rw [hβ,hfixC x x.property]
  have hg' : e g ∉ rankOneBorel F := by
    intro hmem
    apply hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    have hh := mem_normalizer_iff_map_conj_eq.mp hmem
    rw [←hm,Subgroup.map_map] at hh
    rw [Subgroup.map_map]
    have he : e.toMonoidHom.comp (MulAut.conj g).toMonoidHom =
        (MulAut.conj (e g)).toMonoidHom.comp e.toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
        map_mul,map_inv]
    exact (congrArg (fun f => (S : Subgroup SL(2,F)).map f) he).trans hh
  have hβ1 := sylow_torus_and_mover_fixed_eq_one hF β hβU hβD
    (e g) hg' (by rw [hβ,hfix])
  apply (MulAut.congr e).injective
  simpa only [map_one] using hβ1

end Matrix.SpecialLinearGroup
