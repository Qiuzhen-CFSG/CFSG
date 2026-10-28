module

public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.TorusControl
public import Theory.SpecificGroups.PSL3.SmallCompletion.TorusAlignment
public import Theory.SpecificGroups.PSL3.SmallCompletion.TorusAutomorphismForm

/-!
# Literal whole-Borel coordinates over the field of four elements

The simultaneous-scaling torus is the whole projective torus when the
field has four elements. Restricting an actual Borel automorphism to its
characteristic unipotent core then supplies the torus-normalized coordinate
form on that original subgroup. Both the full cubic torus and the two
ordered root planes are retained.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.SmallCompletion
open Matrix.PSL3.LinearThree Matrix.PSL3.CartanActions
open Matrix.PSL3.LinearAmbientGeometry Matrix.PSL3Even.UnipotentGeometry
variable (F : Type*) [Field F] [Finite F]

/-- The literal diagonal diag(t,1,t⁻¹) in the projective Borel. -/
@[expose] def simultaneousTorus : Fˣ →* borel F := {
  toFun t := ⟨torusMap F (t,t⁻¹),torus_le_borel F ⟨(t,t⁻¹),rfl⟩⟩
  map_one' := Subtype.ext (by
    change torusMap F (1 : Fˣ×Fˣ)=1
    exact map_one _)
  map_mul' t s := Subtype.ext (by
    have he : (t*s,(t*s)⁻¹)=(t,t⁻¹)*(s,s⁻¹) := by
      ext <;> simp [mul_comm]
    change torusMap F (t*s,(t*s)⁻¹)=_
    rw [he,map_mul]
    rfl) }

/-- These coordinates have no projective scalar ambiguity. -/
theorem simultaneousTorus_injective : Function.Injective (simultaneousTorus F) := by
  apply (MonoidHom.ker_eq_bot_iff (simultaneousTorus F)).mp
  apply eq_bot_iff.mpr
  intro t ht
  change t=1
  have hh : torusMap F (t,t⁻¹)=1 := congrArg Subtype.val ht
  obtain ⟨he,h3⟩ := (BorelQuotient.torusMap_eq_one_iff F _).mp hh
  change t=t⁻¹ at he
  change t^3=1 at h3
  have h2 : t^2=1 := by
    rw [pow_two]
    exact (congrArg (fun x => t*x) he).trans (mul_inv_cancel t)
  have h := h3
  rw [show (3:ℕ)=2+1 from rfl,pow_add,h2,one_mul,pow_one] at h
  exact h

/-- Exact simultaneous-scaling action on the original unitriangular map. -/
theorem simultaneousTorus_conj (t : Fˣ) (u : U F) :
    simultaneousTorus F t*borelUnipotent F u*(simultaneousTorus F t)⁻¹ =
      borelUnipotent F ⟨t*u.x,t*u.y,(t:F)^2*u.c⟩ := by
  apply Subtype.ext
  change projection F (torusSL F (t,t⁻¹))*projection F (specialLinear F u)*
    (projection F (torusSL F (t,t⁻¹)))⁻¹ = projection F (specialLinear F _)
  rw [←map_inv,←map_mul,←map_mul]
  apply congrArg (projection F)
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  change (torusSL F (t,t⁻¹)).val*matrix F u =
    matrix F _*(torusSL F (t,t⁻¹)).val
  rw [torusSL_val]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrix,Matrix.diagonal_mul,Matrix.mul_diagonal,pow_two,mul_assoc]
  all_goals field_simp

/-- At field four this is the whole torus, not a selected subgroup. -/
theorem simultaneousTorus_range (hF : Nat.card F=4) :
    (simultaneousTorus F).range=borelTorus F := by
  apply eq_of_le_of_card_ge
  · rintro _ ⟨t,rfl⟩
    exact ⟨(t,t⁻¹),rfl⟩
  · have ht := BorelQuotient.card_torus_mul_scalar F
    rw [hF] at ht
    have hc : Nat.card (borelTorus F)=3 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (torus_le_borel F)).toEquiv]
      norm_num at ht
      omega
    rw [hc,←Nat.card_congr (MonoidHom.ofInjective (simultaneousTorus_injective F)).toEquiv,
      Nat.card_units,hF]

/-- Restriction of an actual torus-normalizing Borel automorphism has the
exact semilinear/Frobenius form on its literal unipotent subgroup. -/
theorem borel_four_torus_normal_form (hF : Nat.card F=4)
    (a : MulAut (borel F))
    (h₁ : ∀ u ∈ V₁ F, a (borelUnipotent F u) ∈ (V₁ F).map (borelUnipotent F))
    (h₂ : ∀ u ∈ V₂ F, a (borelUnipotent F u) ∈ (V₂ F).map (borelUnipotent F))
    (hT : ∀ t ∈ borelTorus F, a t ∈ borelTorus F) :
    ∃ (r s k l : F) (σ : F ≃+* F), r ≠ 0 ∧ s ≠ 0 ∧
      (∀ u : U F, a (borelUnipotent F u) =
        borelUnipotent F ⟨r*σ u.x,s*σ u.y,
          r*s*σ u.c+k*(σ u.x)^2+l*(σ u.y)^2⟩) ∧
      ∀ t : Fˣ, a (simultaneousTorus F t) =
        simultaneousTorus F (Units.map σ.toMonoidHom t) := by
  let j := borelUnipotent F
  have hj : Function.Injective j := borelUnipotent_injective F
  have hR : j.range.map a.toMonoidHom=j.range := by
    rw [borelUnipotent_range,←BorelQuotient.twoCore_eq F (n:=2) (by simpa using hF),
      pCore_map_iso]
  let e : U F ≃* j.range := MonoidHom.ofInjective hj
  let d : MulAut (U F) := e.trans
    ((j.range.equivMapOfInjective a.toMonoidHom a.injective).trans
      ((MulEquiv.subgroupCongr hR).trans e.symm))
  have hd (u : U F) : j (d u)=a (j u) := by
    change ((e (e.symm _)) : borel F)=_
    rw [e.apply_symm_apply]
    rfl
  have hd₁ (u : U F) (hu : u∈V₁ F) : d u∈V₁ F := by
    apply (mem_map_iff_mem hj).mp
    rw [hd]
    exact h₁ u hu
  have hd₂ (u : U F) (hu : u∈V₂ F) : d u∈V₂ F := by
    apply (mem_map_iff_mem hj).mp
    rw [hd]
    exact h₂ u hu
  have htor (t : Fˣ) : ∃ s : Fˣ, a (simultaneousTorus F t)=simultaneousTorus F s := by
    have ht := hT _ ((simultaneousTorus_range F hF).le ⟨t,rfl⟩)
    rw [←simultaneousTorus_range F hF] at ht
    obtain ⟨s,hs⟩ := ht
    exact ⟨s,hs.symm⟩
  have htd : ∀ t : Fˣ, ∃ s : Fˣ, ∀ u : U F,
      d ⟨t*u.x,t*u.y,(t:F)^2*u.c⟩ =
        ⟨s*(d u).x,s*(d u).y,(s:F)^2*(d u).c⟩ := by
    intro t
    obtain ⟨s,hs⟩ := htor t
    refine ⟨s,fun u => hj ?_⟩
    rw [hd,←simultaneousTorus_conj,map_mul,map_mul,map_inv,hs,←hd,
      simultaneousTorus_conj]
  obtain ⟨r,s,k,l,σ,hr,hs,hform⟩ := torus_normalized_root_plane_automorphism_form d hd₁ hd₂ htd
  refine ⟨r,s,k,l,σ,hr,hs,fun u => (hd u).symm.trans (congrArg j (hform u)),?_⟩
  intro t
  obtain ⟨q,hq⟩ := htor t
  have hact (u : U F) : d ⟨t*u.x,t*u.y,(t:F)^2*u.c⟩ =
        ⟨q*(d u).x,q*(d u).y,(q:F)^2*(d u).c⟩ := by
    apply hj
    rw [hd,←simultaneousTorus_conj,map_mul,map_mul,map_inv,hq,←hd,
      simultaneousTorus_conj]
  have he := congrArg U.x (hact (⟨1,0,0⟩ : U F))
  rw [hform,hform] at he
  have htq : σ (t:F)=(q:F) := by
    apply mul_left_cancel₀ hr
    simpa only [mul_one,mul_zero,map_one,map_zero,mul_comm (q:F)] using he
  rw [hq]
  congr 1
  exact Units.ext htq.symm

end Matrix.PSL3.SmallCompletion
