module
public import Theory.SpecificGroups.Suzuki.InvolutionSquares
public import Theory.SpecificGroups.SymplecticFour.AbsoluteCentralizer
public import Theory.SpecificGroups.SymplecticFour.TransvectionRecognition.AbsoluteSocle
public import Theory.SpecificGroups.SymplecticFour.TransvectionSquares
public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalEmbedding.BenderAutomorphisms.Suzuki

/-!
# Excluding Suzuki socles normalized by a transvection

The rank-one normalizer makes the irreducible socle absolutely irreducible,
so its ambient symplectic centralizer is trivial. Every involutory Suzuki
automorphism is inner; hence the normalizing transvection belongs to the
socle. But every Suzuki involution is a square, whereas a rank-one
symplectic involution is not. This proves the actual Suzuki row exclusion
in Aschbacher--Smith G.4.1, printed p.342, without a natural-module premise.
-/

public noncomputable section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
open InvolutionTypes BenderSuzuki.MatrixGroups
variable {F:Type*} [Field F] [Finite F] [CharP F 2]

/-- An irreducible actual Suzuki socle has no rank-one symplectic normalizer. -/
theorem not_suzuki_of_isB1_normalizer (N:Subgroup (Sp F))
    (hi:Representation.IsIrreducible ((Representation.symplecticNatural 2).comp N.subtype))
    (t:Sp F) (ht:t∈normalizer (N:Set (Sp F))) (hr:IsB1 t)
    {m:ℕ} (hm:1≤m) : ¬Nonempty (N≃*SuzukiMatrixGroup m) := by
  rintro ⟨e⟩
  have ha := subgroup_absolutelyIrreducible_of_isB1_normalizer N hi t ht hr
  have hC := centralizer_eq_bot_of_absolutelyIrreducible N ha
  let α:MulAut N := N.normalizerMonoidHom ⟨t,ht⟩
  let β:MulAut (SuzukiMatrixGroup m) := MulAut.congr e α
  have ht2:t^2=1 := by simpa only [hr.1] using pow_orderOf_eq_one t
  have hα2:α^2=1 := by
    change (N.normalizerMonoidHom ⟨t,ht⟩)^2=1
    rw [←map_pow]
    have h:(⟨t,ht⟩:normalizer (N:Set (Sp F)))^2=1 := Subtype.ext ht2
    rw [h,map_one]
  have hβ2:β^2=1 := by
    change (MulAut.congr e α)^2=1
    rw [←map_pow,hα2,map_one]
  obtain ⟨b,hb,_⟩ := BenderSuzuki.ZD.suzuki_involutoryAut_inner_and_twoRank m hm β hβ2
  let n:N := e.symm b
  have hconj (g:N) : t*(g:Sp F)*t⁻¹=(n:Sp F)*(g:Sp F)*(n:Sp F)⁻¹ := by
    have heq : α g=n*g*n⁻¹ := by
      apply e.injective
      have h := DFunLike.congr_fun hb (e g)
      change e (α (e.symm (e g)))=b*e g*b⁻¹ at h
      simpa only [e.symm_apply_apply,n,e.apply_symm_apply,map_mul,map_inv] using h
    exact congrArg Subtype.val heq
  have hc:(n:Sp F)⁻¹*t∈centralizer (N:Set (Sp F)) := by
    apply mem_centralizer_iff.mpr
    intro g hg
    have h := hconj ⟨g,hg⟩
    have hh : t*g=(n:Sp F)*g*(n:Sp F)⁻¹*t := (mul_inv_eq_iff_eq_mul).mp h
    change g*((n:Sp F)⁻¹*t)=((n:Sp F)⁻¹*t)*g
    calc
      g*((n:Sp F)⁻¹*t)=(n:Sp F)⁻¹*((n:Sp F)*g*(n:Sp F)⁻¹*t) := by group
      _ = (n:Sp F)⁻¹*(t*g) := by rw [hh]
      _ = ((n:Sp F)⁻¹*t)*g := by group
  have heq:(n:Sp F)⁻¹*t=1 := by simpa only [hC,mem_bot] using hc
  have htn:t=(n:Sp F) := by
    have h := congrArg (fun x:Sp F=>(n:Sp F)*x) heq
    simpa only [mul_inv_cancel_left,mul_one] using h
  have hno:orderOf n=2 := by rw [←orderOf_coe n,←htn]; exact hr.1
  obtain ⟨x,hx⟩ := suzuki_involution_is_square m (by omega) (e n)
    ((e.orderOf_eq n).trans hno)
  let y:N := e.symm x
  have hy:y^2=n := by apply e.injective; simpa [y] using hx
  apply isB1_not_square t hr (y:Sp F)
  exact (congrArg Subtype.val hy).trans htn.symm
end Theory.SpecificGroups.SymplecticFour.TransvectionRecognition
