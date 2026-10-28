module
public import CFSG.Quasithin.ChapterE.Section03.Parameters.AutomizerFF
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.M22CodeRadical

/-!
# The unchanged M22-code fixed space under pair reselection

Rank-five uniqueness in the original Sylow automizer identifies the actual
fixed subgroups of two actors. Thus selecting a pair in the radical's Sylow
join leaves the original four-space unchanged. Transport through the full
automizer also shows that an odd subgroup fixing this space and normalizing
the original module fixes the whole module. No quotient of the full
normalizer kernel is removed.

Source: Aschbacher--Smith 8.2.7, printed pp.717--718, using the native
H.14.3 and H.16.3 quintet calculations, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- The original automizer identifies rank-five actors in one two-subgroup,
so reselection leaves their literal fixed subgroups unchanged. -/
theorem m22_code_fixed_eq (W T A B : Subgroup G) [IsElementaryAbelian 2 W]
    [IsElementaryAbelian 2 (inducedAutomizer W A)]
    [IsElementaryAbelian 2 (inducedAutomizer W B)]
    (hT : IsPGroup 2 T) (hAT : A ≤ T) (hBT : B ≤ T)
    (hAN : A ≤ normalizer (W : Set G)) (hBN : B ≤ normalizer (W : Set G))
    (a : Automizer W →* MathieuCode.m22PairStabilizer) (ha : Function.Injective a)
    (hA : rank (inducedAutomizer W A) = 5) (hB : rank (inducedAutomizer W B) = 5) :
    inducedAutomizer W A = inducedAutomizer W B ∧
      W ⊓ centralizer (A : Set G) = W ⊓ centralizer (B : Set G) := by
  let P := inducedAutomizer W T
  let A' := inducedAutomizer W A
  let B' := inducedAutomizer W B
  have hp : IsPGroup 2 P := hT.comap_subtype.map _
  let : IsElementaryAbelian 2 (A'.map a) := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 (B'.map a) := IsElementaryAbelian.map _
  have he : A'.map a = B'.map a :=
    MathieuCode.NormalizedShadowRows.M22CodeQuintet.eq_of_common_two_group _ _ (P.map a)
      (hp.map a) (map_mono (map_mono (comap_mono hAT)))
      (map_mono (map_mono (comap_mono hBT)))
      ((rank_map_injective a ha _).trans hA) ((rank_map_injective a ha _).trans hB)
  have hab : inducedAutomizer W A = inducedAutomizer W B := Subgroup.map_injective ha he
  refine ⟨hab,?_⟩
  ext w
  constructor
  · intro hw
    refine ⟨hw.1,?_⟩
    have hf := (mem_fixedSpace_inducedAutomizer W A hAN (Additive.ofMul ⟨w,hw.1⟩)).mpr hw.2
    rw [hab] at hf
    exact (mem_fixedSpace_inducedAutomizer W B hBN _).mp hf
  · intro hw
    refine ⟨hw.1,?_⟩
    have hf := (mem_fixedSpace_inducedAutomizer W B hBN (Additive.ofMul ⟨w,hw.1⟩)).mpr hw.2
    rw [←hab] at hf
    exact (mem_fixedSpace_inducedAutomizer W A hAN _).mp hf

end CFSG.Quasithin.Chapter8.MathieuShadowRows
public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter8.MathieuShadowRows
open ChapterE Sporadic.Mathieu MathieuCode
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Every odd subgroup normalizing the original code and centralizing its
quintet fixed space centralizes the full original code. -/
theorem m22_code_odd_centralizer (W A Z : Subgroup G) [IsElementaryAbelian 2 W]
    (hAN : A ≤ normalizer (W : Set G))
    (E : Additive W ≃ₗ[ZMod 2] M22Code)
    (a : Automizer W →* MathieuCode.m22PairStabilizer) (ha : Function.Injective a)
    (hE : ∀ b v, E (automizerRepresentation W b v) = m22OuterCodeRepresentation (a b) (E v))
    (c : MathieuCode.m22PairStabilizer)
    (hc : ((inducedAutomizer W A).map a).map (MulAut.conj c).toMonoidHom = M22Quintet.K)
    (hZ : Odd (Nat.card Z)) (hZN : Z ≤ normalizer (W : Set G))
    (hZU : Z ≤ centralizer (W ⊓ centralizer (A : Set G) : Set G)) :
    Z ≤ centralizer (W : Set G) := by
  let F := E.trans (LinearMap.GeneralLinearGroup.toLinearEquiv (m22OuterCodeRepresentation.asGroupHom c))
  let b : Automizer W →* MathieuCode.m22PairStabilizer := (MulAut.conj c).toMonoidHom.comp a
  have hF (x : Automizer W) (v : Additive W) :
      F (automizerRepresentation W x v) = m22OuterCodeRepresentation (b x) (F v) := by
    change m22OuterCodeRepresentation c (E (automizerRepresentation W x v)) =
      m22OuterCodeRepresentation (c*a x*c⁻¹) (m22OuterCodeRepresentation c (E v))
    rw [hE]
    simp only [←Module.End.mul_apply,←map_mul]
    congr 2
    group
  have hfix : (fixedSpace (automizerRepresentation W) (inducedAutomizer W A)).map F.toLinearMap =
      fixedSpace m22OuterCodeRepresentation M22Quintet.K := by
    rw [fixedSpace_map_equivariant _ _ b F hF]
    change fixedSpace m22OuterCodeRepresentation
      ((inducedAutomizer W A).map ((MulAut.conj c).toMonoidHom.comp a)) = _
    rw [←map_map,hc]
  let f : Z →* Automizer W := W.normalizerMonoidHom.rangeRestrict.comp (inclusion hZN)
  intro z hz
  let z' : Z := ⟨z,hz⟩
  have ho : Odd (orderOf (b (f z'))) :=
    (hZ.of_dvd_nat (orderOf_dvd_natCard z')).of_dvd_nat (orderOf_map_dvd (b.comp f) z')
  have hf : ∀ v ∈ fixedSpace m22OuterCodeRepresentation M22Quintet.K,
      m22OuterCodeRepresentation (b (f z')) v = v := by
    intro v hv
    rw [←hfix] at hv
    obtain ⟨w,hw,rfl⟩ := hv
    change m22OuterCodeRepresentation (b (f z')) (F w) = F w
    rw [←hF]
    apply congrArg F
    apply Additive.toMul.injective
    apply Subtype.ext
    have hwU : (w.toMul : G) ∈ W ⊓ centralizer (A : Set G) :=
      ⟨w.toMul.property,(mem_fixedSpace_inducedAutomizer W A hAN w).mp hw⟩
    change z * (w.toMul : G) * z⁻¹ = (w.toMul : G)
    rw [←(hZU hz) _ hwU,mul_assoc,mul_inv_cancel,mul_one]
  have he := NormalizedShadowRows.M22CodeFourSpace.odd_fixed_eq_one _ ho hf
  have he' : a (f z') = 1 := (MulAut.conj c).map_eq_one_iff.mp he
  have hf1 : f z' = 1 := ha (he'.trans (map_one a).symm)
  intro w hw
  have hh := congrArg (fun x : Automizer W => (x.val ⟨w,hw⟩ : G)) hf1
  change z*w*z⁻¹=w at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter8.MathieuShadowRows
