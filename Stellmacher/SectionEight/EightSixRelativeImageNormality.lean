module
public import Stellmacher.SectionEight.EightSixActorImageNormalizer
public import Stellmacher.SectionEight.GeneratedEightSixResidualCommutator
public import Stellmacher.SectionThree.ResidualImageOddPGroup
public import Stellmacher.SectionThree.PrimitiveDihedralExtraction.ResidualLift
public import Stellmacher.SectionFiveToSeven.Result7_8.GeometricExtraction

/-!
# The relative odd actor is normal in the full next image

Let f be a supplied surjective homomorphism from the next stabilizer that
kills its ordinary two-core. In the actual selected configuration, put
B=f(A) and F=[O₂′(X),B]. Then F is normal in the full image X, the selected
residual O²(E) maps into F, and E maps into FB. These conclusions require
no numerical cost branch and retain the actual D/L/Q and geometric data.

The local residual-image theorem puts the image of O²(Pnext) in O₂′(X).
The selected residual conjugator therefore sends B into FB, so both
conjugate actor groups generating E lie in FB. Image(A)=image(Q) is
normalized by the entire edge-stabilizer image, which also normalizes F.
The selected E and the edge generate Pnext, so F is globally normal.
Since B is a two-group, the residual of any subgroup of FB lies in F;
residual functoriality yields the final assertion for O²(E).

This is the group promotion following bounded (1.6) in the cost-four
paragraph of Stellmacher, Journal of Algebra 190 (1997), proof of (8.6),
printed p.44. It makes the relative commutator module invariant under the
whole next stabilizer without identifying the selected E with that group.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
open scoped commutatorElement

public theorem eight_six_relative_image_normality
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (E A0 : Subgroup G) (actor : G)
    (geom : SectionNine.NineThreeGeometricData ctx.Γ
      ctx.criticalPath.firstStep ctx.criticalPath.a
      (VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a) E A0 actor)
    (hedge : E ⊔ (GAt ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ ctx.criticalPath.firstStep) =
      GAt ctx.Γ ctx.criticalPath.firstStep)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* X)
    (hf : Function.Surjective f)
    (hkernel : pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep) ≤ f.ker) :
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    let B := (A.subgroupOf P).map f
    let F := ⁅SectionOne.oddCore X,B⁆
    F.Normal ∧ ((twoResidualIn E).subgroupOf P).map f ≤ F ∧
      (E.subgroupOf P).map f ≤ F ⊔ B := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let B := (A.subgroupOf P).map f
  let W := SectionOne.oddCore X
  let F := ⁅W,B⁆
  let J := GAt Γ cp.a ⊓ P
  have hEP : E ≤ P := geom.group_le
  have hAE : A ≤ E := geom.generated ▸ le_sup_left
  have hAP : A ≤ P := hAE.trans hEP
  have hlocal := (edge_local_data ctx.sectionSeven Γ cp).2
  obtain ⟨prime,hprime,hodd,hres⟩ := SectionThree.pSet_residual_image_is_odd_pGroup
    S (sectionThreeHypotheses ctx.sectionSeven) P ((pFamily_iff_pSet _ _ _).mp hlocal.1)
      hlocal.2 f hkernel
  let _ : Fact prime.Prime := ⟨hprime⟩
  have hresOdd : Nat.Coprime 2 (Nat.card ((twoResidualSubgroup P).map f)) := by
    obtain ⟨n,hn⟩ := hres.exists_card_eq
    rw [hn]
    exact (hodd.pow).coprime_two_left
  have hnativeNormal : (twoResidualSubgroup P).Normal := by
    rw [SectionThree.twoResidualSubgroup_eq_hktPResidual']
    exact BenderSuzuki.External.hktPResidual_normal
  have hresNormal : ((twoResidualSubgroup P).map f).Normal := hnativeNormal.map f hf
  have hresW : (twoResidualSubgroup P).map f ≤ W := le_sSup ⟨hresNormal,hresOdd⟩
  have hRmono := eight_six_residual_mono E P hEP
  have hRnative : (twoResidualIn P).subgroupOf P = twoResidualSubgroup P :=
    Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  let x : P := ⟨geom.x,hEP (twoResidualIn_le E geom.residual_mem)⟩
  have hxW : f x ∈ W := hresW (Subgroup.mem_map_of_mem f (by
    rw [← hRnative]
    exact hRmono geom.residual_mem))
  let M := ((F ⊔ B).comap f).map P.subtype
  have hAM : A ≤ M := by
    intro a ha
    exact ⟨⟨a,hAP ha⟩,Subgroup.mem_sup_right (Subgroup.mem_map_of_mem f ha),rfl⟩
  have hconjM : A.conjBy geom.x ≤ M := by
    rintro y ⟨a,ha,rfl⟩
    let aP : P := ⟨a,hAP ha⟩
    have haB : f aP ∈ B := Subgroup.mem_map_of_mem f ha
    have hc : ⁅f x,f aP⁆ ∈ F := Subgroup.commutator_mem_commutator hxW haB
    have hh : f (x*aP*x⁻¹) ∈ F ⊔ B := by
      rw [map_mul,map_mul,map_inv]
      have heq : f x*f aP*(f x)⁻¹ = ⁅f x,f aP⁆ * f aP := by
        simp only [commutatorElement_def,mul_assoc,inv_mul_cancel,mul_one]
      rw [heq]
      exact (F ⊔ B).mul_mem (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right haB)
    exact ⟨x*aP*x⁻¹,hh,rfl⟩
  have hEM : E ≤ M := geom.generated ▸ sup_le hAM hconjM
  have hEimage : (E.subgroupOf P).map f ≤ F ⊔ B := by
    rintro y ⟨e,he,rfl⟩
    obtain ⟨m,hm,heq⟩ := hEM he
    have hm' : m = e := Subtype.ext heq
    exact hm' ▸ hm
  have hBN := (eight_six_actor_image_eq_core_and_normalized ctx hlength previous D L Q
    hD hL hQ data f hkernel).2.2
  let _ : W.Normal := pPrimeCore_normal
  have hFNedge : (J.subgroupOf P).map f ≤ Subgroup.normalizer (F : Set X) :=
    le_normalizer_commutator_of_le_normalizers' Subgroup.le_normalizer_of_normal hBN
  have hFNE : (E.subgroupOf P).map f ≤ Subgroup.normalizer (F : Set X) :=
    hEimage.trans (sup_le F.le_normalizer (Subgroup.normalizer_commutator_ge_right W B))
  have hgen : (E.subgroupOf P).map f ⊔ (J.subgroupOf P).map f = ⊤ := by
    rw [← Subgroup.map_sup,← Subgroup.subgroupOf_sup hEP (show J ≤ P from inf_le_right)]
    change ((E ⊔ (GAt Γ cp.a ⊓ P)).subgroupOf P).map f = ⊤
    rw [hedge,Subgroup.subgroupOf_self,← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.mpr hf
  have hnormal : F.Normal := Subgroup.normalizer_eq_top_iff.mp
    (top_unique (hgen ▸ sup_le hFNE hFNedge))
  let _ := hnormal
  have hAQ : A ≤ Q := data.core_generation ▸ le_sup_of_le_left le_sup_left
  have hQtwo : IsPGroup 2 Q := by
    rw [hQ,twoCoreIn]
    exact (pCore_isPGroup (p := 2)).map _
  have hBp : IsPGroup 2 B :=
    ((hQtwo.to_le hAQ).of_equiv (Subgroup.subgroupOfEquivOfLe hAP).symm).map f
  have hresF : twoResidualAmbient ((E.subgroupOf P).map f) ≤ F :=
    SectionThree.twoResidualAmbient_le_left_of_le_sup F B ((E.subgroupOf P).map f)
      (hnormal.subgroupOf (F ⊔ B)) hBp hEimage
  have hresNative : (twoResidualIn E).subgroupOf P = twoResidualAmbient (E.subgroupOf P) := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le ((twoResidualIn_le E).trans hEP)]
    exact (map_twoResidualAmbient_of_subgroup_image (E.subgroupOf P) P.subtype E
      (Subgroup.map_subgroupOf_eq_of_le hEP)).symm
  refine ⟨hnormal,?_,hEimage⟩
  rw [hresNative,map_twoResidualAmbient_of_subgroup_image (E.subgroupOf P) f _ rfl]
  exact hresF
end Stellmacher.SectionEight
