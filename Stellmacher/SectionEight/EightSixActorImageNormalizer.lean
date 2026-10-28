module
public import Stellmacher.SectionEight.EightSixCommonStructure

/-!
# The core image underlying the predecessor actor

For the actual equation-one configuration in Stellmacher (8.6), take any
homomorphism from the next stabilizer that kills its ordinary two-core.
The image of A=Vprevious intersect Qa equals the image of Q=O₂(L), and
both the edge-Sylow and the full edge-stabilizer images normalize it. No cost branch, action module, or
classification conclusion is assumed.

The three-factor generation Q=A Atilde D identifies the images because
Atilde and D lie in Qnext. The equation-one Sylow intersection puts Q
inside the edge Sylow. Since L is a normal closure under Ga, its
characteristic two-core Q is normalized by Ga and by the edge Sylow.
Passing that normalization through the supplied homomorphism proves the
normalization assertions.

This gives the Sylow-invariance needed to promote the relative double-SL₂
group in the cost-four branch to the whole next faithful image. Source:
Stellmacher, Journal of Algebra 190 (1997), proof of (8.6), equation (1)
and the cost-four paragraph on printed pp.41–44.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix

public theorem eight_six_actor_image_eq_core_and_normalized
    {G X : Type*} [Group G] [Finite G] [Group X] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hlength : ctx.criticalPath.length = 2)
    (previous : ctx.Γ.Vertex) (D L Q : Subgroup G)
    (hD : D = QAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.firstStep)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L)
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q)
    (f : GAt ctx.Γ ctx.criticalPath.firstStep →* X)
    (hkernel : pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep) ≤ f.ker) :
    let P := GAt ctx.Γ ctx.criticalPath.firstStep
    let A := VAt ctx.Γ previous ⊓ QAt ctx.Γ ctx.criticalPath.a
    (A.subgroupOf P).map f = (Q.subgroupOf P).map f ∧
      (S.subgroupOf P).map f ≤ Subgroup.normalizer (((A.subgroupOf P).map f : Subgroup X) : Set X) ∧
      ((GAt ctx.Γ ctx.criticalPath.a ⊓ P).subgroupOf P).map f ≤
        Subgroup.normalizer (((A.subgroupOf P).map f : Subgroup X) : Set X) := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let A := VAt Γ previous ⊓ QAt Γ cp.a
  let V := VAt Γ cp.firstStep
  let R := QAt Γ cp.firstStep
  let Atilde := V ⊓ QAt Γ cp.a
  have hSP : S ≤ P := (edge_sylow_data ctx.sectionSeven Γ cp).2.1
  have hSGa : S ≤ GAt Γ cp.a := (edge_sylow_data ctx.sectionSeven Γ cp).1.1
  have hQS : Q ≤ S :=
    (le_sup_right.trans data.sylow_intersection.symm.le).trans inf_le_right
  have hQP : Q ≤ P := hQS.trans hSP
  have hAQ : A ≤ Q := data.core_generation ▸ le_sup_of_le_left le_sup_left
  have hAP : A ≤ P := hAQ.trans hQP
  have hVR : V ≤ R := neighbor_join_le_core_of_length_gt_one Γ cp
    (by exact hlength ▸ by decide) _
  have hDR : D ≤ R := hD ▸ inf_le_right
  have hRP : R ≤ P := by
    change Γ.twoCoreAt _ ≤ Γ.vertexStabilizer _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hRnative : R.subgroupOf P = pCore 2 P := by
    change (Γ.twoCoreAt _).subgroupOf P = _
    rw [Γ.twoCoreAt_def]
    exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
  have hkill (M : Subgroup G) (hMR : M ≤ R) : (M.subgroupOf P).map f = ⊥ := by
    apply bot_unique
    rintro x ⟨m,hm,rfl⟩
    exact MonoidHom.mem_ker.mp (((Subgroup.subgroupOf_mono P hMR).trans
      (hRnative.symm ▸ hkernel)) hm)
  have himage : (A.subgroupOf P).map f = (Q.subgroupOf P).map f := by
    have hgen : Q = (A ⊔ Atilde) ⊔ D := data.core_generation
    rw [hgen,Subgroup.subgroupOf_sup (sup_le hAP (inf_le_left.trans (hVR.trans hRP)))
      (hDR.trans hRP),Subgroup.subgroupOf_sup hAP (inf_le_left.trans (hVR.trans hRP)),
      Subgroup.map_sup,Subgroup.map_sup,hkill Atilde (inf_le_left.trans hVR),hkill D hDR,
      sup_bot_eq,sup_bot_eq]
  have hQN : GAt Γ cp.a ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQ,twoCoreIn]
    apply (eight_six_conjugate_closure_normalizer (QAt Γ previous) (GAt Γ cp.a)).trans
    rw [← hL]
    exact BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
      L (pCore 2 L)
  have hnative : (GAt Γ cp.a ⊓ P).subgroupOf P ≤
      Subgroup.normalizer (Q.subgroupOf P : Set P) := by
    intro s hs
    apply Subgroup.mem_normalizer_iff.mpr
    intro q
    change (q:G) ∈ Q ↔ (s:G)*(q:G)*(s:G)⁻¹ ∈ Q
    exact Subgroup.mem_normalizer_iff.mp (hQN hs.1) q
  have hedge : ((GAt Γ cp.a ⊓ P).subgroupOf P).map f ≤
      Subgroup.normalizer ((A.subgroupOf P).map f : Set X) := by
    rw [himage]
    exact (Subgroup.map_mono hnative).trans (Subgroup.le_normalizer_map f)
  exact ⟨himage,(Subgroup.map_mono (Subgroup.subgroupOf_mono P (le_inf hSGa hSP))).trans hedge,hedge⟩
end Stellmacher.SectionEight
