module
public import Stellmacher.SectionEight.GeneratedEightSixSmallIndexBarredQuotient
public import Stellmacher.SectionEight.GeneratedEightSixSL2ResidualOdd

/-!
# The initial residual is covered by the core and the three-Sylow

For the equation-one configuration of Stellmacher (8.6), the initial
SL2(2) quotient implies E_a lies in Q join T, where T is the actual
chosen Sylow three-subgroup and Q=O2(L). No actor-index or cost-branch
hypothesis is required.

The native residual image in SL2(2) is its normal order-three derived
subgroup. It therefore lies in the image of the given three-Sylow. Pulling
back gives E_a contained in Qa times T. Both E_a and T lie in L, and
normality of L identifies Q with L intersect Qa. The same factorization
therefore has its two-part in Q and gives the claimed containment.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.6), the initial
SL2(2) quotient on printed p.41 and the fixed-core decomposition in case C.
This supplies the actual residual-to-three-Sylow transfer for that proof.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u
public theorem eight_six_initial_residual_le_core_sup_three
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (ctx : SectionEightLocalContext G S P1 P2)
    (hquot : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.a)
      (QAt ctx.Γ ctx.criticalPath.a) SL2Two)
    (previous : ctx.Γ.Vertex) (D L Q T : Subgroup G)
    (hL : L = conjugateClosure (QAt ctx.Γ previous) (GAt ctx.Γ ctx.criticalPath.a))
    (hQ : Q = twoCoreIn L) (hT : IsSylowIn 3 T (GAt ctx.Γ ctx.criticalPath.a))
    (data : EightSixEquationOneData ctx.Γ ctx.criticalPath previous D L Q) :
    EAt ctx.Γ ctx.criticalPath.a ≤ Q ⊔ T := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.a
  let Qa := QAt Γ cp.a
  let E := EAt Γ cp.a
  have hEdef : E = twoResidualIn P := Γ.twoResidualAt_def _
  have hEP : E ≤ P := hEdef ▸ twoResidualIn_le P
  obtain ⟨sylow,hsylow⟩ := hT
  have hTP : T ≤ P := hsylow ▸ Subgroup.map_subtype_le _
  have hTthree : IsPGroup 3 T := hsylow ▸ sylow.isPGroup'.map _
  have hTE : T ≤ E := hEdef ▸ eight_six_three_subgroup_le_residual T P hTP hTthree
  have hTL : T ≤ L := hTE.trans data.residual_le
  have hLnormal : NormalIn L P := by
    refine ⟨data.closure_le,Subgroup.normal_subgroupOf_of_le_normalizer ?_⟩
    rw [hL]
    exact eight_six_conjugate_closure_normalizer _ _
  have hQcore : Q = L ⊓ Qa := by
    rw [hQ,eight_six_core_of_normal_eq_inter _ _ hLnormal]
    rw [show Qa = twoCoreIn P from Γ.twoCoreAt_def _]
  obtain ⟨f,hsurj,hker⟩ := hquot
  have hnative : E.subgroupOf P = twoResidualAmbient (⊤ : Subgroup P) := by
    have hn : E.subgroupOf P = twoResidualSubgroup P := by
      rw [hEdef]
      exact Subgroup.comap_map_eq_self_of_injective P.subtype_injective _
    rw [hn,SectionThree.twoResidualSubgroup_eq_hktPResidual',
      SectionThree.twoResidualAmbient_top_eq_hktPResidual]
  have hEimage : (E.subgroupOf P).map f = _root_.commutator SL2Two := by
    rw [hnative,map_twoResidualAmbient_of_subgroup_image ⊤ f ⊤
      (Subgroup.map_top_of_surjective f hsurj),eight_six_sl2_residual_eq_commutator]
  let _ : ((E.subgroupOf P).map f).Normal := hEimage ▸ inferInstance
  have hEthree : IsPGroup 3 ((E.subgroupOf P).map f) := by
    apply IsPGroup.of_card (n := 1)
    rw [hEimage,isSL2Two_commutator_card (show IsSL2Two SL2Two from ⟨MulEquiv.refl _⟩)]
    rfl
  have hmaple : (E.subgroupOf P).map f ≤ (sylow : Subgroup P).map f :=
    hEthree.le_sylow_of_normal (sylow.mapSurjective hsurj)
  have hle : E.subgroupOf P ≤ (sylow : Subgroup P) ⊔ Qa.subgroupOf P := by
    have hh := Subgroup.map_le_iff_le_comap.mp hmaple
    rwa [Subgroup.comap_map_eq,hker] at hh
  let _ : (Qa.subgroupOf P).Normal := hker ▸ f.normal_ker
  intro e he
  obtain ⟨t,ht,q,hq,hteq⟩ := Subgroup.mem_sup_of_normal_right.mp
    (hle (show (⟨e,hEP he⟩:P) ∈ E.subgroupOf P from he))
  have htT : (t:G) ∈ T := hsylow ▸ Subgroup.mem_map_of_mem P.subtype ht
  have hqL : (q:G) ∈ L := by
    have heq : (t:G)*(q:G)=e := congrArg Subtype.val hteq
    have hh := L.mul_mem (L.inv_mem (hTL htT)) (data.residual_le he)
    simpa only [←heq,inv_mul_cancel_left] using hh
  have hqQ : (q:G) ∈ Q := hQcore ▸ ⟨hqL,hq⟩
  have hh := (Q ⊔ T).mul_mem ((le_sup_right : T ≤ Q ⊔ T) htT) ((le_sup_left : Q ≤ Q ⊔ T) hqQ)
  have heq : (t:G)*(q:G)=e := congrArg Subtype.val hteq
  rwa [heq] at hh
end Stellmacher.SectionEight
