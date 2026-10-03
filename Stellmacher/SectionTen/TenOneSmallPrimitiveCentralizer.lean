module
public import Stellmacher.SectionTen.TenOneSmallCentralizerElementary
public import Theory.GroupTheory.CenterFreeC4SquarePrimitiveCentralizer

/-!
# Middle-core centralizers of primitive residual points

In the actual small first-module case, an element of the middle residual
core with nontrivial square has centralizer in Qmiddle precisely equal to
the middle residual core. Its centralizer inside Wstar is consequently
the middle central plane.

The center-free C4-square residual packet is applied inside the actual
middle stabilizer. The chosen point, core and residual intersection are
transported through its literal subtype embedding. The general theorem
uses the nontrivial cubic residual action and the fact that its commuting
two-group automorphisms fix only square-one points. Intersecting the
result with Wstar uses its proved intersection with the residual core.

Source: Stellmacher (10.1)(a3), printed p.61 before (8),
`refs/files/stellmacher-n-group.pdf`. The point is supplied explicitly;
existence in the first and middle residual intersection is a separate step.
-/

namespace Stellmacher.SectionTen
open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine
universe u
variable {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
  {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
  {embedding : G →* H} {T A B : Subgroup G}

public theorem ten_one_small_primitive_middle_centralizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (x : G) (hx : x ∈ twoCoreIn (EAt ctx.Γ middle)) (hx2 : x^2≠1) :
    QAt ctx.Γ middle ⊓ Subgroup.centralizer ({x} : Set G) =
      twoCoreIn (EAt ctx.Γ middle) := by
  let M := GAt ctx.Γ middle
  let E := twoResidualAmbient (⊤ : Subgroup M)
  let Q := pCore 2 M
  let R := E ⊓ Q
  let D := twoCoreIn (EAt ctx.Γ middle)
  let Qm := QAt ctx.Γ middle
  let _ : E.Normal := by
    dsimp only [E]
    rw [SectionThree.twoResidualAmbient_top_eq_hktPResidual]
    exact BenderSuzuki.External.hktPResidual_normal
  obtain ⟨hcenter,hc4,himage⟩ := ten_one_small_middle_bound_inputs ctx middle hpath hsmall hmodel
  have hEmap : E.map M.subtype = EAt ctx.Γ middle := by
    have hm := map_twoResidualAmbient_of_subgroup_image (⊤ : Subgroup M) M.subtype M
      (by rw [← MonoidHom.range_eq_map,Subgroup.range_subtype])
    exact hm.trans (ctx.Γ.twoResidualAt_def middle).symm
  have hQmap : Q.map M.subtype = Qm := (ctx.Γ.twoCoreAt_def middle).symm
  have hRmap : R.map M.subtype = D := by
    rw [Subgroup.map_inf E Q M.subtype M.subtype_injective,hEmap,hQmap]
    change ctx.Γ.twoResidualAt middle ⊓ ctx.Γ.twoCoreAt middle =
      twoCoreIn (ctx.Γ.twoResidualAt middle)
    rw [ctx.Γ.twoResidualAt_def,ctx.Γ.twoCoreAt_def,residual_core_eq_inter_core]
  obtain ⟨r,hr,hrx⟩ := (show x ∈ R.map M.subtype from hRmap.symm ▸ hx)
  change (r:G)=x at hrx
  let rR : R := ⟨r,hr⟩
  have hr2 : rR^2 ≠ 1 := by
    intro hh
    apply hx2
    have hh' := congrArg (fun z : R => ((z:M):G)) hh
    change (r:G)^2=1 at hh'
    rwa [hrx] at hh'
  have hcentralizer := inf_centralizer_singleton_eq_of_centerfree_c4_square_primitive
    (default : Sylow 2 M) E Q (twoResidualAmbient_top_sup_sylow _)
      (pCore_isPGroup (p:=2) (G:=M)) hcenter hc4 himage rR hr2
  change Qm ⊓ Subgroup.centralizer ({x} : Set G) = D
  apply le_antisymm
  · intro q hq
    obtain ⟨qM,hqM,hqeq⟩ := (show q ∈ Q.map M.subtype from hQmap.symm ▸ hq.1)
    change (qM:G)=q at hqeq
    have hqc : qM ∈ Subgroup.centralizer ({r} : Set M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hs' : s=r := Set.mem_singleton_iff.mp hs
      subst s
      apply Subtype.ext
      change (r:G)*(qM:G)=(qM:G)*(r:G)
      rw [hrx,hqeq]
      exact Subgroup.mem_centralizer_iff.mp hq.2 x (Set.mem_singleton _)
    have hqR : qM∈R := hcentralizer.le ⟨hqM,hqc⟩
    rw [← hRmap]
    exact ⟨qM,hqR,hqeq⟩
  · intro q hq
    have hqQ : q ∈ Qm := by
      rw [← hQmap]
      apply Subgroup.map_mono (show R≤Q from inf_le_right)
      exact hRmap.symm ▸ hq
    refine ⟨hqQ,?_⟩
    change q ∈ Subgroup.centralizer ({x} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y=x := Set.mem_singleton_iff.mp hy
    subst y
    obtain ⟨equiv⟩ := hc4
    let _ : CommGroup R := equiv.toMonoidHom.commGroupOfInjective equiv.injective
    let _ : IsMulCommutative D := by rw [← hRmap]; infer_instance
    exact setLike_mul_comm (s:=D) hx hq

public theorem ten_one_small_primitive_wstar_centralizer
    (ctx : AmbientSectionTenContext H S0 S P1 P2 embedding T A B)
    (middle : ctx.Γ.Vertex)
    (hpath : IsCriticalPathOffset ctx.Γ ctx.criticalPath 2 middle)
    (hsmall : Nat.card (VAt ctx.Γ ctx.criticalPath.firstStep) = 8)
    (hmodel : QuotientIsModel (GAt ctx.Γ ctx.criticalPath.firstStep)
      (QAt ctx.Γ ctx.criticalPath.firstStep) SL2Two)
    (x : G) (hx : x ∈ twoCoreIn (EAt ctx.Γ middle)) (hx2 : x^2≠1) :
    let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
      GeneratedNeighborhoodV ctx.Γ middle
    let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
    Wstar ⊓ Subgroup.centralizer ({x} : Set G) = ZAt ctx.Γ middle := by
  let W0 := NeighborhoodQIntersection ctx.Γ (Neighborhood ctx.Γ middle) ⊓
    GeneratedNeighborhoodV ctx.Γ middle
  let Wstar := QAt ctx.Γ middle ⊓ Subgroup.centralizer (W0 : Set G)
  have hWD : Wstar ⊓ twoCoreIn (EAt ctx.Γ middle) = ZAt ctx.Γ middle :=
    (ten_one_small_centralizer_elementary ctx middle hpath hsmall hmodel).2.2.2.1
  change Wstar ⊓ Subgroup.centralizer ({x} : Set G) = ZAt ctx.Γ middle
  rw [← hWD,← ten_one_small_primitive_middle_centralizer ctx middle hpath hsmall hmodel x hx hx2,
    ← inf_assoc,inf_eq_left.mpr (show Wstar ≤ QAt ctx.Γ middle from inf_le_left)]

end Stellmacher.SectionTen
