module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveHexagon.SixPath

/-!
# The genuine source actor carrying the base point to the fourth point

The right long-root label moves the left endpoint a distance four. The
only new nonbacktracking test lies in the first endpoint and follows from
its literal order-twenty quotient. Nine-path transitivity then supplies
an actual conjugating element, and the point labels determine the actor's
conjugation on z, u and zu. No recognition or smallness is assumed.
Source: the final proof of J.4.7, printed p.444.
-/

public section
namespace CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
open Subgroup Theory.GroupTheory
open Tits.ExceptionalParabolics.FullRee Tits.ExceptionalParabolics.FullRee.LongRootPaths
open ChapterF.SourceCompletion.BinaryRee
open Subgroup.CosetGeometry.RankTwo SimpleGraph SimpleGraph.BasedWalk
open SimpleGraph.PathTransitivePolygon
open MarkedInverter
open ReeTwo ParabolicMarkedComparison Tits.AmalgamRigidity.FullRee
noncomputable section
set_option maxRecDepth 2000
private theorem conjugate_root_not_middle :
    leftReflection⁻¹*modelU*leftReflection ∉ amalgam.left.range := by
  rintro ⟨t,ht⟩
  obtain ⟨k,rfl⟩ := borelEquiv.surjective t
  have he : SylowModel.embedding k=Centralizer.weyl⁻¹*Centralizer.rootOne^2*Centralizer.weyl := by
    apply Verified.firstEquiv.injective
    rw [map_mul,map_mul,map_inv,map_pow]
    have hU : modelU=Verified.firstEquiv (Centralizer.rootOne^2) := by
      calc
        modelU=amalgam.left (middleRootOne^2) := modelU_middle
        _=(amalgam.left middleRootOne)^2 := map_pow _ _ _
        _=(Verified.firstEquiv Centralizer.rootOne)^2 := by
          apply congrArg (fun x:first=>x^2)
          apply Subtype.ext
          change (middleRootOne : ReeF4.Model 0)=(Verified.firstEquiv Centralizer.rootOne : ReeF4.Model 0)
          rw [Verified.firstEquiv_coe,Verified.localMap_rootOne]
          exact SecondExtension.inclusion_rootOne
        _=Verified.firstEquiv (Centralizer.rootOne^2) := (map_pow _ _ _).symm
    rw [hU,map_pow] at ht
    exact ht
  let y : FirstRestrictions.E :=
    (SemidirectProduct.inr FiveFour.r)⁻¹*(FirstRestrictions.fromS SylowModel.rootOne)^2*
      SemidirectProduct.inr FiveFour.r
  have hn : y∉FirstRestrictions.fromS.range := by
    rw [PointedPairs.mem_firstB_iff]
    decide +kernel
  apply hn
  refine ⟨k,?_⟩
  apply FirstRestrictions.equiv.injective
  rw [FirstRestrictions.equiv_fromS,he]
  dsimp [y]
  rw [map_mul,map_mul,map_inv,map_pow,FirstRestrictions.equiv_fromS,
    SylowModel.embedding_rootOne]
  have hr : FirstRestrictions.equiv (SemidirectProduct.inr FiveFour.r)=Centralizer.weyl := by
    change SemidirectProduct.inr (Core.complementEquiv FiveFour.r)=Centralizer.weyl
    rw [Core.complementEquiv_r]
    rfl
  rw [hr]

variable {K:Type*} [Group K] (q:Completion K)
private theorem conjugate_root_not_right :
    (leftActor q)⁻¹*q.left modelU*leftActor q ∉ q.right.range := by
  intro h
  have he:(leftActor q)⁻¹*q.left modelU*leftActor q=
      q.left (leftReflection⁻¹*modelU*leftReflection) := by simp only [map_mul,map_inv,leftActor]
  rw [he] at h
  have hm : q.left (leftReflection⁻¹*modelU*leftReflection)∈q.middle.range :=
    completion_overlap q ▸ ⟨⟨_,rfl⟩,h⟩
  obtain ⟨t,ht⟩ := hm
  exact conjugate_root_not_middle ⟨t,q.left_injective ht⟩

private theorem rightActor_inv : (rightActor q)⁻¹=rightActor q := by
  have h : rightReflection^2=1 := by
    apply Subtype.ext
    change (rightReflection:ReeF4.Model 0)^2=1
    rw [rightReflection_coe,←map_pow]
    have hr : (Atlas.a .r8)^2=1 := by
      simpa only [Atlas.a,Tits.parrottRelator,map_pow,FreeGroup.lift_apply_of] using
        Tits.atlas1600ParrottAssignment_relations .i_r8
    rw [hr,map_one]
  exact inv_eq_of_mul_eq_one_left (by simpa only [rightActor,map_pow,pow_two,map_one,map_mul] using congrArg q.right h)

theorem moved_six_left_distance :
    q.graph.dist (completionLeftWord q • basePoint q)
      (q.left modelU • (completionLeftWord q • basePoint q))=4 := by
  let a:K := (leftActor q)⁻¹*q.left modelU*leftActor q
  have ha:a∈q.family false := ⟨leftReflection⁻¹*modelU*leftReflection,by simp only [map_mul,map_inv];rfl⟩
  have hb:rightActor q∈q.family true := ⟨rightReflection,rfl⟩
  have hd := q.four_path_geodesic (alternatingFour q.family a (rightActor q) ha hb)
    (alternatingFour_nonbacktracking q.family a (rightActor q) ha hb
      (conjugate_root_not_right q) (completion_right_not_left q))
  change q.graph.dist (basePoint q) ((rightActor q*a*rightActor q)•basePoint q)=4 at hd
  have he := q.graphAction.dist_smul (completionLeftWord q)⁻¹
    (completionLeftWord q•basePoint q) (q.left modelU•(completionLeftWord q•basePoint q))
  simp only [←mul_smul,inv_mul_cancel,one_smul] at he
  have hw : (completionLeftWord q)⁻¹*(q.left modelU*completionLeftWord q)=
      rightActor q*a*rightActor q := by
    dsimp [completionLeftWord,a,leftActor,rightActor]
    rw [mul_inv_rev]
    have hb':(q.right rightReflection)⁻¹=q.right rightReflection := rightActor_inv q
    rw [hb']
    group
  rw [hw] at he
  simpa only [mul_smul] using he.symm.trans hd

private theorem fixes_label (g:K) (hg:g•basePoint q=basePoint q) :
    g*centralRoot q*g⁻¹=centralRoot q := by
  have hm:g∈q.left.range := by
    have h:g∈stabilizer q.family (basePoint q) := hg
    simpa only [stabilizer,base,Subgroup.CosetGeometry.stabilizer_base,Completion.family_false] using h
  have hc:=completion_root_centralizes q hm
  change g∈centralizer {q.left (amalgam.left (middleRoot 9))} at hc
  rw [←modelZ_middle] at hc
  exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp hc)

private theorem same_vertex_label (g h:K) (he:g•basePoint q=h•basePoint q) :
    g*centralRoot q*g⁻¹=h*centralRoot q*h⁻¹ := by
  have hr:=fixes_label q (h⁻¹*g) (by rw [mul_smul,he,inv_smul_smul])
  calc
    _=h*((h⁻¹*g)*centralRoot q*(h⁻¹*g)⁻¹)*h⁻¹ := by group
    _=_ := by rw [hr]

theorem exists_six_actor : ∃ a j:K,
    a•(completionLeftWord q•basePoint q)=basePoint q ∧
    a•(q.left modelU•(completionLeftWord q•basePoint q))=
      completionFourthWord q•basePoint q ∧
    j=a*q.left modelU*a⁻¹ ∧
    j•basePoint q=completionFourthWord q•basePoint q ∧
    j*centralRoot q*j⁻¹=q.left modelU ∧
    j*(centralRoot q*q.left modelU)*j⁻¹=centralRoot q*q.left modelU ∧
    a*(completionLeftWord q*centralRoot q*(completionLeftWord q)⁻¹)*a⁻¹=centralRoot q := by
  let L:=completionLeftWord q
  let U:=q.left modelU
  have hd : q.graph.dist (basePoint q) ((L⁻¹*U*L)•basePoint q)=4 := by
    have hh:=q.graphAction.dist_smul L⁻¹ (L•basePoint q) (U•(L•basePoint q))
    simp only [←mul_smul,inv_mul_cancel,one_smul] at hh
    rw [mul_assoc] at ⊢
    exact hh.trans (by simpa only [mul_smul] using moved_six_left_distance q)
  have htwo : HasTwoNeighbors q.graph := by
    intro v w
    obtain ⟨z,hz,hzw,_⟩:=q.thick v w w
    exact ⟨z,hz,hzw⟩
  have ht:=((q.nine_transitive (basePoint q)).mono htwo (by decide : 4≤9)).sphereTransitive q.graphAction q.connected
  obtain ⟨k,hkx,hky⟩:=ht _ _ hd (four_point_distance q)
  let a:=k*L⁻¹
  let j:=a*U*a⁻¹
  have ha:a•(L•basePoint q)=basePoint q := by simpa only [a,mul_smul,inv_smul_smul] using hkx
  have hay:a•(U•(L•basePoint q))=completionFourthWord q•basePoint q := by
    simpa only [a,mul_smul] using hky
  have hj:j•basePoint q=completionFourthWord q•basePoint q := by
    calc
      j•basePoint q=j•(a•(L•basePoint q)) := congrArg (fun v=>j•v) ha.symm
      _=_ := by simpa only [j,mul_smul,inv_smul_smul] using hay
  have hl:a*(L*centralRoot q*L⁻¹)*a⁻¹=centralRoot q := by
    have hh:=same_vertex_label q (a*L) 1 (by simpa only [mul_smul,one_smul] using ha)
    simpa only [mul_inv_rev,mul_assoc,one_mul,inv_one,mul_one] using hh
  have hjz:j*centralRoot q*j⁻¹=U := by
    have hh:=same_vertex_label q j (completionFourthWord q) hj
    rw [centralRoot,modelZ_middle] at hh
    change j*centralRoot q*j⁻¹=q.left modelU
    rw [modelU_middle,centralRoot,modelZ_middle]
    exact hh.trans (completion_conjugates q)
  have hU:U^2=1 := by
    have hh:=pow_orderOf_eq_one U
    rw [(marked_four_point q).2.1] at hh
    exact hh
  have hj2:j^2=1 := by
    calc
      j^2=a*U^2*a⁻¹ := by dsimp [j];simp only [pow_two];group
      _=1 := by rw [hU];group
  have hji:j⁻¹=j := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hj2)
  have hjU:j*U*j⁻¹=centralRoot q := by rw [←hjz,hji];calc
    _=(j*j)*centralRoot q*(j*j) := by group
    _=_ := by rw [←pow_two,hj2,one_mul,mul_one]
  have hc:Commute (centralRoot q) U := by
    have hh:=completion_root_centralizes q (show U∈q.left.range from ⟨modelU,rfl⟩)
    change U∈centralizer {q.left (amalgam.left (middleRoot 9))} at hh
    rw [←modelZ_middle] at hh
    exact (mem_centralizer_singleton_iff.mp hh).symm
  refine ⟨a,j,ha,hay,rfl,hj,hjz,?_,hl⟩
  calc
    j*(centralRoot q*U)*j⁻¹=(j*centralRoot q*j⁻¹)*(j*U*j⁻¹) := by group
    _=centralRoot q*U := by rw [hjz,hjU,hc.eq]

end
end CFSG.Quasithin.ChapterJ.RuSubgroup.FiveHexagon.PathTransport
