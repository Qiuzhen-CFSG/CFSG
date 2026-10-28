module

public import CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightTreeNormalizer
public import Theory.GroupTheory.QuotientKernelComplement

/-!
# Correcting the chosen original eight reflection inside its half-path actor

The same two half-path roots complement the full original eight core. Their
normalizer has only the original central involution as excess. On the same
tree that excess fixes the three-ball, so projecting the chosen reflection
into the literal half-path actor retains the neighbor and Cartan actions.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Subgroup.CosetGeometry Theory.GroupTheory.WeakBNPair.RegularTree
namespace CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightReflectionChange
open ChapterF.Source ChapterF.Source.SuzukiContainment ChapterF.Source.DGS85
open OriginalExtension Reduction NoncommutingProfile
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReducedCartan
section Geometry
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "A" => reducedAmalgam L S
local notation "F" => reducedFamily L S
local notation "UP" => Universal.cosetFamily A

private theorem half_complement_in_stabilizer (h : HypothesisF11 L S)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) (hl : p.length=12)
    (hfull : graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6))=
      RankTwo.stabilizer F ((bOne_tree_cover h).vertex (p.getVert 6)))
    (hcomp : (pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))).IsComplement'
      (halfPathLocalMap h p 6 hl).range) :
    (pCore 2 (RankTwo.stabilizer UP (p.getVert 6))).IsComplement'
      ((halfPathActor (X := (A).Universal) p 6).subgroupOf
        (RankTwo.stabilizer UP (p.getVert 6))) := by
  let P := RankTwo.stabilizer UP (p.getVert 6)
  let D := halfPathActor (X := (A).Universal) p 6
  let R := D.subgroupOf P
  let g := ((bOne_tree_cover h).stabilizerEquiv (p.getVert 6)).trans
    (MulEquiv.subgroupCongr hfull.symm)
  have hDP : D≤P := halfPathActor_le_midpoint_stabilizer hl
  have hr : R.map g.toMonoidHom=(halfPathLocalMap h p 6 hl).range := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact ⟨⟨y,hy⟩,rfl⟩
    · rintro ⟨y,rfl⟩
      exact ⟨⟨y,hDP y.property⟩,y.property,rfl⟩
  have hd : Disjoint (pCore 2 P) g.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr g.injective]
    exact disjoint_bot_right
  have hh := QuotientKernelComplement.complement_comap g.toMonoidHom (pCore 2 P)
    (R.map g.toMonoidHom) hd (by rw [pCore_map_iso,hr]; exact hcomp)
  rwa [comap_map_eq_self_of_injective g.injective] at hh

private theorem complement_subgroupOf_congr {X : Type*} [Group X]
    (D P Q : Subgroup X) (he : P=Q)
    (h : (pCore 2 P).IsComplement' (D.subgroupOf P)) :
    (pCore 2 Q).IsComplement' (D.subgroupOf Q) := by
  subst Q
  exact h

private theorem correction_frame (h : HypothesisF11 L S) (H : Subgroup G)
    (hactor : graphLocalGroup F (RankTwo.base F true)=RankTwo.stabilizer F (RankTwo.base F true))
    (hN : SourceEightTreeNormalizer.HasEightTreeNormalizer h H)
    (c : CompatibleCartans L (reducedSylow L S)) (d : SixPathSmallActorGeometry c)
    {a b : SourceVertex A} (p : (sourceGraph A).Walk a b) (hl : p.length=12)
    (hmid : p.getVert 6=base UP true)
    (hC : cartan c≤halfPathActor (X := (A).Universal) p 6)
    (hrev : ∀ k≤12, d.reflection true • p.getVert k=p.getVert (12-k))
    (hcomp : (pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))).IsComplement'
      (halfPathLocalMap h p 6 hl).range) :
    ∃ J : Subgroup (A).Universal,
      halfPathActor (X := (A).Universal) p 6≤J ∧ cartan c≤J ∧
      centerIn J ⊓ halfPathActor (X := (A).Universal) p 6=⊥ ∧
      d.reflection true∈centerIn J ⊔ halfPathActor (X := (A).Universal) p 6 ∧
      centerIn J≤graphBallFixer (sourceGraph A) (base UP true) 3 := by
  let P := RankTwo.stabilizer UP (base UP true)
  let D := halfPathActor (X := (A).Universal) p 6
  let R := D.subgroupOf P
  have hDP : D≤P := by
    intro x hx
    change x • base UP true=base UP true
    rw [←hmid]
    exact halfPathActor_le_midpoint_stabilizer hl hx
  have hfull : graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6))=
      RankTwo.stabilizer F ((bOne_tree_cover h).vertex (p.getVert 6)) := by
    rw [hmid,(bOne_tree_cover h).vertex_base]
    exact hactor
  have hR : (pCore 2 P).IsComplement' R := by
    have hh := half_complement_in_stabilizer h p hl hfull hcomp
    exact complement_subgroupOf_congr D _ P
      (congrArg (RankTwo.stabilizer UP) hmid) hh
  obtain ⟨j,_,hNs⟩ := hN
  obtain ⟨hn,hz,hd,hball⟩ := hNs R hR
  let Z := (centerIn (H.pCoreIn 2)).comap (H.subtype.comp j.toMonoidHom)
  let N := normalizer (R:Set P)
  let J := N.map P.subtype
  have hm : R.map P.subtype=D := map_subgroupOf_eq_of_le hDP
  have hJ : D≤J := hm ▸ map_mono (f := P.subtype) R.le_normalizer
  have hc : centerIn J=Z.map P.subtype := by
    change centerIn (N.map P.subtype)=_
    rw [centerIn_eq_map_center,map_center_image_of_injective _ _ P.subtype_injective,
      ←Subgroup.map_map,←centerIn_eq_map_center]
    exact congrArg (Subgroup.map P.subtype) hz
  have htD : d.reflection true∈normalizer (D:Set (A).Universal) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (pathRoot (X := (A).Universal) (p.drop 6) ⊔ pathRoot (X := (A).Universal) (p.take 6)).map _=_
    rw [Subgroup.map_sup]
    obtain ⟨ha,hb⟩ := pathRoot_halves_reflection p 6 hl (d.reflection true) hrev
    exact (congrArg₂ (fun R V : Subgroup (A).Universal => R ⊔ V) hb ha).trans (sup_comm _ _)
  have htN : (⟨d.reflection true,d.fixes true⟩:P)∈N := by
    change (⟨d.reflection true,d.fixes true⟩:P)∈normalizer (D.subgroupOf P:Set P)
    rw [←subgroupOf_normalizer_eq hDP]
    exact htD
  refine ⟨J,hJ,hC.trans hJ,?_,?_,?_⟩
  · rw [hc]
    change Z.map P.subtype ⊓ D=⊥
    rw [←hm,←map_inf _ _ _ P.subtype_injective,hd,Subgroup.map_bot]
  · have hh : d.reflection true∈J := mem_map_of_mem P.subtype htN
    have he : J=D ⊔ centerIn J := by
      change (normalizer (R:Set P)).map P.subtype=_
      rw [hn,Subgroup.map_sup,hm,hc]
    rw [he,sup_comm] at hh
    exact hh
  · rw [hc]
    exact hball

/-- The original chosen eight reflection is replaced inside its same literal
half-path actor; the opposite reflection, neighbor and Cartan actions, and
first four reverse-path vertices are retained. -/
@[expose] def HasEightReflectionChange (h : HypothesisF11 L S)
    (c : CompatibleCartans L (reducedSylow L S)) : Prop :=
  ∃ d : SixPathSmallActorGeometry c,
    (∀ i, Nonempty (BinarySixPathReflectionClass h i (d.reflection i))) ∧
    ∃ (a b : SourceVertex A) (p : (sourceGraph A).Walk a b) (_hp : p.IsPath) (hl : p.length=12),
      p.getVert 6=base UP true ∧ p.getVert 7=base UP false ∧
      (∀ z∈p.support,z∈cartanApartment A (reflectionGroup c d.reflection)) ∧
      (∀ k≤12,d.reflection true • p.getVert k=p.getVert (12-k)) ∧
      pCore 2 (halfPathActor (X := (A).Universal) p 6)=⊥ ∧
      (pCore 2 (graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 6)))).IsComplement'
        (halfPathLocalMap h p 6 hl).range ∧
      ∃ (t' : Bool → (A).Universal)
        (hf : ∀ i,t' i • base UP i=base UP i)
        (hm : ∀ i,t' i • base UP (!i)≠base UP (!i))
        (_hs : ∀ i,t' i*t' i=1)
        (hn : ∀ i,t' i∈normalizer (cartan c:Set (A).Universal)),
        t' true∈halfPathActor (X := (A).Universal) p 6 ∧ t' false=d.reflection false ∧
        (∀ i,t' i • base UP (!i)=d.reflection i • base UP (!i)) ∧
        (∃ z∈graphBallFixer (sourceGraph A) (base UP true) 3,
          d.reflection true=z*t' true ∧ z*z=1) ∧
        (∀ k∈cartan c,t' true*k*(t' true)⁻¹=d.reflection true*k*(d.reflection true)⁻¹) ∧
        (∀ n (hnn : 0<n) k,k≤n → k≤4 →
          (reflectionPath c t' hf hm hn n hnn true).walk.reverse.getVert k=
            (reflectionPath c d.reflection d.fixes d.moves d.normalizes n hnn true).walk.reverse.getVert k)

private theorem assemble (h : HypothesisF11 L S) (H : Subgroup G)
    (hactor : graphLocalGroup F (RankTwo.base F true)=RankTwo.stabilizer F (RankTwo.base F true))
    (hN : SourceEightTreeNormalizer.HasEightTreeNormalizer h H)
    (c : CompatibleCartans L (reducedSylow L S))
    (hhalf : SourceEightHalfActor.HasEightHalfActor h c) : HasEightReflectionChange h c := by
  obtain ⟨d,hclass,_,K,fK,finK,chK,_,em,hpaths,a,b,p,hp,hl,hmid,hnext,hT,hrev,_,hcore,_,hcomp,_⟩ := hhalf
  let _ := fK
  let _ := finK
  let _ := chK
  have hC : cartan c≤halfPathActor (X := (A).Universal) p 6 := by
    have hh := (hpaths p hp hl hT).2.2.2.2.2.2.1
    exact hh (by rw [hmid]; rfl)
  obtain ⟨J,hDJ,hCJ,hdis,htprod,hball⟩ := correction_frame h H hactor hN c d p hl hmid hC hrev hcomp
  obtain ⟨t',hf,hm,hs,hn,ht,ho,ha,⟨z,hz,hfactor,hz2⟩,hconj,_,hpath⟩ :=
    source_six_central_reflection_change c d.reflection d.fixes d.moves d.squares d.normalizes
      true J (halfPathActor (X := (A).Universal) p 6) hDJ hCJ hdis htprod hball
  exact ⟨d,hclass,a,b,p,hp,hl,hmid,hnext,hT,hrev,hcore,hcomp,t',hf,hm,hs,hn,
    ht,ho,ha,⟨z,hball hz,hfactor,hz2⟩,hconj,hpath⟩

end Geometry

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (eR : (pResidual 2 H ⧸ pCore 2 (pResidual 2 H)) ≃* Theory.PSL2.BinaryGroup 3)
include hG hempty hM hu hmany hcard e hH eR
local notation "Lₛ" => ![locals T M Mc H 1,locals T M Mc H 0]
local notation "Sₛ" => (T : Subgroup G)
local notation "Fₛ" => reducedFamily Lₛ Sₛ

set_option maxHeartbeats 800000 in
/-- The genuine original eight-field source supplies the compatible correction
inside its own marked half-path actor, without a reflection-placement input. -/
theorem source_eight_reflection_change
    (c : CompatibleCartans Lₛ (reducedSylow Lₛ Sₛ)) :
    HasEightReflectionChange
      (show HypothesisF11 Lₛ Sₛ from
        (source_hypothesis hG T hempty hM hu hmany hcard e H hH eR).1.swap) c := by
  exact assemble _ H
    (SourceEightTreeEndpoint.source_eight_tree_endpoint hG T hempty hM hu hmany hcard e H hH eR).2
    (SourceEightTreeNormalizer.source_eight_tree_normalizer hG T hempty hM hu hmany hcard e H hH eR) c
    (SourceEightHalfActor.source_eight_halfactor hG T hempty hM hu hmany hcard e H hH eR c)

end CFSG.Quasithin.Chapter14.Section02.EightLargeParabolic.SourceEightReflectionChange
