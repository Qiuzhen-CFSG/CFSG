module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneProfile
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneSourceMarking
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneApartmentRoots
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Selecting whole-Cartan reflections from the original natural actors

The neighbor center maps onto the marked SL₂ Sylow, so it has an element
outside the endpoint core. Lift that element through the actual universal
endpoint isomorphism. The covering preserves the full edge intersection;
restriction of its injective edge map carries the edge radical to the
original edge radical. Thus the lift belongs to the actual edge path root.
The proved whole-Cartan selection then constructs a moving involution,
including centralization of the Cartan part of the full local kernel.

Original parabolic nonsolvability excludes the two-element field: its SL₂
quotient would be solvable, hence so would the actor, its original local
factor and the original parabolic. No field-size premise is added to that
consumer. These reflections feed the long-path construction in BOneApartment.
We do not assert conjugacy to an element of each later long-path root;
the central correction and that further source fusion issue remain separate.

Source: DGS, Groups and Graphs (1985), (10.5), pp.156--157, and
(14.1)--(14.2), pp.210--211.
-/

open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open Subgroup.CosetGeometry.RankTwo hiding base

public noncomputable section
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
variable {G F W : Type*} [Group G] [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
private def edgePath (i : Bool) : (sourceGraph (reducedAmalgam L S)).Walk
    (base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (base (Universal.cosetFamily (reducedAmalgam L S)) i) :=
  SimpleGraph.Walk.cons
    ⟨by change (!i) ≠ i; cases i <;> decide, incident_base _ _ _⟩ .nil

private theorem edgePath_fixer (i : Bool) : pathFixer (X := (reducedAmalgam L S).Universal) (edgePath (L := L) (S := S) i) =
    Universal.cosetFamily (reducedAmalgam L S) i ⊓ Universal.cosetFamily (reducedAmalgam L S) (!i) := by
  ext x
  have mem_fix (j : Bool) : x ∈ Universal.cosetFamily (reducedAmalgam L S) j ↔
      x • base (Universal.cosetFamily (reducedAmalgam L S)) j =
        base (Universal.cosetFamily (reducedAmalgam L S)) j := by
    rw [←Subgroup.CosetGeometry.stabilizer_base (Universal.cosetFamily (reducedAmalgam L S)) j]
    rfl
  constructor
  · intro hx
    have h0 := hx 0 (by change 0 ≤ 1; decide)
    have h1 := hx 1 (by change 1 ≤ 1; decide)
    exact ⟨(mem_fix i).mpr h1,(mem_fix (!i)).mpr h0⟩
  · rintro ⟨hx,hx'⟩ n hn
    change n ≤ 1 at hn
    interval_cases n
    · exact (mem_fix (!i)).mp hx'
    · exact (mem_fix i).mp hx

variable (h : HypothesisF11 L S) (i : Bool)
  (d : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
    (base (reducedFamily L S) (!i)) F W)

private theorem neighbor_escapes : ∃ x : d.actor,
    (x : G₀ L S) ∈ Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ∧
    (x : G₀ L S) ∉ Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  let e := Matrix.SpecialLinearGroup.sylowEquivAdditive F 2 d.imageSylow
  let s : d.imageSylow := e (Multiplicative.ofAdd (1 : F))
  have hs : (s : SL(2,F)) ≠ 1 := by
    intro he
    have he' : s = 1 := Subtype.ext he
    have hh := congrArg e.symm he'
    simp [s] at hh
  have hm : (s : SL(2,F)) ∈ ((Z (reducedFamily L S)
      (base (reducedFamily L S) (!i))).subgroupOf d.actor).map d.quotient := by
    rw [d.neighbor_image]
    exact s.property
  obtain ⟨x,hx,hxs⟩ := hm
  refine ⟨x,hx,?_⟩
  intro hxQ
  have hk : x ∈ d.quotient.ker := d.kernel.symm ▸ hxQ
  exact hs (hxs.symm.trans hk)

private theorem universal_neighbor_escapes : ∃ x : universalBOneActor h i d,
    (x : (reducedAmalgam L S).Universal) ∈ pathRoot (X := (reducedAmalgam L S).Universal)
      (edgePath (L := L) (S := S) i) ∧
    bOne_tree_map h x ∈ Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ∧
    bOne_tree_map h x ∉ Q (reducedFamily L S) (base (reducedFamily L S) i) := by
  obtain ⟨y,hyZ,hyQ⟩ := neighbor_escapes i d
  let e := universalBOneActorEquiv h i d
  let x := e.symm y
  have he : bOne_tree_map h x = (y : G₀ L S) :=
    congrArg Subtype.val (e.apply_symm_apply y)
  have hxZ : bOne_tree_map h x ∈ Z (reducedFamily L S)
      (base (reducedFamily L S) (!i)) := he ▸ hyZ
  have hxQ : bOne_tree_map h x ∉ Q (reducedFamily L S)
      (base (reducedFamily L S) i) := he ▸ hyQ
  let A := reducedAmalgam L S
  let C := Universal.cosetFamily A i ⊓ Universal.cosetFamily A (!i)
  let f := bOne_tree_map h
  let cov := bOne_tree_cover h
  have hx : (x : A.Universal) ∈ C := by
    refine ⟨x.property.2,cov.mem_of_mem_image i x.property.2 ?_⟩
    simpa only [RankTwo.stabilizer,RankTwo.base,Subgroup.CosetGeometry.stabilizer_base] using
      Z_le_stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i)) hxZ
  have hxcore : f x ∈ (C.map f).pCoreIn 2 := by
    rw [cov.map_inf_pair]
    have hZQ : Z (reducedFamily L S) (base (reducedFamily L S) (!i)) ≤
        Q (reducedFamily L S) (base (reducedFamily L S) (!i)) :=
      ((source_Z_Q_U (reduced_triple h) _).1).trans (map_subtype_le _)
    have hh := Noncommuting.graph_Q_le_edgeCore (reduced_triple h) d.adjacent.symm (hZQ hxZ)
    change f x ∈ (MulAction.stabilizer (G₀ L S) (base (reducedFamily L S) (!i)) ⊓
      MulAction.stabilizer (G₀ L S) (base (reducedFamily L S) i)).pCoreIn 2 at hh
    rw [Subgroup.CosetGeometry.stabilizer_base, Subgroup.CosetGeometry.stabilizer_base] at hh
    simpa only [inf_comm] using hh
  have hinj : Function.Injective (f.domRestrict C) := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : Universal.cosetFamily A i => (z : A.Universal))
      (cov.injective i (a₁ := ⟨a,a.property.1⟩) (a₂ := ⟨b,b.property.1⟩) hab)
  have hrange : (f.domRestrict C).range = C.map f := by
    change (f.comp C.subtype).range = C.map f
    rw [MonoidHom.range_comp,range_subtype]
  rw [←hrange, pCoreIn_range_of_injective 2 (f.domRestrict C) hinj] at hxcore
  obtain ⟨z,hz,hzx⟩ := hxcore
  have hzxe : z = ⟨x,hx⟩ := hinj hzx
  refine ⟨x,?_,hxZ,hxQ⟩
  rw [pathRoot,edgePath_fixer]
  exact ⟨⟨x,hx⟩,hzxe ▸ hz,rfl⟩


include h in
/-- Nonsolvability of the original parabolic forces a nonbinary natural field. -/
theorem field_gt_two_of_nonsolvable
    (ha : d.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (hns : ¬ Group.IsSolvable (parabolic L S (if i then 1 else 0))) : 2 < Nat.card F := by
  by_contra hsmall
  have hF : Nat.card F = 2 := by have := Finite.one_lt_card (α := F); omega
  let : Fintype F := Fintype.ofFinite F
  let e := ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let f := Matrix.SpecialLinearGroup.map (n := Fin 2) e.symm.toRingHom
  have hf : Function.Injective f := by
    intro a b hab
    ext j k
    exact e.symm.injective (congrArg (fun z : SL(2,ZMod 2) => z.val j k) hab)
  let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
  let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Group.isSolvable_of_isSolvable_injective
      (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
  let : Group.IsSolvable SL(2,ZMod 2) := Group.isSolvable_of_isSolvable_injective
    (f := SLTwoPermThree.sl2Two_equiv_perm_three.some.toMonoidHom)
    SLTwoPermThree.sl2Two_equiv_perm_three.some.injective
  let : Group.IsSolvable SL(2,F) := Group.isSolvable_of_isSolvable_injective hf
  let : ∀ j, Finite (reducedFamily L S j) := finite_endpoints (reduced_triple h)
  let : Finite (stabilizer (reducedFamily L S) (base (reducedFamily L S) i)) := by
    change Finite (MulAction.stabilizer (G₀ L S) (base (reducedFamily L S) i))
    rw [stabilizer_base]
    infer_instance
  let : Finite d.actor := Finite.of_injective (inclusion d.actor_le) (inclusion_injective _)
  have hk : IsPGroup 2 d.quotient.ker := by
    rw [d.kernel]
    exact (isPGroup_pCoreIn 2 (stabilizer (reducedFamily L S)
      (base (reducedFamily L S) i))).of_equiv (subgroupOfEquivOfLe d.core_le).symm
  let : Group.IsNilpotent d.quotient.ker := hk.isNilpotent
  let : Group.IsSolvable d.actor := Group.isSolvable_of_ker_le_range
    d.quotient.ker.subtype d.quotient (by rw [range_subtype])
  let a := d.actor.equivMapOfInjective (G₀ L S).subtype (G₀ L S).subtype_injective
  let : Group.IsSolvable (d.actor.map (G₀ L S).subtype) :=
    Group.isSolvable_of_surjective (f := a.toMonoidHom) a.surjective
  have hL : L (if i then 1 else 0) ≤ d.actor.map (G₀ L S).subtype := by
    rw [ha,subgroupOf_map_subtype]
    refine le_inf ((local_le_starredParabolic _).trans le_sup_right) ?_
    cases i
    · exact (local_le_starredParabolic 0).trans (le_sup_left.trans le_sup_left)
    · exact (local_le_starredParabolic 1).trans (le_sup_left.trans le_sup_right)
  let : Group.IsSolvable (L (if i then 1 else 0)) :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hL)
  exact hns ((h.parabolic_solvable_iff_local_quotient _).mpr inferInstance)

/-- Select an actual moving involution normalizing the whole Cartan; no
root-element or diagonal-coordinate witness is assumed. -/
theorem exists_full_cartan_reflection
    (c : CompatibleCartans L (reducedSylow L S))
    (ha : d.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) i) =
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hneighbor : Q (reducedFamily L S) (base (reducedFamily L S) (!i)) =
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (E : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      W ≃ₗ[ZMod 2] (Fin 2 → F)) (hF : 2 < Nat.card F) :
    ∃ t : (reducedAmalgam L S).Universal,
      t ∈ universalBOneActor h i d ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) i =
        base (Universal.cosetFamily (reducedAmalgam L S)) i ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      t*t = 1 ∧ orderOf t = 2 ∧
      t ∈ normalizer (cartan c : Set (reducedAmalgam L S).Universal) ∧
      ∀ z ∈ cartan c, z ∈ RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute t z := by
  classical
  have hpair : ({0,1} : Set F).ncard ≤ 2 := by
    simp
  have hc : ({0,1} : Set F).ncard < (Set.univ : Set F).ncard := by
    rw [Set.ncard_univ]
    omega
  obtain ⟨b,_,hb⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hc
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hb
  obtain ⟨x,hxR,hxZ,hxQ⟩ := universal_neighbor_escapes h i d
  obtain ⟨t,ht,hfix,hmove,hsq,ho,hn,_,hcentral⟩ :=
    source_bOne_full_cartan_reflection_of_neighbor h c i d ha hcore hneighbor E
      b hb.1 hb.2 (edgePath (L := L) (S := S) i) x hxR hxZ hxQ
  exact ⟨t,ht,hfix,hmove,hsq,ho,hn,hcentral⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
