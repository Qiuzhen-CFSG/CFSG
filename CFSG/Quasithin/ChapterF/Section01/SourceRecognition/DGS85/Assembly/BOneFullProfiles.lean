module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneReflections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.Assembly.BOneActionMarking

/-!
# Full-Cartan profiles from the original b=1 critical pair

The original neighbor center surjects onto the marked SL₂ Sylow, so it
supplies a nontrivial involution outside the endpoint core. Its lift belongs
to the two-core of the actual universal edge stabilizer: the covering is
injective on that edge and preserves its whole intersection. Change matrix
coordinates once to put the neighbor Sylow in the upper unipotent group and the whole odd
Cartan on the diagonal. The inverse change in the representation preserves every
original action clause. This constructs all fields of both earlier
FullCartanReflectionProfile inputs from the original critical pair.

Original nonsolvability supplies the nonbinary scalars. BOneCriticalGeometry
uses these profiles in the r=3 exchange and faithful finite completion.
The seed path here is the original edge; no long-path alignment is asserted.
Long-root fusion uses the independently proved canonical-root theorem.
The Borel-image root signs and the other source branches remain necessary.

Source: DGS, Groups and Graphs (1985), (7.1), pp.126--127,
(10.5), pp.156--157, and (14.1)--(14.2), pp.210--211.
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
universe u
variable {G F W : Type u} [Group G] [Field F] [Finite F] [CharP F 2]
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


/-- Construct the earlier full-Cartan profile, including the exact matrix
marking and an actual involution in the original edge radical. -/
theorem full_cartan_profile_of_action
    (c : CompatibleCartans L (reducedSylow L S))
    (ha : d.actor = ((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (hneighbor : Q (reducedFamily L S) (base (reducedFamily L S) (!i)) =
      Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (E : letI : Algebra (ZMod 2) F := ZMod.algebra F 2
      W ≃ₗ[ZMod 2] (Fin 2 → F)) (hF : 2 < Nat.card F) :
    Nonempty (FullCartanReflectionProfile.{u} h c i) := by
  classical
  obtain ⟨m,hdiag,hfull,htri,hmS⟩ := exists_full_cartan_neighbor_marking h c i d ha hneighbor
  let e := MulAut.conj m
  let d' := d.marking e
  obtain ⟨x,hxR,hxZ,hxQ⟩ := universal_neighbor_escapes h i d
  let x' : universalBOneActor h i d' := x
  let π := universalBOneQuotient h i d'
  have hxS : d.quotient (universalBOneActorEquiv h i d x) ∈
      (d.imageSylow : Subgroup SL(2,F)) := by
    rw [←d.neighbor_image]
    exact mem_map_of_mem d.quotient hxZ
  have hxU : π x' ∈ Matrix.SpecialLinearGroup.upperUnipotent F :=
    hmS ▸ mem_map_of_mem e.toMonoidHom hxS
  obtain ⟨a,haimage⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent F (π x')).mp hxU
  have ha0 : a ≠ 0 := by
    intro he
    have hπone : π x' = 1 := by
      rw [←haimage,he,Matrix.SpecialLinearGroup.transvection_coeff_zero]
    have hxker : x ∈ (universalBOneQuotient h i d).ker := by
      change universalBOneQuotient h i d x = 1
      apply e.injective
      exact hπone.trans e.map_one.symm
    have hh : universalBOneActorEquiv h i d x ∈ d.quotient.ker := hxker
    rw [d.kernel] at hh
    exact hxQ hh
  have hxx : x' * x' = 1 := by
    apply (universalBOneActorEquiv h i d').injective
    apply Subtype.ext
    simpa only [map_mul,map_one,Subgroup.coe_mul,Subgroup.coe_one,
      universalBOneActorEquiv,coveredActorEquiv_apply,pow_two] using
      ((mem_omegaCenterIn_iff _ _).mp
        ((source_Z_Q_U (reduced_triple h) (base (reducedFamily L S) (!i))).1 hxZ)).2.2
  have hpair : ({0,1} : Set F).ncard ≤ 2 := by simp
  have hc : ({0,1} : Set F).ncard < (Set.univ : Set F).ncard := by
    rw [Set.ncard_univ]
    omega
  obtain ⟨b,_,hb⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard hc
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff,not_or] at hb
  exact ⟨{
    F := F
    W := W
    data := d'
    actor_eq := ha
    dimension := E
    diagonal := hdiag
    full_diagonal := hfull
    triangular := htri
    diagonal_parameter := b
    diagonal_ne_zero := hb.1
    diagonal_ne_one := hb.2
    start := base (Universal.cosetFamily (reducedAmalgam L S)) (!i)
    path := edgePath i
    path_isPath := by
      apply SimpleGraph.Walk.IsPath.nil.cons
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton]
      intro he
      have hh := congrArg (fun z : SourceVertex (reducedAmalgam L S) => z.type) he
      change (!i) = i at hh
      cases i <;> cases hh
    root_element := x'
    root_mem := hxR
    root_square := hxx
    root_parameter := a
    root_ne_zero := ha0
    root_image := haimage.symm }⟩

/-- Construct both earlier profiles from the unchanged nonsolvable
critical-pair hypotheses. Their fields, module coordinates, diagonal torus
markings and root involutions are all produced internally. -/
theorem full_cartan_profiles_of_critical_bOne
    (hns : ∀ j : Fin 2, ¬ Group.IsSolvable (parabolic L S j))
    {v w : RankTwo.Vertex (reducedFamily L S)}
    (hc : IsCriticalPair (reducedFamily L S) v w)
    (hne : ⁅Z (reducedFamily L S) v, Z (reducedFamily L S) w⁆ ≠ ⊥)
    (hb : b (reducedFamily L S) = 1)
    (c : CompatibleCartans L (reducedSylow L S)) :
    Nonempty (∀ j : Bool, FullCartanReflectionProfile.{u} h c j) := by
  obtain ⟨k₀,_,_,_,k₁,_,_,_,⟨p⟩⟩ := profile_of_nonsolvable_parabolics h hns hc hne hb
  let : Algebra (ZMod 2) k₀ := ZMod.algebra k₀ 2
  let : Algebra (ZMod 2) k₁ := ZMod.algebra k₁ 2
  obtain ⟨hQ₀,hQ₁⟩ := paired_cores_eq_centers_of_actions (reduced_triple h) p.left p.right
  obtain ⟨d₀⟩ := full_cartan_profile_of_action h false p.left c p.left_actor hQ₁ p.natural
    (field_gt_two_of_nonsolvable h false p.left p.left_actor (hns 0))
  obtain ⟨d₁⟩ := full_cartan_profile_of_action h true p.right c p.right_actor hQ₀
    (LinearEquiv.refl (ZMod 2) _)
    (field_gt_two_of_nonsolvable h true p.right p.right_actor (hns 1))
  exact ⟨fun j => by cases j; exact d₀; exact d₁⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BOneSource
