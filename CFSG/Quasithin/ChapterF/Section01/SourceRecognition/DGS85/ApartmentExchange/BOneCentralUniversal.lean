module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneCentralActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneUniversal

/-!
# Central-kernel actor reflections on the universal endpoints

The genuine Chapter 10 actor quotient may retain a central kernel in its
natural coordinates. Transport those coordinates through the actual universal
endpoint covering and apply the central-kernel reflection construction. The
result is a universal involution fixing one marked endpoint, moving the other,
and conjugate inside the lifted actor to the prescribed path-root involution.

The normalization conclusion is deliberately the Cartan intersection with the
lifted actor. Normalization by Cartan factors outside that actor, the remaining
Chapter 14 exchange alternatives, and quotient root signs remain separate
source obligations. In particular this module does not assert (14.19) or
Theorem D.

Source: DGS, *Groups and Graphs* (1985), (10.5), printed pp.155--157, the
universal tree convention p.208, and the reflection argument (14.2),
pp.210--211.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
open Theory.GroupTheory.WeakBNPair.RegularTree NaturalCubic Subgroup.CosetGeometry
open CFSG.Quasithin.ChapterF.Source
open CFSG.Quasithin.ChapterF.Source.SuzukiContainment
open CFSG.Quasithin.ChapterF.Source.DGS85
open OriginalExtension NoncommutingProfile Reduction
open Theory.GroupTheory.AmalgamGraph
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
namespace ReducedCartan
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable {F W : Type*} [Field F] [Finite F] [CharP F 2]
  [AddCommGroup W] [Module (ZMod 2) W]
variable (h : HypothesisF11 L S) (i : Bool)
variable (d : BOneActionData (reducedFamily L S) (base (reducedFamily L S) i)
  (base (reducedFamily L S) (!i)) F W)
local instance universalCentralAlgebra : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- Central natural coordinates on the actual lifted Chapter 10 actor. -/
def universalBOneNaturalCentralKernel
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) i)=
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F)) :
    NaturalCentralKernel (universalBOneQuotient h i d) :=
  (BOneActor.naturalCentralKernel (reduced_triple h) d hcore E).ofEquiv
    (universalBOneActorEquiv h i d)

private theorem central_middle_le (j : Bool) : originalMiddle (reducedAmalgam L S)≤
    Universal.cosetFamily (reducedAmalgam L S) j := by
  rw [originalMiddle,←Universal.overlap_eq _
    (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))]
  cases j
  · exact inf_le_left
  · exact inf_le_right

/-- Construct a central-kernel reflection on the universal endpoint.

The actor Cartan is retained explicitly in the normalizer conclusion; no
identification with the full endpoint quotient is used. -/
theorem source_bOne_central_actor_root_reflection
    (c : CompatibleCartans L (reducedSylow L S))
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) i)=
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    {v : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk v
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (x : universalBOneActor h i d)
    (hxR : (x:(reducedAmalgam L S).Universal)∈pathRoot (X := (reducedAmalgam L S).Universal) p)
    (hxZ : bOne_tree_map h x∈Z (reducedFamily L S) (base (reducedFamily L S) (!i)))
    (hxQ : bOne_tree_map h x∉Q (reducedFamily L S) (base (reducedFamily L S) i)) :
    ∃ t : (reducedAmalgam L S).Universal,
      t∈universalBOneActor h i d ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) i=
        base (Universal.cosetFamily (reducedAmalgam L S)) i ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      t*t=1 ∧ orderOf t=2 ∧
      t∈normalizer ((cartan c ⊓ universalBOneActor h i d : Subgroup (reducedAmalgam L S).Universal) : Set _) ∧
      (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) p,
        orderOf y=2 ∧ ∃ g∈universalBOneActor h i d, g*y*g⁻¹=t) := by
  let A := reducedAmalgam L S
  let H := universalBOneActor h i d
  let e := universalBOneActorEquiv h i d
  let K := (cartan c).subgroupOf H
  let K' := K.map e.toMonoidHom
  let := (reduced_hypothesis h).finite_commonBorel
  let : Finite (cartan c) := Finite.of_surjective
    ((middleMap L S).subgroupMap ((c.D 0⊔c.D 1).subgroupOf (commonBorel L (reducedSylow L S))))
    ((middleMap L S).subgroupMap_surjective _)
  let := cartan_abelian h c
  let : IsMulCommutative K := IsMulCommutative.of_comm fun y z => by
    apply Subtype.ext
    apply Subtype.ext
    exact setLike_mul_comm (show (y:H).val∈cartan c from y.property)
      (show (z:H).val∈cartan c from z.property)
  let : Group.IsSolvable K' := Group.isSolvable_of_comm (mul_comm' (M := K'))
  have hodd : Nat.Coprime 2 (Nat.card K') := by
    rw [card_map_of_injective e.injective]
    apply (cartan_odd c).of_dvd_right
    have he := card_map_of_injective (f := H.subtype) (K := K) H.subtype_injective
    rw [←he,subgroupOf_map_subtype]
    exact card_dvd_of_le inf_le_left
  have hK : ∀ k∈K', (k:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S)
      (base (reducedFamily L S) (!i)) := by
    rintro k ⟨y,hy,rfl⟩
    rw [RankTwo.stabilizer,stabilizer_base]
    change bOne_tree_map h y∈reducedFamily L S (!i)
    rw [←(bOne_tree_cover h).map_eq (!i)]
    exact mem_map_of_mem _ ((cartan_le c).trans (central_middle_le (!i)) hy)
  obtain ⟨t,_,htmove,htnorm,htsq,ho,g,hg⟩ :=
    BOneActor.exists_neighbor_center_reflection (reduced_triple h) d hcore E K' hK hodd
      (e x) hxZ hxQ
  let u := e.symm t
  have hu : e u=t := e.apply_symm_apply t
  have hfix : (u:A.Universal) • base (Universal.cosetFamily A) i=base (Universal.cosetFamily A) i := by
    have he := u.property.2
    rwa [←stabilizer_base (F := Universal.cosetFamily A) (i := i)] at he
  have hmove : (u:A.Universal) • base (Universal.cosetFamily A) (!i)≠base (Universal.cosetFamily A) (!i) := by
    intro he
    apply htmove
    have hm : (u:A.Universal)∈Universal.cosetFamily A (!i) := by
      rw [←stabilizer_base (F := Universal.cosetFamily A) (i := !i)]
      exact he
    have him : bOne_tree_map h u∈reducedFamily L S (!i) := by
      rw [←(bOne_tree_cover h).map_eq (!i)]
      exact mem_map_of_mem _ hm
    have heq : bOne_tree_map h u=(t:G₀ L S) := congrArg Subtype.val hu
    rw [heq] at him
    change (t:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S) (base (reducedFamily L S) (!i))
    rw [RankTwo.stabilizer,stabilizer_base]
    exact him
  have hnorm : u∈normalizer (K : Set H) := by
    have he := K'.le_normalizer_map e.symm.toMonoidHom
      (mem_map_of_mem e.symm.toMonoidHom htnorm)
    have heq : e.symm.toMonoidHom.comp e.toMonoidHom=MonoidHom.id H := by
      ext y : 1
      exact e.symm_apply_apply y
    have heK : K'.map e.symm.toMonoidHom=K := by
      dsimp only [K']
      rw [map_map,heq]
      exact Subgroup.map_id K
    rw [heK] at he
    exact he
  have hnorm' := K.le_normalizer_map H.subtype (mem_map_of_mem H.subtype hnorm)
  rw [subgroupOf_map_subtype] at hnorm'
  have hsq : u*u=1 := e.injective (by rw [map_mul,hu,htsq,map_one])
  have ho' : orderOf (u:A.Universal)=2 := by
    rw [Subgroup.orderOf_coe,←e.orderOf_eq u,hu]
    exact ho
  refine ⟨u,u.property,hfix,hmove,congrArg Subtype.val hsq,ho',hnorm',x,hxR,?_,e.symm g,(e.symm g).property,?_⟩
  · rw [Subgroup.orderOf_coe,←e.orderOf_eq x]
    have he := (MulAut.conj g).orderOf_eq (e x)
    change orderOf (g*e x*g⁻¹)=orderOf (e x) at he
    rw [hg] at he
    exact he.symm.trans ho
  · have he : e.symm g*x*(e.symm g)⁻¹=u := by
      apply e.injective
      simpa only [map_mul,map_inv,e.apply_symm_apply,hu] using hg
    exact congrArg H.subtype he

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
