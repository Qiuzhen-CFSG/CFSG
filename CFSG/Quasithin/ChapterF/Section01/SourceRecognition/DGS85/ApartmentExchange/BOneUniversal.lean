module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneActor
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.ReflectionSelection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.NoncommutingProfile.BOneTreeSource
public import Theory.GroupTheory.WeakBNPair.RegularTree.ActorCover

/-!
# Natural actor reflections on the marked universal endpoints

Lift the genuine Chapter 10 local actor through the existing covering of
the universal reduced amalgam. Restricting to its matching endpoint gives
an actual isomorphism, with the original covering map on every element.
The natural-kernel coordinates use its unchanged SL₂ quotient. Normalization
by the whole Cartan follows from the source Borel normalization theorem.

The actor reflection calculation now yields an actual universal involution,
normalizing the whole source Cartan, moving the other marked endpoint and
conjugate inside the same lifted actor to the prescribed path-root involution.
It also centralizes the Cartan part of the full radius-one kernel. No SL₂
identification of the full endpoint quotient is required.

This proves the transport and reflection deduction in the nonbinary,
trivial-actor-center branch, conditional on the literal diagonal and root
coordinate markings. Constructing those markings and the chosen root
involution, the binary and nontrivial-center cases, the remaining exchange
alternatives and quotient root signs remain source obligations.

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, the universal
tree convention p.208 and (14.2), pp.210--211.
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
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

private theorem actor_le_endpoint : d.actor≤reducedFamily L S i := by
  simpa only [RankTwo.stabilizer,stabilizer_base] using d.actor_le

/-- The Chapter 10 actor lifted inside the matching universal endpoint. -/
abbrev universalBOneActor := coveredActor (F := Universal.cosetFamily (reducedAmalgam L S))
  (f := bOne_tree_map h) d.actor i

/-- Its isomorphism to the earlier actor uses the actual universal covering map. -/
def universalBOneActorEquiv : universalBOneActor h i d ≃* d.actor :=
  coveredActorEquiv (bOne_tree_cover h) d.actor i (by exact actor_le_endpoint i d)

/-- The literal earlier quotient, composed with the same covering restriction. -/
def universalBOneQuotient : universalBOneActor h i d →* SL(2,F) :=
  d.quotient.comp (universalBOneActorEquiv h i d).toMonoidHom

/-- Natural coordinates on the actual lifted actor's kernel, with no
identification of the larger endpoint quotient with SL₂. -/
def universalBOneNaturalKernel
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) i)=
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hz : centerIn d.actor=⊥) (E : W ≃ₗ[ZMod 2] (Fin 2 → F)) :
    NaturalKernel (universalBOneQuotient h i d) :=
  (BOneActor.naturalKernel (reduced_triple h) d hcore hz E).ofEquiv
    (universalBOneActorEquiv h i d)

private theorem bOne_middle_eq : originalMiddle (reducedAmalgam L S)=
    Universal.cosetFamily (reducedAmalgam L S) false ⊓
      Universal.cosetFamily (reducedAmalgam L S) true :=
  (Universal.overlap_eq _ (inclusion_injective (commonBorel_le_parabolic 0))
    (inclusion_injective (commonBorel_le_parabolic 1))).symm

private theorem bOne_middle_le (j : Bool) : originalMiddle (reducedAmalgam L S)≤
    Universal.cosetFamily (reducedAmalgam L S) j := by
  rw [bOne_middle_eq]
  cases j
  · exact inf_le_left
  · exact inf_le_right

/-- The whole chosen source Cartan normalizes the lifted earlier actor. -/
theorem universalBOneActor_normalized (c : CompatibleCartans L (reducedSylow L S))
    (hactor : d.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S)) :
    cartan c≤normalizer (universalBOneActor h i d : Set (reducedAmalgam L S).Universal) := by
  apply coveredActor_normalized d.actor i (cartan c)
    ((cartan_le c).trans (bOne_middle_le i))
  have hn : (B₀ L S).subgroupOf (G₀ L S)≤normalizer (d.actor : Set (G₀ L S)) := by
    rw [hactor]
    exact reduced_borel_normalizes_source_actor h _
  apply le_trans ?_ hn
  apply (map_mono (cartan_le c)).trans
  rw [bOne_middle_eq,(bOne_tree_cover h).map_inf]
  exact (reduced_triple h).intersection.le

/-- Source (14.2) in the nonbinary centerless natural branch: the original
Chapter 10 actor supplies both the reflection and its root conjugator inside
the marked universal endpoint, retaining the full local-kernel clause. -/
theorem source_bOne_actor_root_reflection
    (c : CompatibleCartans L (reducedSylow L S))
    (hactor : d.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) i)=
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (hz : centerIn d.actor=⊥) (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
    (hdiag : ∀ k : universalBOneActor h i d, (k:(reducedAmalgam L S).Universal)∈cartan c →
      ∃ a : F, ∃ ha : a≠0, universalBOneQuotient h i d k=Matrix.SpecialLinearGroup.diag2 a ha)
    (hfull : ∀ a : F, ∀ ha : a≠0, Matrix.SpecialLinearGroup.diag2 a ha∈
      ((cartan c).subgroupOf (universalBOneActor h i d)).map (universalBOneQuotient h i d))
    (htri : ∀ k : d.actor, (k:G₀ L S)∈RankTwo.stabilizer (reducedFamily L S)
      (base (reducedFamily L S) (!i)) → (d.quotient k).val 1 0=0)
    (b : F) (hb : b≠0) (hb1 : b≠1)
    {v : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk v
      (base (Universal.cosetFamily (reducedAmalgam L S)) i))
    (x : universalBOneActor h i d)
    (hxR : (x:(reducedAmalgam L S).Universal)∈pathRoot (X := (reducedAmalgam L S).Universal) p)
    (hx : x*x=1) (a : F) (ha : a≠0) (hπx : universalBOneQuotient h i d x=upper a) :
    ∃ t : (reducedAmalgam L S).Universal,
      t∈universalBOneActor h i d ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) i=
        base (Universal.cosetFamily (reducedAmalgam L S)) i ∧
      t • base (Universal.cosetFamily (reducedAmalgam L S)) (!i)≠
        base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ∧
      t*t=1 ∧ t∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) ∧
      (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) p,
        orderOf y=2 ∧ ∃ g∈universalBOneActor h i d, g*y*g⁻¹=t) ∧
      ∀ z∈cartan c, z∈RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute t z := by
  let A := reducedAmalgam L S
  let H := universalBOneActor h i d
  let π := universalBOneQuotient h i d
  let nat := universalBOneNaturalKernel h i d hcore hz E
  let : ∀ j, Finite (reducedFamily L S j) := finite_endpoints (reduced_triple h)
  let : Finite d.actor := Finite.of_injective (inclusion d.actor_le) (inclusion_injective _)
  let : Finite H := Finite.of_equiv d.actor (universalBOneActorEquiv h i d).symm.toEquiv
  let := (reduced_hypothesis h).finite_commonBorel
  let : Finite (cartan c) := Finite.of_surjective
    ((middleMap L S).subgroupMap ((c.D 0⊔c.D 1).subgroupOf (commonBorel L (reducedSylow L S))))
    ((middleMap L S).subgroupMap_surjective _)
  let := cartan_abelian h c
  have honto : Function.Surjective π := d.onto.comp (universalBOneActorEquiv h i d).surjective
  have hn := universalBOneActor_normalized h i d c hactor
  obtain ⟨t,ht,htsq,ho,hπt,g,hg⟩ := nat.exists_actor_cartan_reflection H (cartan c)
    π honto hn (cartan_odd c) hdiag hfull b hb hb1 x hx a ha hπx
  have htri' (k : H) (hk : (k:A.Universal)∈Universal.cosetFamily A (!i)) :
      (π k).val 1 0=0 := by
    apply htri (universalBOneActorEquiv h i d k)
    rw [RankTwo.stabilizer,stabilizer_base]
    change bOne_tree_map h k∈reducedFamily L S (!i)
    rw [←(bOne_tree_cover h).map_eq (!i)]
    exact mem_map_of_mem _ hk
  have hfix : (t:A.Universal) • base (Universal.cosetFamily A) i=base (Universal.cosetFamily A) i := by
    have he := t.property.2
    rwa [←stabilizer_base (F := Universal.cosetFamily A) (i := i)] at he
  refine ⟨t,t.property,hfix,?_,congrArg Subtype.val htsq,ht,?_,?_⟩
  · intro he
    have htP : (t:A.Universal)∈Universal.cosetFamily A (!i) := by
      rw [←stabilizer_base (F := Universal.cosetFamily A) (i := !i)]
      exact he
    have hh := htri' t htP
    rw [hπt,braid_matrix a ha] at hh
    exact inv_ne_zero ha hh
  · refine ⟨x,hxR,?_,g,g.property,congrArg Subtype.val hg⟩
    rw [Subgroup.orderOf_coe]
    apply orderOf_eq_prime (show x^2=1 by simpa only [pow_two] using hx)
    intro he
    have hh := congrArg (fun z : SL(2,F) => z.val 0 1) hπx
    rw [he,map_one] at hh
    exact ha (by simpa [upper,Matrix.SpecialLinearGroup.transvection_coe] using hh.symm)
  · intro z hzK hzM
    apply nat.commutes_cartan_localKernel H (cartan c)
      (RankTwo.ballKernel (Universal.cosetFamily A) (base (Universal.cosetFamily A) i) 1)
      π honto hn _ (cartan_odd c) _ t ht z hzK hzM
    · intro k hk
      apply RankTwo.stabilizer_le_normalizer_ballKernel (Universal.cosetFamily A)
        (base (Universal.cosetFamily A) i) 1
      rw [RankTwo.stabilizer,stabilizer_base]
      exact hk.2
    · intro y hy
      apply htri' y
      have hadj : (sourceGraph A).Adj (base (Universal.cosetFamily A) i)
          (base (Universal.cosetFamily A) (!i)) :=
        ⟨by change i≠!i; cases i <;> decide,incident_base _ _ _⟩
      have he := (RankTwo.ballKernel_one_le_edge (Universal.cosetFamily A) hadj hy).2
      change (y:A.Universal)∈RankTwo.stabilizer (Universal.cosetFamily A)
        (base (Universal.cosetFamily A) (!i)) at he
      rwa [RankTwo.stabilizer,stabilizer_base] at he

end ReducedCartan
end CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
