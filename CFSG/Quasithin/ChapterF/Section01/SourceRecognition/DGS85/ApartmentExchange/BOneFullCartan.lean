module
public import Theory.GroupTheory.WeakBNPair.RegularTree.NaturalCentralCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.BOneCentralUniversal

/-!
# Whole-Cartan reflections with the central defect retained

On the actual universal endpoint, the source identity Q=Z makes the kernel
of the lifted Chapter 10 actor elementary abelian. Its center lies in this
kernel because the binary SL₂ image is centerless. The central correction
therefore gives an involution normalizing the whole compatible Cartan,
moving the other marked endpoint and centralizing the Cartan part of the
full local permutation kernel.

The original path-root element is retained in the conjugacy formula, along
with the actual central factor introduced by Hall correction. The proof does
not put that factor in the path root: regular path roots meet the full local
kernel trivially. Removing the central defect, the diagonal markings, the
binary case, and the Chapter 14 exchange alternatives remain source
obligations. This is not the complete conjugacy clause of (14.2) or (14.19).

Source: DGS, *Groups and Graphs* (1985), (10.5), pp.155--157, and the
universal-tree reflection argument (14.2), pp.208--211.
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

/-- Construct a reflection of the whole Cartan in the nonbinary natural
branch with arbitrary actor center. The exact central defect in its path-root
conjugacy is retained; no unproved root-fusion statement is used. -/
theorem source_bOne_full_cartan_reflection
    (c : CompatibleCartans L (reducedSylow L S))
    (hactor : d.actor=((B₀ L S).pCoreIn 2 ⊔ starredParabolic L S (if i then 1 else 0)).subgroupOf (G₀ L S))
    (hcore : Q (reducedFamily L S) (base (reducedFamily L S) i)=
      Z (reducedFamily L S) (base (reducedFamily L S) i))
    (E : W ≃ₗ[ZMod 2] (Fin 2 → F))
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
      t*t=1 ∧ orderOf t=2 ∧ t∈normalizer (cartan c : Set (reducedAmalgam L S).Universal) ∧
      (∃ y∈pathRoot (X := (reducedAmalgam L S).Universal) p,
        orderOf y=2 ∧ ∃ z∈centerIn (universalBOneActor h i d),
          bOne_tree_map h z∈Q (reducedFamily L S) (base (reducedFamily L S) i) ∧
          ∃ g∈universalBOneActor h i d, g*(z*y)*g⁻¹=t) ∧
      ∀ z∈cartan c, z∈RankTwo.ballKernel (Universal.cosetFamily (reducedAmalgam L S))
        (base (Universal.cosetFamily (reducedAmalgam L S)) i) 1 → Commute t z := by
  let A := reducedAmalgam L S
  let H := universalBOneActor h i d
  let π := universalBOneQuotient h i d
  let nat := universalBOneNaturalCentralKernel h i d hcore E
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
  let e := universalBOneActorEquiv h i d
  have hcenter : center H≤π.ker := by
    intro z hz
    have hc : π z∈center SL(2,F) := by
      apply Subgroup.mem_center_iff.mpr
      intro y
      obtain ⟨u,rfl⟩ := honto y
      simpa only [map_mul] using congrArg π (Subgroup.mem_center_iff.mp hz u)
    rwa [Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot,mem_bot] at hc
  have kernel_core (z : H) (hz : z∈π.ker) :
      bOne_tree_map h z∈Q (reducedFamily L S) (base (reducedFamily L S) i) := by
    have hm : e z∈d.quotient.ker := hz
    rw [d.kernel] at hm
    exact hm
  have hsquare (z : π.ker) : z*z=1 := by
    have hzQ := kernel_core z z.property
    have hzZ : bOne_tree_map h z∈Z (reducedFamily L S) (base (reducedFamily L S) i) := hcore ▸ hzQ
    have hs := ((mem_omegaCenterIn_iff _ _).mp
      ((source_Z_Q_U (reduced_triple h) (base (reducedFamily L S) i)).1 hzZ)).2.2
    apply Subtype.ext
    apply e.injective
    apply Subtype.ext
    simpa only [Subgroup.coe_mul,Subgroup.coe_one,map_mul,map_one,e,
      universalBOneActorEquiv,coveredActorEquiv_apply,pow_two] using hs
  obtain ⟨t,ht,htsq,ho,hπt,z,hz,hzker,g,hg⟩ := nat.exists_full_cartan_reflection H (cartan c)
    π honto hn (cartan_odd c) hcenter hsquare hdiag hfull b hb hb1 x hx a ha hπx
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
  refine ⟨t,t.property,hfix,?_,congrArg Subtype.val htsq,
    (Subgroup.orderOf_coe t).trans ho,ht,?_,?_⟩
  · intro he
    have htP : (t:A.Universal)∈Universal.cosetFamily A (!i) := by
      rw [←stabilizer_base (F := Universal.cosetFamily A) (i := !i)]
      exact he
    have hh := htri' t htP
    rw [hπt,braid_matrix a ha] at hh
    exact inv_ne_zero ha hh
  · refine ⟨x,hxR,?_,z,?_,kernel_core z hzker,g,g.property,congrArg H.subtype hg⟩
    · rw [Subgroup.orderOf_coe]
      apply orderOf_eq_prime (show x^2=1 by simpa only [pow_two] using hx)
      intro he
      have hh := congrArg (fun z : SL(2,F) => z.val 0 1) hπx
      rw [he,map_one] at hh
      exact ha (by simpa [upper,Matrix.SpecialLinearGroup.transvection_coe] using hh.symm)
    · rw [centerIn_eq_map_center]
      exact mem_map_of_mem H.subtype hz
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
