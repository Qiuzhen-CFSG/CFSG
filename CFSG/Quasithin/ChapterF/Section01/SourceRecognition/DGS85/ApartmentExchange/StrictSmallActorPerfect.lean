module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.StrictSmallActorMarkedCoordinates
public import Theory.SpecificGroups.SL2.RootLiftDerived
public import Theory.GroupTheory.PResidual.PerfectImage

/-!
# Perfection of the actual strict six-path actor

The original source supplies both injective root images and the full diagonal
torus in their same quotient coordinates. The prescribed Cartan normalizes
each actual path radical. A nonidentity diagonal therefore moves each entire
root by commutators, and the two roots generate the small actor. Thus the
actor is perfect and equals its two-residual, before any natural-kernel or
apartment-exchange assertion.

Source: DGS, Groups and Graphs (1985), (14.3) and (14.9), pp.212,215--216.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S) {u : Vertex (reducedFamily L S)}
  (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) u)
  (hne : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
    Z (reducedFamily L S) u⁆ ≠ ⊥)
  (hb : b (reducedFamily L S) = 2)
  (hβu : (graph (reducedFamily L S)).Adj (base (reducedFamily L S) true) u)
  (hns : ¬ Group.IsSolvable (parabolic L S 0))
  {n : ℕ} (hlinear : ClassicalGroup.IsPSL (L 0 ⧸ pCore 2 (L 0)) 2 (2^n))
local notation "A" => reducedAmalgam L S
variable {a b : SourceVertex (reducedAmalgam L S)}
  (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
  (hp : p.IsPath) (hl : p.length=12)
  (hT : ∀ z∈p.support, z∈strictSourceApartment h hc hne hb hβu hns hlinear)

include h hc hne hb hβu hns hlinear hp hl hT

/-- The two literal half-path radicals generate a perfect actor, from
the unchanged original strict source inputs. -/
theorem strict_source_small_actor_perfect :
    Group.IsPerfect (halfPathActor (X := (A).Universal) p 6) := by
  obtain ⟨K,fK,finK,chK,hK,e,hmarks⟩ :=
    strict_source_small_actor_marked_coordinates h hc hne hb hβu hns hlinear
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨_,_,hRk,hVk,z,hR,hV,hfull⟩ := hmarks p hp hl hT
  let D := halfPathActor (X := (A).Universal) p 6
  let R := (pathRoot (X := (A).Universal) (p.drop 6)).subgroupOf D
  let V := (pathRoot (X := (A).Universal) (p.take 6)).subgroupOf D
  let c := chosenCartans h
  let C := (cartan c).subgroupOf D
  let k := K ((bOne_tree_cover h).vertex (p.getVert 6)).type
  let f := (MulAut.conj z).toMonoidHom.comp
    (halfPathLinearMap h p 6 hl (e ((bOne_tree_cover h).vertex (p.getVert 6))))
  have hker : f.ker=(halfPathLinearMap h p 6 hl (e ((bOne_tree_cover h).vertex (p.getVert 6)))).ker :=
    MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective
  have hRk' : R ⊓ f.ker=⊥ := by rw [hker]; exact hRk
  have hVk' : V ⊓ f.ker=⊥ := by rw [hker]; exact hVk
  have hoddC : Odd (Nat.card C) := by
    rw [←card_map_of_injective (f := D.subtype) (K := C) D.subtype_injective]
    change Odd (Nat.card (((cartan c).subgroupOf D).map D.subtype))
    rw [subgroupOf_map_subtype]
    exact (Nat.coprime_two_left.mp (cartan_odd c)).of_dvd_nat
      (card_dvd_of_le (show cartan c ⊓ D ≤ cartan c from inf_le_left))
  have hoim : Odd (Nat.card (C.map f)) := hoddC.of_dvd_nat (C.card_map_dvd f)
  have hCne : C.map f≠⊥ := by
    let : Nontrivial kˣ := Finite.one_lt_card_iff_nontrivial.mp (by
      rw [Nat.card_units]
      have := hK ((bOne_tree_cover h).vertex (p.getVert 6)).type
      change 4≤Nat.card k at this
      omega)
    obtain ⟨s,hs⟩ := exists_ne (1:kˣ)
    intro he
    have hm := hfull (s:k) s.ne_zero
    change Matrix.SpecialLinearGroup.diag2 (s:k) s.ne_zero∈C.map f at hm
    have hm1 := he.le hm
    have heq := congrArg (fun x : SL(2,k) => x.val 0 0) hm1
    apply hs
    apply Units.ext
    simpa [Matrix.SpecialLinearGroup.diag2_coe'] using heq
  let d := strictSourceReflections h hc hne hb hβu hns hlinear
  have hfix (x : D) (hx : x∈C) (j : ℕ) :
      x.val • p.getVert j=p.getVert j :=
    reflectionApartment_fixed c d.t d.normalizes x.val hx _ (hT _ (p.getVert_mem_support j))
  have hCR : C ≤ normalizer (R : Set D) := by
    intro x hx
    have hpath : x.val∈pathFixer (X := (A).Universal) (p.drop 6) := by
      intro j _
      rw [drop_getVert]
      exact hfix x hx _
    have hn := pathFixer_le_normalizer_pathRoot (p.drop 6) hpath
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp hn y.val)
  have hCV : C ≤ normalizer (V : Set D) := by
    intro x hx
    have hpath : x.val∈pathFixer (X := (A).Universal) (p.take 6) := by
      intro j _
      rw [take_getVert]
      exact hfix x hx _
    have hn := pathFixer_le_normalizer_pathRoot (p.take 6) hpath
    exact mem_normalizer_iff.mpr (fun y => mem_normalizer_iff.mp hn y.val)
  have hRd : R ≤ _root_.commutator D := Matrix.SpecialLinearGroup.sylow_lift_le_commutator
    f R C (Matrix.SpecialLinearGroup.upperUnipotentSylow k 2) hR hRk' hCR hoim hCne
  have hVcard : Nat.card (V.map f)=Nat.card k := by
    let j : k → V.map f := fun a => ⟨NaturalCubic.lower a,(hV _).mpr ⟨a,rfl⟩⟩
    have hj : Function.Bijective j := by
      constructor
      · intro x y he
        have he' := congrArg (fun z : V.map f => z.val.val 1 0) he
        simpa [j,NaturalCubic.lower,Matrix.SpecialLinearGroup.transvection_coe] using he'
      · intro x
        obtain ⟨a,ha⟩ := (hV x.val).mp x.property
        exact ⟨a,Subtype.ext ha⟩
    exact (Nat.card_congr (Equiv.ofBijective j hj)).symm
  obtain ⟨Q,hQ⟩ := ((pathRoot_isTwo (X := (A).Universal) (p.take 6)).comap_subtype.map f).exists_le_sylow
  have hQeq : V.map f=(Q : Subgroup SL(2,k)) := by
    apply eq_of_le_of_card_ge hQ
    change Nat.card Q ≤ Nat.card (V.map f)
    rw [hVcard,←Nat.card_congr (Matrix.SpecialLinearGroup.sylowEquivAdditive k 2 Q).toEquiv]
    rfl
  have hVd : V ≤ _root_.commutator D := Matrix.SpecialLinearGroup.sylow_lift_le_commutator
    f V C Q hQeq hVk' hCV hoim hCne
  have hgen : R ⊔ V=⊤ := by
    apply Subgroup.map_injective D.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le
      (show pathRoot (X := (A).Universal) (p.drop 6) ≤ D from le_sup_left),
      map_subgroupOf_eq_of_le
      (show pathRoot (X := (A).Universal) (p.take 6) ≤ D from le_sup_right),
      ←MonoidHom.range_eq_map,range_subtype]
  exact ⟨top_unique (hgen ▸ sup_le hRd hVd)⟩

/-- The whole actual strict small actor equals its two-residual. -/
theorem strict_source_small_actor_two_residual :
    pResidual 2 (halfPathActor (X := (A).Universal) p 6)=⊤ := by
  let _ : ∀ i, Finite (reducedFamily L S i) := finite_endpoints (reduced_triple h)
  let J := graphLocalGroup (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 6))
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _)) (inclusion_injective _)
  let _ : Finite (halfPathActor (X := (A).Universal) p 6) :=
    Finite.of_injective _ (halfPathLocalMap_injective h p 6 hl)
  let _ := strict_source_small_actor_perfect h hc hne hb hβu hns hlinear p hp hl hT
  exact pResidual_eq_top_of_isPerfect 2

end CFSG.Quasithin.ChapterF.Source.DGS85.Assembly.BTwoSource
