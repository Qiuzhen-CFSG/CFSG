module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementarySecondKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorSecondKernel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryRootCoordinates
public import Theory.GroupTheory.Commutator.AbelianSylowLift

/-!
# Central-core reduction for the actual elementary apartment actor

Under the nontrivial Cartan-kernel clause of DGS (14.5)(c), the two-root
core fixes the midpoint's second ball. The source second-kernel identities
make this core central elementary, and trivial on the alpha orbit. The
actual injective upper-root marking lifts an abelian Sylow of the midpoint
quotient. Central Sylow transfer therefore removes the core from the
actor's derived subgroup, including beta field order four.

The final application constructs the full-Cartan reflections from the
original nonbinary elementary source. It assumes no local catalogue,
reflection choice, root marking or central-extension classification.
The Cartan-kernel clause remains explicit. Eliminating the entire beta
actor core, controlling the adjoined reflection, exchange, root signs,
binary choices, nonelementary catalogue exclusions and full original
(11.7)--(11.8) marked recognition remain separate source obligations.
Source: DGS, Groups and Graphs (1985), (11.7), pp.174--175;
(14.5)(c), p.213, and the central-kernel argument in (14.9), p.215.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
open Reduction NoncommutingProfile OriginalExtension SuzukiContainment CommutingNontrivial
variable {G : Type*} [Group G] {L : Fin 2 → Subgroup G} {S : Subgroup G}
local notation "F" => reducedFamily L S
local notation "A" => reducedAmalgam L S
local notation "T" => Universal.cosetFamily A
local notation "G₀" => Reduction.G₀ L S
variable (h : HypothesisF11 L S)
    (hc : IsCriticalPair (reducedFamily L S) (base (reducedFamily L S) false) (base (reducedFamily L S) true))
    (hb : DGS85.b (reducedFamily L S) = 1)
    (hcomm : ⁅Z (reducedFamily L S) (base (reducedFamily L S) false),
      Z (reducedFamily L S) (base (reducedFamily L S) true)⁆ = ⊥)
    (helem : ∃ hN : (((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
        (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))).Normal,
      letI := hN
      IsElementaryAbelian 2 (twoCore (commonBorel L S) ⧸
        ((Q (reducedFamily L S) (base (reducedFamily L S) true)).map
          (Reduction.G₀ L S).subtype).subgroupOf (twoCore (commonBorel L S))))

include h hc hb hcomm helem


variable (c : CompatibleCartans L (reducedSylow L S))
    (t : Bool → (reducedAmalgam L S).Universal)
    (htfix : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) i =
      base (Universal.cosetFamily (reducedAmalgam L S)) i)
    (htmove : ∀ i, t i • base (Universal.cosetFamily (reducedAmalgam L S)) (!i) ≠
      base (Universal.cosetFamily (reducedAmalgam L S)) (!i))
    (htsq : ∀ i, t i*t i=1)
    (htnorm : ∀ i, t i∈normalizer (cartan c : Set (reducedAmalgam L S).Universal))

include c t htfix htmove htsq htnorm

variable {a b : SourceVertex (reducedAmalgam L S)}
    (p : (sourceGraph (reducedAmalgam L S)).Walk a b)
    (hp : p.IsPath) (hl : p.length=8)
    (hT : ∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t))
include hp hl hT

/-- Under the Cartan-kernel clause of (14.5)(c), the actor's own core is
central and elementary. It vanishes at an alpha midpoint. -/
theorem original_elementary_nonbinary_actor_core_central
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hne : (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) :
    let D := halfPathActor (X := (A).Universal) p 4
    pCore 2 D ≤ center D ∧ IsElementaryAbelian 2 (pCore 2 D) ∧
      (((bOne_tree_cover h).vertex (p.getVert 4)).type=false → pCore 2 D=⊥) := by
  intro D
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let φ := bOne_tree_map h
  let cov := bOne_tree_cover h
  let v := cov.vertex (p.getVert 4)
  let V := (D.pCoreIn 2).map φ
  have hVball : V ≤ ballKernel F v 2 :=
    (original_elementary_nonbinary_actor_core_radius_two h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT hnb hne).1
  have hVI : V ≤ neighborCoreIntersection F v := by
    apply le_iInf
    intro z
    exact CommutingTrivial.two_subgroup_le_Q F z.val (reduced_kernel_sylow h z.val)
      ((isPGroup_pCoreIn 2 D).map φ)
      (hVball.trans (ballKernel_succ_le F z.property 1))
  have hvw : (graph F).Adj v (cov.vertex (p.getVert 5)) :=
    cov.hom.map_adj (p.adj_getVert_succ (by omega))
  have hVcore : V ≤ (ballKernel F v 2).pCoreIn 2 :=
    hVI.trans_eq (reduced_neighborCoreIntersection_eq_second_core h hvw.symm)
  have hVomega : V ≤ omegaCenterIn (graphLocalGroup F v) := hVcore.trans
    (original_elementary_second_kernel_structure h hc hb hcomm helem v).2.2.1
  have hcentral : pCore 2 D ≤ center D := by
    intro x hx
    have hxV : φ x.val ∈ V := mem_map_of_mem φ (mem_map_of_mem D.subtype hx)
    have hxc := (mem_omegaCenterIn_iff _ _).mp (hVomega hxV) |>.2.1
    apply mem_center_iff.mpr
    intro y
    apply halfPathLocalMap_injective h p 4 hl
    apply Subtype.ext
    change φ (y.val*x.val)=φ (x.val*y.val)
    simp only [map_mul]
    exact mem_centralizer_iff.mp hxc _
      (halfPathActor_map_le_local h p 4 hl (mem_map_of_mem φ y.property))
  have hele : IsElementaryAbelian 2 (pCore 2 D) := by
    let f : pCore 2 D →* omegaCenterIn (graphLocalGroup F v) :=
      (φ.comp (D.subtype.comp (pCore 2 D).subtype)).codRestrict _ (fun x =>
        hVomega (mem_map_of_mem φ (mem_map_of_mem D.subtype x.property)))
    apply IsElementaryAbelian.of_injective f
    intro x y he
    apply Subtype.ext
    apply halfPathLocalMap_injective h p 4 hl
    apply Subtype.ext
    change φ x.val.val=φ y.val.val
    exact congrArg (fun z : omegaCenterIn (graphLocalGroup F v) => (z:G₀)) he
  refine ⟨hcentral,hele,?_⟩
  intro hv
  have hzero : V=⊥ := bot_unique (hVball.trans
    ((original_elementary_second_kernel_structure h hc hb hcomm helem v).1 hv).le)
  apply bot_unique
  intro x hx
  have he : φ x.val=1 := mem_bot.mp (hzero ▸
    (show φ x.val∈V from mem_map_of_mem φ (mem_map_of_mem D.subtype hx)))
  apply mem_bot.mpr
  apply halfPathLocalMap_injective h p 4 hl
  apply Subtype.ext
  change φ x.val=φ 1
  simpa only [map_one] using he


/-- The central core meets the actual actor's derived subgroup trivially.
The Sylow lift is the original four-path radical, with its actual marking. -/
theorem original_elementary_nonbinary_actor_derived_core
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hne : (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) :
    let D := halfPathActor (X := (A).Universal) p 4
    pCore 2 D ⊓ _root_.commutator D=⊥ := by
  intro D
  let _ : ∀ i, Finite (F i) := finite_endpoints (reduced_triple h)
  let J := graphLocalGroup F ((bOne_tree_cover h).vertex (p.getVert 4))
  let _ : Finite J := Finite.of_injective (inclusion (sylowGenerated_le _))
    (inclusion_injective _)
  let _ : Finite D := Finite.of_injective _ (halfPathLocalMap_injective h p 4 hl)
  have hcentral := (original_elementary_nonbinary_actor_core_central h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hnb hne).1
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hroots⟩ :=
    original_elementary_apartment_root_coordinates h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  obtain ⟨hf,hker,hr,hu,z,hR,hU,hxy⟩ := hroots p hp hl hT
  let k := K ((bOne_tree_cover h).vertex (p.getVert 4)).type
  let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
  let f := (MulAut.conj z).toMonoidHom.comp
    (halfPathLinearMap h p 4 hl (e ((bOne_tree_cover h).vertex (p.getVert 4))))
  have hfk : f.ker=pCore 2 D :=
    (MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective).trans hker
  let Q := Matrix.SpecialLinearGroup.upperUnipotentSylow k 2
  let _ : IsMulCommutative Q := inferInstanceAs
    (IsMulCommutative (Matrix.SpecialLinearGroup.upperUnipotentHom k).range)
  have he := Theory.GroupTheory.CentralExtension.kernel_inf_commutator_eq_bot_of_abelian_sylow_lift
    f (by rw [hfk]; exact hcentral) (by rw [hfk]; exact pCore_isPGroup)
    Q R hR (by rw [hfk]; exact hr)
  simpa only [hfk] using he

omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The original source constructs the apartment on which the two-root core
is central elementary, has trivial derived intersection, and vanishes on
alpha. Only the stated nontrivial Cartan-kernel clause remains conditional. -/
theorem original_elementary_nonbinary_central_core_apartment
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i=base T i) ∧
      (∀ i, t i • base T (!i)≠base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
      ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=8 →
        (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
        (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
          U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥ →
        let D := halfPathActor (X := (A).Universal) p 4
        pCore 2 D ≤ center D ∧ IsElementaryAbelian 2 (pCore 2 D) ∧
          pCore 2 D ⊓ _root_.commutator D=⊥ ∧
          (((bOne_tree_cover h).vertex (p.getVert 4)).type=false → pCore 2 D=⊥) := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  refine ⟨t,htfix,htmove,htsq,htnorm,?_⟩
  intro a b p hp hl hT hne D
  obtain ⟨hcentral,hele,hzero⟩ := original_elementary_nonbinary_actor_core_central
    h hc hb hcomm helem (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hnb hne
  exact ⟨hcentral,hele,original_elementary_nonbinary_actor_derived_core
    h hc hb hcomm helem (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hnb hne,hzero⟩

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
