module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorReflections
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorTorus
public import Theory.GroupTheory.WeakBNPair.RegularTree.FaithfulPathExchange
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange.SourceWeylParameter

/-!
# Exchange and the marked quotient for faithful elementary actors

The original midpoint map identifies each two-root actor with SL2 under
the retained nontrivial Cartan-kernel condition. The actual Cartan fills
the diagonal torus in the same root coordinates, and the constructed
reversing involution lies in that actor. Comparing the reciprocal-parameter
braid with this reflection gives a Cartan correction. Faithfulness kills
its kernel, proving exchange on every supported eight-path.

The source constructs the same-Cartan reflections without a reflection or
catalogue premise. The final consumer uses the proved exchange to construct
the literal finite quotient, both original endpoint inclusion squares,
the whole Borel, split data and rotation order four, and applies the marked
U4 comparison. The Cartan-kernel condition and Borel-image root signs remain
explicit. Their discharge, the binary reflection choices, nonelementary
catalogue exclusions and full original (11.7)--(11.8) assembly remain with
this source family; no unconditional recognition is asserted here.

Source: DGS, Groups and Graphs (1985), (14.11)--(14.12), pp.217--218;
(3.6)--(3.7), pp.77--80, and Theorem D, p.224. The elementary source
profile is (11.7), pp.174--175.
-/

@[expose] public noncomputable section
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

/-- Exchange on the actual eight-path follows from the constructed faithful
actor, full diagonal Cartan and reversing involution. Only the previously
explicit Cartan-kernel condition remains at this path. -/
theorem original_elementary_nonbinary_path_exchange
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hne : (cartan c).map (bOne_tree_map h) ⊓
      U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥)
    (g : (A).Universal)
    (hg : ∀ j, 4≤j → j≤8 → g • p.getVert j=p.getVert j)
    (hmove : g • a≠a) :
    ∃ y : (A).Universal, (∀ j≤4, y • p.getVert j=p.getVert j) ∧ y • (g • a)=b := by
  obtain ⟨m,hm,K,fK,finK,chK,hK,e,hroots⟩ :=
    original_elementary_apartment_root_coordinates h hc hb hcomm helem
      c t htfix htmove htsq htnorm
  let _ := fK
  let _ := finK
  let _ := chK
  let D := halfPathActor (X := (A).Universal) p 4
  let R := (pathRoot (X := (A).Universal) (p.drop 4)).subgroupOf D
  let V := (pathRoot (X := (A).Universal) (p.take 4)).subgroupOf D
  let v := (bOne_tree_cover h).vertex (p.getVert 4)
  let k := K v.type
  obtain ⟨hf,hker,hr,hv,z,hR,hV,_⟩ := hroots p hp hl hT
  let f := (MulAut.conj z).toMonoidHom.comp (halfPathLinearMap h p 4 hl (e v))
  have hzero := original_elementary_nonbinary_actor_core_eq_bot h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hnb hne
  have hfi : Function.Injective f := (f.ker_eq_bot_iff).mp (by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulAut.conj z).injective,hker,hzero])
  have hdiag := original_elementary_actor_full_diagonal h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT (e v) z hR hV
  obtain ⟨u,huD,_,_,_,hrev,_⟩ := original_elementary_nonbinary_actor_reflection
    h hc hb hcomm helem c t htfix htmove htsq htnorm p hp hl hT hnb hne
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hfix : cartan c ≤ pathFixer (X := (A).Universal) p := by
    intro x hx j _
    exact reflectionApartment_fixed c t htnorm x hx _ (hT _ (p.getVert_mem_support j))
  have hfac := apartment_path_factorization h c 4 (by decide) t htfix htmove htsq
    htnorm hpath.1 (original_source_tree_thickness h t) (p.drop 4)
    (by rw [drop_length,hl]; decide) (by
      intro x hx
      rw [drop_support_eq_support_drop_min] at hx
      exact hT x (List.mem_of_mem_drop hx))
  apply halfFixer_exchange_of_faithful_coordinates p 4 hl (cartan c) D hfix hfac
    le_sup_left f hfi ?_ ?_ ?_ hdiag ⟨u,huD⟩ hrev g hg hmove
  · intro x hx
    obtain ⟨a,ha⟩ := (Matrix.SpecialLinearGroup.mem_upperUnipotent k (f x)).mp
      (hR ▸ mem_map_of_mem f hx)
    exact ⟨a,ha.symm⟩
  · intro y hy
    obtain ⟨a,ha⟩ := (hV (f y)).mp (mem_map_of_mem f hy)
    exact ⟨a,ha.symm⟩
  · intro a
    obtain ⟨y,hy,he⟩ := (hV (NaturalCubic.lower a)).mpr ⟨a,rfl⟩
    exact ⟨y,hy,he⟩

omit p hp hl hT in
/-- The same apartment satisfies the complete source exchange condition as
soon as its Cartan-kernel condition holds at supported midpoints. -/
theorem original_elementary_nonbinary_apartment_exchange
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hkernel : ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=8 →
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c t)) →
      (cartan c).map (bOne_tree_map h) ⊓
        U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) :
    ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (reflectionGroup c t)) 4 := by
  intro a b p hp hl hT g hg hmove
  exact original_elementary_nonbinary_path_exchange h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hnb (hkernel p hp hl hT) g hg hmove

omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The original nonbinary source constructs its own Cartan reflections;
exchange then needs only the nontriviality of their full local kernels. -/
theorem original_elementary_nonbinary_exchange_apartment
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i=base T i) ∧
      (∀ i, t i • base T (!i)≠base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
      ((∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=8 →
        (∀ z∈p.support, z∈cartanApartment A (reflectionGroup (chosenCartans h) t)) →
        (cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
          U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) →
        ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
          (cartanApartment A (reflectionGroup (chosenCartans h) t)) 4) := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  exact ⟨t,htfix,htmove,htsq,htnorm,fun hk =>
    original_elementary_nonbinary_apartment_exchange h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm hnb hk⟩

omit p hp hl hT

local notation "hpath" => original_elementary_tree_path_profile h hc hb hcomm
  (original_borel_elementary_alpha_model h hc hb helem)
  (original_borel_elementary_beta_model h helem) helem

variable
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map ((Reduction.G₀ L S)).subtype ⧸
        pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map ((Reduction.G₀ L S)).subtype)) 2 2)
    (hkernel : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b), p.IsPath → p.length=8 →
      (∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) →
      (cartan c).map (bOne_tree_map h) ⊓
        U (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥)
    (hsign : ∀ i x, x∈reflectionGroup c t →
      (∀ r∈((pathRoots h c 4 (by decide) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm (original_borel_elementary_alpha_model h hc hb helem) (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4
        (x⁻¹*r*x)∈(originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)) ∨
      (∀ r∈((pathRoots h c 4 (by decide) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm (original_borel_elementary_alpha_model h hc hb helem) (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4
        ((t i*x)⁻¹*r*(t i*x))∈(originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)))

local notation "hex" => original_elementary_nonbinary_apartment_exchange
  h hc hb hcomm helem c t htfix htmove htsq htnorm hnb hkernel

/-- The actual marked finite quotient, with exchange constructed from the
source actors. Cartan-kernel nontriviality and the root signs remain explicit. -/
def elementaryActorFiniteQuotient :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.MarkedQuotient (recognitionEndpoints A) :=
  pathFiniteQuotient h c 4 (by decide) t htfix htmove htsq htnorm hpath.1
    (original_source_tree_thickness h t) hpath.2 hex hsign

/-- Both original endpoint inclusion squares and the whole Borel are retained. -/
def elementaryActorFiniteMarkedIso : Iso A
    (elementaryActorFiniteQuotient h hc hb hcomm helem c t htfix htmove htsq htnorm
      hnb hkernel hsign).standardAmalgam := by
  unfold elementaryActorFiniteQuotient
  exact pathFiniteMarkedIso h c 4 (by decide) t htfix htmove htsq htnorm hpath.1
    (original_source_tree_thickness h t) hpath.2 hex hsign

/-- The same quotient has the original normal two-group and odd Cartan splitting. -/
def elementaryActorFiniteSplitData : Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
    (elementaryActorFiniteQuotient h hc hb hcomm helem c t htfix htmove htsq htnorm
      hnb hkernel hsign).tits := by
  unfold elementaryActorFiniteQuotient
  exact pathFiniteSplitData h c 4 (by decide) t htfix htmove htsq htnorm hpath.1
    (original_source_tree_thickness h t) hpath.2 hex hsign

/-- The constructed quotient has exactly the source Weyl parameter four. -/
theorem elementaryActorFiniteRotationOrder :
    Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates.rotationOrder
      (elementaryActorFiniteQuotient h hc hb hcomm helem c t htfix htmove htsq htnorm
        hnb hkernel hsign)=4 := by
  unfold elementaryActorFiniteQuotient
  exact pathFiniteQuotient_simple_product_order h c 4 (by decide) t htfix htmove htsq htnorm
    hpath.1 (original_source_tree_thickness h t) hpath.2 hex hsign

include hnb hkernel hsign in
/-- Literal marked U4 comparison using the constructed exchange and quotient.
The Cartan-kernel and root-sign premises are still source obligations. -/
theorem original_elementary_nonbinary_comparison_of_cartan_kernels_and_signs :
    ∃ (m : ℕ) (hm : 0<m), Nonempty (Iso A (UnitaryFourNative.amalgam m hm false)) := by
  let := FongSeitzBinary.QuadrangleStructure.original_core_normal_in_sylow
    (L := L) (S := reducedSylow L S) 1
  have he : IsElementaryAbelian 2 (reducedSylow L S ⧸
      ((parabolic L (reducedSylow L S) 1).pCoreIn 2).subgroupOf (reducedSylow L S)) := by
    have hq : (Q F (base F true)).map (G₀).subtype =
        (parabolic L (reducedSylow L S) 1).pCoreIn 2 :=
      (reduced_base_Q_map h true).trans (reduced_parabolic_core h 1).symm
    have he := helem
    rw [hq] at he
    obtain ⟨hn,he⟩ := he
    exact he
  exact original_elementary_reduced_comparison_of_source h hc hb hcomm he
    (elementaryActorFiniteQuotient h hc hb hcomm helem c t htfix htmove htsq htnorm hnb hkernel hsign)
    (elementaryActorFiniteMarkedIso h hc hb hcomm helem c t htfix htmove htsq htnorm hnb hkernel hsign)
    (elementaryActorFiniteSplitData h hc hb hcomm helem c t htfix htmove htsq htnorm hnb hkernel hsign)
    (elementaryActorFiniteRotationOrder h hc hb hcomm helem c t htfix htmove htsq htnorm hnb hkernel hsign)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
