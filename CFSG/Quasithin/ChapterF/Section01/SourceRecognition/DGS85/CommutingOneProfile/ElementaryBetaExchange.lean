module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryCartanKernels
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryActorExchange

/-!
# Elementary exchange with the beta Cartan-kernel premise discharged

The original nonbinary source supplies the full-Cartan reflections. The
strict adjacent-torus order comparison now proves the beta kernel
nontrivial, so the existing faithful-actor exchange applies at every beta
midpoint without a kernel premise. The full apartment exchange and marked
U4 comparison retain only the alpha kernel and literal Borel root signs.

The comparison constructs the finite quotient, both original endpoint
inclusion squares, full Borel, split structure and rotation order four
before applying the existing U4 profile. It does not assert unconditional
recognition: alpha kernels, root signs, binary choices, nonelementary
exclusions and the complete original 11.7/11.8 assembly remain here.

Source: DGS, Groups and Graphs (1985), (14.6), pp.213--214,
(14.11)--(14.12), pp.217--218, and Theorem D, p.224.
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


/-- The nonbinary source exchange conclusion at every beta midpoint has
no Cartan-kernel premise. The alpha midpoint remains a separate duty. -/
theorem original_elementary_nonbinary_beta_path_exchange
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type=true)
    (g : (A).Universal)
    (hg : ∀ j, 4≤j → j≤8 → g • p.getVert j=p.getVert j)
    (hmove : g • a≠a) :
    ∃ y : (A).Universal, (∀ j≤4, y • p.getVert j=p.getVert j) ∧ y • (g • a)=b := by
  exact original_elementary_nonbinary_path_exchange h hc hb hcomm helem
    c t htfix htmove htsq htnorm p hp hl hT hnb
    (original_elementary_beta_cartan_kernel_ne_bot h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT hv) g hg hmove


omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The original nonbinary elementary source constructs an apartment with
nontrivial beta Cartan kernels and exchange at every beta midpoint. -/
theorem original_elementary_nonbinary_beta_exchange_apartment
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
        ((bOne_tree_cover h).vertex (p.getVert 4)).type=true →
        ((cartan (chosenCartans h)).map (bOne_tree_map h) ⊓
          U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) ∧
        (∀ g : (A).Universal, (∀ j, 4≤j → j≤8 → g • p.getVert j=p.getVert j) →
          g • a≠a → ∃ y : (A).Universal,
            (∀ j≤4, y • p.getVert j=p.getVert j) ∧ y • (g • a)=b) := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  refine ⟨t,htfix,htmove,htsq,htnorm,?_⟩
  intro a b p hp hl hT hv
  exact ⟨original_elementary_beta_cartan_kernel_ne_bot h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hv,
    fun g hg hmove => original_elementary_nonbinary_beta_path_exchange h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm p hp hl hT hnb hv g hg hmove⟩

omit p hp hl hT in
/-- Only the alpha midpoint kernel condition remains in the elementary
apartment exchange theorem. -/
theorem original_elementary_nonbinary_exchange_of_alpha_kernels
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    (hα : ∀ {a b} (p : (sourceGraph A).Walk a b), p.IsPath → p.length=8 →
      (∀ z∈p.support, z∈cartanApartment A (reflectionGroup c t)) →
      ((bOne_tree_cover h).vertex (p.getVert 4)).type=false →
      (cartan c).map (bOne_tree_map h) ⊓
        U F ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥) :
    ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (reflectionGroup c t)) 4 := by
  apply original_elementary_nonbinary_apartment_exchange h hc hb hcomm helem
    c t htfix htmove htsq htnorm hnb
  intro a b p hp hl hT
  cases hv : ((bOne_tree_cover h).vertex (p.getVert 4)).type
  · exact hα p hp hl hT hv
  · exact original_elementary_beta_cartan_kernel_ne_bot h hc hb hcomm helem
      c t htfix htmove htsq htnorm p hp hl hT hv

omit p hp hl hT

variable
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map ((Reduction.G₀ L S)).subtype ⧸
        pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map ((Reduction.G₀ L S)).subtype)) 2 2)
    (hα : ∀ {a b} (p : (sourceGraph (reducedAmalgam L S)).Walk a b), p.IsPath → p.length=8 →
      (∀ z∈p.support, z∈cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) →
      ((bOne_tree_cover h).vertex (p.getVert 4)).type=false →
      (cartan c).map (bOne_tree_map h) ⊓
        U (reducedFamily L S) ((bOne_tree_cover h).vertex (p.getVert 4)) ≠ ⊥)
    (hsign : ∀ i x, x∈reflectionGroup c t →
      (∀ r∈((pathRoots h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm (original_borel_elementary_alpha_model h hc hb helem) (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4
        (x⁻¹*r*x)∈(originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)) ∨
      (∀ r∈((pathRoots h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm (original_borel_elementary_alpha_model h hc hb helem) (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4
        ((t i*x)⁻¹*r*(t i*x))∈(originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)))


include hnb hα hsign in
/-- The original marked U4 comparison now needs Cartan-kernel nontriviality
only at alpha midpoints. Both original endpoint maps, the full Borel and
the literal root signs remain those of the existing finite quotient. -/
theorem original_elementary_nonbinary_comparison_of_alpha_kernels_and_signs :
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
  have hpath := original_elementary_tree_path_profile h hc hb hcomm
    (original_borel_elementary_alpha_model h hc hb helem)
    (original_borel_elementary_beta_model h helem) helem
  have hex : ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (reflectionGroup c t)) 4 :=
    original_elementary_nonbinary_exchange_of_alpha_kernels
    h hc hb hcomm helem c t htfix htmove htsq htnorm hnb hα
  let quot := pathFiniteQuotient h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm hpath.1
    (original_source_tree_thickness h t) hpath.2 hex hsign
  exact original_elementary_reduced_comparison_of_source h hc hb hcomm he quot
    (pathFiniteMarkedIso h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm hpath.1
      (original_source_tree_thickness h t) hpath.2 hex hsign)
    (pathFiniteSplitData h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm hpath.1
      (original_source_tree_thickness h t) hpath.2 hex hsign)
    (pathFiniteQuotient_simple_product_order h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm hpath.1
      (original_source_tree_thickness h t) hpath.2 hex hsign)

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
