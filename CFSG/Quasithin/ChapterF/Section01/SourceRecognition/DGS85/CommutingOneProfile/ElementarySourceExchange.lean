module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryAlphaCartan
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementaryBetaExchange

/-!
# Nonbinary elementary exchange from the original source

The alpha torus-separation argument and the beta torus-order argument now
supply both nontrivial full Cartan-kernel factors. Applying the existing
faithful two-root calculation proves exchange throughout the apartment.
The original source also constructs the Cartan-normalizing involutions,
so the apartment-existence conclusion has no reflection or kernel premise.

The literal marked U4 comparison retains only the quotient Borel root-sign
input. Its finite quotient, split data, rotation order four, full Borel
and both original endpoint inclusion squares are the previously constructed
ones. This conditional comparison is not the complete source recognition:
root signs, binary choices, nonelementary exclusions and the full retained
11.7/11.8 assembly still require discharge.
Source: DGS, Groups and Graphs (1985), (14.6), pp.213--214;
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


omit p hp hl hT in
/-- Exchange for the actual nonbinary elementary apartment, with both
Cartan-kernel conditions proved from the original source. -/
theorem original_elementary_nonbinary_apartment_exchange_of_source
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
      (cartanApartment A (reflectionGroup c t)) 4 := by
  exact original_elementary_nonbinary_exchange_of_alpha_kernels
    h hc hb hcomm helem c t htfix htmove htsq htnorm hnb
    (fun p hp hl hT hv => original_elementary_nonbinary_alpha_cartan_kernel_ne_bot
      h hc hb hcomm helem c t htfix htmove htsq htnorm p hp hl hT hnb hv)

omit c t htfix htmove htsq htnorm p hp hl hT in
/-- The original source constructs a full-Cartan apartment satisfying
exchange at every vertex. No reflection or Cartan-kernel premise remains. -/
theorem original_elementary_nonbinary_exchange_apartment_of_source
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ t : Bool → (A).Universal,
      (∀ i, t i • base T i=base T i) ∧
      (∀ i, t i • base T (!i)≠base T (!i)) ∧
      (∀ i, t i*t i=1) ∧
      (∀ i, t i∈normalizer (cartan (chosenCartans h) : Set (A).Universal)) ∧
      ChosenApartmentExchange (X := (A).Universal) (sourceGraph A)
        (cartanApartment A (reflectionGroup (chosenCartans h) t)) 4 := by
  obtain ⟨t,htfix,htmove,htsq,htnorm⟩ :=
    original_elementary_nonbinary_tree_reflections h hc hb hcomm helem hnb (chosenCartans h)
  exact ⟨t,htfix,htmove,htsq,htnorm,
    original_elementary_nonbinary_apartment_exchange_of_source h hc hb hcomm helem
      (chosenCartans h) t htfix htmove htsq htnorm hnb⟩

omit p hp hl hT

variable
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map ((Reduction.G₀ L S)).subtype ⧸
        pCore 2 ((graphLocalGroup (reducedFamily L S) (base (reducedFamily L S) true)).map ((Reduction.G₀ L S)).subtype)) 2 2)
    (hsign : ∀ i x, x∈reflectionGroup c t →
      (∀ r∈((pathRoots h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm (original_borel_elementary_alpha_model h hc hb helem) (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4
        (x⁻¹*r*x)∈(originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)) ∨
      (∀ r∈((pathRoots h c 4 (Nat.succ_lt_succ (Nat.zero_lt_succ 2)) t htfix htmove htsq htnorm (original_elementary_tree_path_profile h hc hb hcomm (original_borel_elementary_alpha_model h hc hb helem) (original_borel_elementary_beta_model h helem) helem).1 (original_source_tree_thickness h t)) i).root, quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4
        ((t i*x)⁻¹*r*(t i*x))∈(originalMiddle (reducedAmalgam L S)).map
          (quotientMap (reducedAmalgam L S) (cartanApartment (reducedAmalgam L S) (reflectionGroup c t)) 4)))


include hnb hsign in
/-- The literal marked U4 comparison now retains only the quotient
Borel root-sign input. Its Cartan-kernel and exchange inputs are discharged. -/
theorem original_elementary_nonbinary_comparison_of_signs :
    ∃ (m : ℕ) (hm : 0<m), Nonempty (Iso A (UnitaryFourNative.amalgam m hm false)) := by
  exact original_elementary_nonbinary_comparison_of_alpha_kernels_and_signs
    h hc hb hcomm helem c t htfix htmove htsq htnorm hnb
    (fun p hp hl hT hv => original_elementary_nonbinary_alpha_cartan_kernel_ne_bot
      h hc hb hcomm helem c t htfix htmove htsq htnorm p hp hl hT hnb hv) hsign

end CFSG.Quasithin.ChapterF.Source.DGS85.CommutingOneProfile
