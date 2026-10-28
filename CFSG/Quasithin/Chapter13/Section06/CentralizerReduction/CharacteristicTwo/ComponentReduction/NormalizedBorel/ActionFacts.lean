module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.Actions
public import Theory.GroupTheory.PerfectCentralCoverOuter

/-!
# The marked actions in the normalized-component reduction

All starred subgroups are images in the literal quotient N(K)/C(K).
The product of three residual conjugates of z, which is v before taking
this quotient, proves that the residual image does not centralize z*.
Centralization of a passes through the same map. The central four-group
then lies in the center of the intersection of the Sylow image with K*.

The final lemma isolates the precise root calculation still needed from
the models: every nonidentity element of that center must have the same
centralizer in the specified Borel. In particular the calculation must
apply to a*, not only to z*. This module proves the conditional exclusion;
it does not assert Borel placement or any model centralizer calculation.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 13.6.6, printed p.927.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
open Subgroup Theory.GroupTheory A5Module
open BinaryPermutation.FiveCentralizerGeometry
variable {G : Type*} [Group G] {L V : Subgroup G}

/-- The image of the actual local residual under the component action. -/
def residualStar (s : Marking L V) (K : Subgroup (Gv (markedV s))) :
    Subgroup (XStar K) :=
  ((residual s).subgroupOf (X K)).map (NormalizerAction.quotient K)

def aStar (s : Marking L V) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) : XStar K :=
  NormalizerAction.quotient K ⟨aLocal s, ha⟩

def zStar (s : Marking L V) (K : Subgroup (Gv (markedV s)))
    (hz : zLocal s ∈ X K) : XStar K :=
  NormalizerAction.quotient K ⟨zLocal s, hz⟩

/-- The source R*, embedded in X*, without a root-group assertion. -/
def rootCenter (T : Subgroup G) {v : G} (K : Subgroup (Gv v)) : Subgroup (XStar K) :=
  let U := NormalizerAction.sylowImage K (localT T v) ⊓ NormalizerAction.componentImage K
  (center U).map U.subtype

/-- The candidate relative Sylow normalizer in K*Lᵥ*. Its identification
with a model Borel, and containment of Lᵥ*, require the model argument. -/
def borelCandidate (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) : Subgroup (XStar K) :=
  (NormalizerAction.componentImage K ⊔ residualStar s K) ⊓
    normalizer ((NormalizerAction.sylowImage K (localT T (markedV s)) ⊓
      NormalizerAction.componentImage K : Subgroup (XStar K)) : Set (XStar K))

theorem residualStar_le_of_le (s : Marking L V) (K : Subgroup (Gv (markedV s)))
    (h : residual s ≤ K) : residualStar s K ≤ NormalizerAction.componentImage K :=
  map_mono (subgroupOf_mono (X K) h)

theorem aStar_centralizes_residual (s : Marking L V)
    (K : Subgroup (Gv (markedV s))) (ha : aLocal s ∈ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s)))) :
    ⁅residualStar s K, zpowers (aStar s K ha)⁆ = ⊥ := by
  rw [commutator_eq_bot_iff_le_centralizer]
  intro d hd
  obtain ⟨d, hd, rfl⟩ := hd
  rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
  exact (show Commute d (⟨aLocal s, ha⟩ : X K) from
    Subtype.ext (mem_centralizer_iff.mp hac d hd)).map (NormalizerAction.quotient K)

/-- The marked triple product detects a nontrivial commutator in the
faithful action, even though its prequotient product is the central v. -/
theorem zStar_not_centralizes_residual [Finite G] (s : Marking L V)
    (K : Subgroup (Gv (markedV s))) (hz : zLocal s ∈ X K)
    (hDN : residual s ≤ X K)
    (hzc : zLocal s ∉ centralizer (K : Set (Gv (markedV s)))) :
    ⁅residualStar s K, zpowers (zStar s K hz)⁆ ≠ ⊥ := by
  intro hc
  obtain ⟨c, hcD, hprod⟩ := exists_residual_triple s
  let cH : Gv (markedV s) := ⟨c, Lv_le_Gv L (markedV s) hcD⟩
  let cX : X K := ⟨cH, hDN hcD⟩
  let zX : X K := ⟨zLocal s, hz⟩
  let q := NormalizerAction.quotient K
  have hzc1 : q zX ≠ 1 := fun he => hzc ((NormalizerAction.quotient_eq_one_iff K zX).mp he)
  have hcz : Commute (q cX) (q zX) := by
    have hh := commutator_eq_bot_iff_le_centralizer.mp hc
      (show q cX ∈ residualStar s K from ⟨cX, hcD, rfl⟩)
    exact (mem_centralizer_iff.mp hh (zStar s K hz) (mem_zpowers _)).symm
  have hz2 : zX * zX = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change s.map (Multiplicative.ofAdd z) * s.map (Multiplicative.ofAdd z) = 1
    rw [← map_mul, show Multiplicative.ofAdd z * Multiplicative.ofAdd z = 1 by decide +kernel,
      map_one]
  have hp : q (zX * MulAut.conj cX zX * MulAut.conj (cX ^ 2) zX) = 1 := by
    apply (NormalizerAction.quotient_eq_one_iff K _).mpr
    have he : ((zX * MulAut.conj cX zX * MulAut.conj (cX ^ 2) zX : X K) :
        Gv (markedV s)) = centralElement (markedV s) := Subtype.ext hprod
    rw [he]
    exact ((vLine_le_center _).trans (center_le_centralizer _)) (mem_zpowers _)
  exact (q.map_ne_of_three_conjugate_product zX zX cX hz2 hp hcz.symm hzc1) rfl

/-- The actual characteristic-two centralizer gives the required nontrivial
action of z. Together with the marked module it proves the source asymmetry. -/
theorem marked_action_asymmetry [Finite G] (s : Marking L V)
    (K : Subgroup (Gv (markedV s))) (hK : IsComponent (Gv (markedV s)) K)
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (hzCore : centralizer (pCore 2 (centralizer ({zLocal s} : Set (Gv (markedV s)))) :
      Set (centralizer ({zLocal s} : Set (Gv (markedV s))))) ≤
        pCore 2 (centralizer ({zLocal s} : Set (Gv (markedV s))))) :
    ⁅residualStar s K, zpowers (zStar s K hz)⁆ ≠ ⊥ ∧
      ⁅residualStar s K, zpowers (aStar s K ha)⁆ = ⊥ :=
  ⟨zStar_not_centralizes_residual s K hz hDN
      (hK.not_centralizes_of_twoCore_centralizer _ hzCore),
    aStar_centralizes_residual s K ha hac⟩

/-- Centrality in T* and membership in K* imply centrality in their
intersection; this does not assume that the intersection is abelian. -/
theorem four_le_rootCenter (s : Marking L V) (T : Subgroup G)
    (K : Subgroup (Gv (markedV s))) (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K)
    (hET : EStar s K ha hz ≤
      (center (NormalizerAction.sylowImage K (localT T (markedV s)))).map
        (NormalizerAction.sylowImage K (localT T (markedV s))).subtype)
    (hEK : EStar s K ha hz ≤ NormalizerAction.componentImage K) :
    EStar s K ha hz ≤ rootCenter T K := by
  intro e he
  obtain ⟨eT, heT, rfl⟩ := hET he
  refine ⟨⟨eT.val, eT.property, hEK he⟩, mem_center_iff.mpr ?_, rfl⟩
  intro u
  have hh := congrArg
    (fun x : NormalizerAction.sylowImage K (localT T (markedV s)) => x.val)
    (mem_center_iff.mp heT ⟨u.val, u.property.1⟩)
  exact Subtype.ext hh

/-- A uniform root centralizer calculation excludes the marked configuration
in any subgroup B containing the residual image. The model owners must
prove this calculation in the genuine Borel, including the extension cases. -/
theorem exclude_of_root_centralizers [Finite G] (s : Marking L V)
    (T : Subgroup G) (K : Subgroup (Gv (markedV s)))
    (ha : aLocal s ∈ X K) (hz : zLocal s ∈ X K) (hDN : residual s ≤ X K)
    (hac : aLocal s ∈ centralizer (residual s : Set (Gv (markedV s))))
    (han : aLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hzn : zLocal s ∉ centralizer (K : Set (Gv (markedV s))))
    (hER : EStar s K ha hz ≤ rootCenter T K)
    (B : Subgroup (XStar K)) (hDB : residualStar s K ≤ B)
    (hroot : ∀ r ∈ rootCenter T K, r ≠ 1 →
      B ⊓ centralizer ({r} : Set (XStar K)) = B ⊓ centralizer (rootCenter T K : Set (XStar K))) :
    False := by
  have haR : aStar s K ha ∈ rootCenter T K := hER (subset_closure (by simp [aStar]))
  have hzR : zStar s K hz ∈ rootCenter T K := hER (subset_closure (by simp [zStar]))
  have ha1 : aStar s K ha ≠ 1 := fun he =>
    han ((NormalizerAction.quotient_eq_one_iff K _).mp he)
  have hc := commutator_eq_bot_iff_le_centralizer.mp (aStar_centralizes_residual s K ha hac)
  apply zStar_not_centralizes_residual s K hz hDN hzn
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro d hd
  rw [zpowers_eq_closure, centralizer_closure, mem_centralizer_singleton_iff]
  have hdR : d ∈ B ⊓ centralizer (rootCenter T K : Set (XStar K)) := by
    rw [← hroot (aStar s K ha) haR ha1]
    exact ⟨hDB hd, mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp (hc hd) _ (mem_zpowers _)).symm⟩
  exact (mem_centralizer_iff.mp hdR.2 (zStar s K hz) hzR).symm

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.NormalizedBorel
