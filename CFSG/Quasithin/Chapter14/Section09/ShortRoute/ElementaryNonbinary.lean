module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.ElementarySourceRecognition
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.UnitaryFourNative
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.CommutingOneProfile.FullElementaryMarkedProfile

/-!
# Original restoration of the nonbinary elementary DGS branch

The existing Chapter 11 argument constructs the marked reduced U₄ amalgam
from the original commuting distance-one hypotheses and elementary beta
Sylow quotient. Its whole-Borel isomorphism identifies the two-core orders,
so the recognized field has exactly the source degree and remains nonbinary.
Native restoration then gives the original full-Borel and endpoint maps,
including their restrictions to the reduced pair and the possible outer
extension. The same maps give a finite faithful completion with exact overlap.

No profile, exchange, root-sign or model-comparison premise is added. The
binary and nonelementary alternatives and the other critical distances
remain separate branches. This result does not identify the source ambient
group with the finite completion.
Source: Delgado--Goldschmidt--Stellmacher, Groups and Graphs (1985),
(11.7), pp.174--175, Theorem D, p.224, and (15.2), pp.226--228.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory RankTwoAmalgam SimpleGraph SimpleGraph.Walk
open Theory.GroupTheory.AmalgamGraph Subgroup.CosetGeometry.RankTwo
open Theory.GroupTheory.WeakBNPair.RegularTree
open CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.ApartmentExchange
open ReducedCartan
open scoped MatrixGroups Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
open CommutingOneProfile
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



omit hc hb hcomm helem in
/-- The whole middle map determines the field parameter through its two-core. -/
theorem elementary_comparison_core_card {m : ℕ} (hm : 0<m)
    (e : Iso A (UnitaryFourNative.amalgam m hm false)) :
    Nat.card (reducedSylow L S) = (2^m)^6 := by
  have he := congrArg (fun H : Subgroup (GreenBook.LieModels.UnitaryFour.overlap m hm) => Nat.card H)
    (pCore_map_iso 2 e.middle)
  rw [card_map_of_injective e.middle.injective] at he
  change Nat.card (pCore 2 (commonBorel L (reducedSylow L S))) =
    Nat.card (pCore 2 (GreenBook.LieModels.UnitaryFour.overlap m hm)) at he
  rw [GreenBook.LieModels.UnitaryFour.overlap_twoCore] at he
  rw [Nat.card_congr (subgroupOfEquivOfLe
    (GreenBook.LieModels.UnitaryFour.upperProjective_le_overlap m hm)).toEquiv,
    GreenBook.LieModels.UnitaryFour.upperProjective_card] at he
  have hc := congrArg (fun H : Subgroup G => Nat.card H) (reduced_borel_core h)
  rw [show twoCore (commonBorel L (reducedSylow L S)) =
    (pCore 2 (commonBorel L (reducedSylow L S))).map
      (commonBorel L (reducedSylow L S)).subtype from rfl,
    card_map_of_injective (commonBorel L (reducedSylow L S)).subtype_injective] at hc
  exact hc.symm.trans he

/-- The recognized field stays nonbinary under the original nonbinary hypothesis. -/
theorem elementary_comparison_nonbinary
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2)
    {m : ℕ} (hm : 0<m) (e : Iso A (UnitaryFourNative.amalgam m hm false)) : 1<m := by
  obtain ⟨n,hn,hbeta,_,_,_,_,_,hcard,_⟩ :=
    original_borel_elementary_orders_and_paths_of_source h hc hb hcomm helem
  have hmc := elementary_comparison_core_card h hm e
  change Nat.card (twoCore (commonBorel L S)) = _ at hmc
  rw [hcard] at hmc
  have he : 2^(6*n) = 2^(6*m) := by
    convert hmc using 1 <;> simp only [←pow_mul,←pow_add] <;> congr 1 <;> omega
  have hnm : n=m := by
    have hh := Nat.pow_right_injective (by decide : 1<2) he
    omega
  subst n
  by_contra hnot
  have hm1 : m=1 := by omega
  apply hnb
  simpa only [hm1,pow_one] using hbeta


/-- The original nonbinary elementary branch, with the full Borel restored
and the original reduced maps retained on both endpoints. -/
theorem elementary_nonbinary_original_comparison
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ (m : ℕ) (hm : 0<m) (hmgt : 1<m),
      ∃ e : Iso A (UnitaryFourNative.amalgam m hm false),
      ∃ f : Iso (originalAmalgam L S) (UnitaryFourNative.extension h m hm false e hmgt).amalgam,
        (∀ b : commonBorel L S,
          (f.middle b : MulAut (GreenBook.LieModels.UnitaryFour.ProjectiveGroup m hm)) =
            completionAction h (UnitaryFourNative.reducedCompletion m hm false e)
              (UnitaryFourNative.reduced_preserved h m hm false e hmgt) b) ∧
        (∀ x : parabolic L (reducedSylow L S) 0,
          (f.left (inclusion (reduced_parabolic_le h 0) x) :
            MulAut (GreenBook.LieModels.UnitaryFour.ProjectiveGroup m hm)) =
              MulAut.conj (e.left x).val) ∧
        (∀ x : parabolic L (reducedSylow L S) 1,
          (f.right (inclusion (reduced_parabolic_le h 1) x) :
            MulAut (GreenBook.LieModels.UnitaryFour.ProjectiveGroup m hm)) =
              MulAut.conj (e.right x).val) := by
  obtain ⟨m,hm,⟨e⟩⟩ := original_elementary_nonbinary_reduced_comparison
    h hc hb hcomm helem hnb
  have hmgt := elementary_comparison_nonbinary h hc hb hcomm helem hnb hm e
  exact ⟨m,hm,hmgt,e,UnitaryFourNative.exists_original_extension_iso h m hm false e hmgt⟩

/-- A finite faithful completion of the original elementary branch, with
intersection equal to the image of the entire original Borel. -/
theorem elementary_nonbinary_original_finite_completion
    (hnb : ¬ ClassicalGroup.IsPSL
      ((graphLocalGroup F (base F true)).map (G₀).subtype ⧸
        pCore 2 ((graphLocalGroup F (base F true)).map (G₀).subtype)) 2 2) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X),
      ∃ c : FaithfulCompletion (originalAmalgam L S) (G := X),
        c.left.range ⊓ c.right.range = c.middle.range := by
  obtain ⟨m,hm,hmgt,e,f,_⟩ := elementary_nonbinary_original_comparison h hc hb hcomm helem hnb
  let E := UnitaryFourNative.extension h m hm false e hmgt
  have hg := (UnitaryFourNative.model m hm false).generated
  rw [UnitaryFourNative.model_left_range,UnitaryFourNative.model_right_range] at hg
  refine ⟨E.carrier,inferInstance,inferInstance,(E.completion hg).comapIso f,?_⟩
  simpa only [FaithfulCompletion.comapIso_left_range,FaithfulCompletion.comapIso_right_range,
    FaithfulCompletion.comapIso_middle_range] using E.completion_overlap hg

end CFSG.Quasithin.ChapterF.Source.DGS85.ShortRoute
