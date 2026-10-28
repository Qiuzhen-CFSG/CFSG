module
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.LieModels.Triality
public import Theory.SpecificGroups.Triality.StandardTwoRank.Derived
public import Theory.SpecificGroups.Triality.OuterOddSubgroups.Coverage.RootGeometry.SimpleRecognition.ParabolicIntersections
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.CoreFaithfulness
public import Theory.GroupTheory.Amalgam.RankTwoCompletion.OverlapCover
public import Mathlib.Data.Finite.Perm

/-!
# Faithful completions of the genuine triality amalgam at q = 2

The Borel has order 28672 and index three in the central endpoint. Hence the
intersection in any faithful completion is either the whole marked Borel or
the entire central endpoint. The latter makes the completion equal its arms
endpoint, of order 258048. Its faithful Borel-coset action would embed this
group in Sym(9), whose order has insufficient two-part. This proves the whole
overlap without a finiteness or noncollapse hypothesis on the completion.

The native Borel has trivial normal core. Transport through both compatible
endpoint maps gives faithfulness for every completion and the canonical common
coset covering, retaining the original odd factor of order seven.

Source: Aschbacher--Smith F.3.3--4 and F.4.6(1), pp.270,276--277. This is the
local geometric input to the triality specialization of F.4.31, not ambient
recognition. The latter remains with qt-e-14315-eight-borel-exclusion.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open Subgroup.CosetGeometry
namespace CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics
abbrev parameters := binaryParameters 1 Nat.zero_lt_one
theorem parameters_prime : parameters.prime = 2 := rfl
abbrev Model := Carrier parameters
abbrev amalgam := GreenBook.LieModels.Triality.amalgam parameters
abbrev Completion (G : Type*) [Group G] :=
  RankTwoAmalgam.FaithfulCompletion amalgam (G := G)

def modelCompletion : Completion Model :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups
    (parabolic parameters .arms) (borel parameters) (parabolic parameters .central)
    (borel_le_parabolic _ _) (borel_le_parabolic _ _)
    (parabolic_sup_binary _ rfl)

@[simp] theorem model_left_range : modelCompletion.left.range = parabolic parameters .arms := range_subtype _
@[simp] theorem model_right_range : modelCompletion.right.range = parabolic parameters .central := range_subtype _
@[simp] theorem model_middle_range : modelCompletion.middle.range = borel parameters :=
  RankTwoAmalgam.FaithfulCompletion.ofSubgroups_middle_range
    (parabolic parameters .arms) (borel parameters) (parabolic parameters .central)
    (borel_le_parabolic _ _) (borel_le_parabolic _ _) (parabolic_sup_binary _ rfl)

theorem model_overlap : modelCompletion.left.range ⊓ modelCompletion.right.range =
    modelCompletion.middle.range := by
  rw [model_left_range,model_right_range,model_middle_range]
  exact parabolic_inf_binary _ rfl

theorem model_middle_normalCore : modelCompletion.middle.range.normalCore = ⊥ := by
  rw [model_middle_range]
  exact _root_.Triality.Standard.TwoRank.Derived.normal_eq_bot_of_le_borel 1 Nat.zero_lt_one
    _ (borel parameters).normalCore_le

theorem borel_card : Nat.card (borel parameters) = 28672 := by
  simpa [parameters,Parameters.q,binaryParameters] using
    ConcreteBruhat.FixedCellCount.card_borel 1 Nat.zero_lt_one

theorem parabolic_card (i : Node) : Nat.card (parabolic parameters i) =
    if i = .arms then 258048 else 86016 := by
  have h := ((borel parameters).subgroupOf (parabolic parameters i)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe (borel_le_parabolic parameters i)).toEquiv] at h
  change Nat.card (borel parameters) * (borel parameters).relIndex (parabolic parameters i) = _ at h
  rw [borel_card,
    OuterOdd.Coverage.RootGeometry.SimpleRecognition.borel_relIndex_parabolic] at h
  cases i <;> simpa [parameters,Parameters.q,binaryParameters] using h.symm

namespace Completion
variable {G : Type*} [Group G] (c : Completion G)
abbrev family : Bool → Subgroup G := c.cosetFamily
abbrev Vertex := RankTwo.Vertex c.family
abbrev graph := RankTwo.graph c.family
@[simp] theorem family_false : c.family false = c.left.range := rfl
@[simp] theorem family_true : c.family true = c.right.range := rfl

theorem connected : c.graph.Connected := RankTwo.connected c.family c.generated

theorem left_card : Nat.card c.left.range = 258048 :=
  (RankTwoAmalgam.FaithfulCompletion.left_card c).trans (by simpa using parabolic_card .arms)
theorem right_card : Nat.card c.right.range = 86016 :=
  (RankTwoAmalgam.FaithfulCompletion.right_card c).trans (by simpa using parabolic_card .central)
theorem middle_card : Nat.card c.middle.range = 28672 := (RankTwoAmalgam.FaithfulCompletion.middle_card c).trans borel_card

theorem middle_normalCore : c.middle.range.normalCore = ⊥ :=
  c.middle_normalCore_eq_bot_of_model modelCompletion model_middle_normalCore

private theorem middle_relIndex_right : c.middle.range.relIndex c.right.range = 3 := by
  have h := (c.middle.range.subgroupOf c.right.range).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe c.middle_le_right).toEquiv,
    c.middle_card,c.right_card] at h
  change 28672 * c.middle.range.relIndex c.right.range = 86016 at h
  omega

/-- The order-three right Borel index and faithful core exclude collapsed endpoints. -/
theorem overlap : c.left.range ⊓ c.right.range = c.middle.range := by
  let I := c.left.range ⊓ c.right.range
  have hBI : c.middle.range ≤ I := le_inf c.middle_le_left c.middle_le_right
  have hi := relIndex_mul_relIndex c.middle.range I c.right.range hBI inf_le_right
  rw [c.middle_relIndex_right] at hi
  have hd : I.relIndex c.right.range ∣ 3 := ⟨c.middle.range.relIndex I,by simpa only [Nat.mul_comm] using hi.symm⟩
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd with hone | hthree
  · have hRL : c.right.range ≤ c.left.range := (relIndex_eq_one.mp hone).trans inf_le_left
    have htop : c.left.range = ⊤ := by simpa only [sup_eq_left.mpr hRL] using c.generated
    have hcG : Nat.card G = 258048 := by simpa only [htop,card_top] using c.left_card
    let : Finite G := Nat.finite_of_card_ne_zero (by rw [hcG]; decide)
    have hidx := c.middle.range.card_mul_index
    rw [c.middle_card,hcG] at hidx
    have h9 : c.middle.range.index = 9 := by omega
    have hf : Function.Injective (MulAction.toPermHom G (G ⧸ c.middle.range)) := by
      rw [←MonoidHom.ker_eq_bot_iff,←normalCore_eq_ker,c.middle_normalCore]
    have hdiv := card_dvd_of_injective _ hf
    rw [hcG,Nat.card_perm,←index_eq_card,h9] at hdiv
    norm_num at hdiv
  · rw [hthree] at hi
    have h1 : c.middle.range.relIndex I = 1 := by omega
    exact le_antisymm (relIndex_eq_one.mp h1) hBI

theorem vertex_action_injective : Function.Injective (MulAction.toPermHom G c.Vertex) := by
  rw [←MonoidHom.ker_eq_bot_iff,RankTwo.global_kernel]
  change (c.left.range ⊓ c.right.range).normalCore = ⊥
  rw [c.overlap,c.middle_normalCore]

theorem coverData : RankTwo.CoverData (RankTwoAmalgam.Universal.cosetFamily amalgam) c.family
    (RankTwoAmalgam.Universal.lift amalgam c) :=
  RankTwoAmalgam.Universal.coverData_of_overlap amalgam c c.overlap

theorem rootPathTransitive_iff_model (i : Bool) (n : ℕ) :
    SimpleGraph.PathTransitivePolygon.RootPathTransitive c.graph G (RankTwo.base c.family i) n ↔
      SimpleGraph.PathTransitivePolygon.RootPathTransitive modelCompletion.graph Model
        (RankTwo.base modelCompletion.family i) n :=
  RankTwoAmalgam.Universal.rootPathTransitive_iff_of_overlap amalgam c modelCompletion
    c.overlap model_overlap i n

end Completion
end CFSG.Quasithin.ChapterF.SourceCompletion.TrialityTwo
