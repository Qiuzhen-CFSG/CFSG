module
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.SuzukiRecognition.Reduction
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.Suzuki.Model
public import Theory.Representation.Suzuki.NaturalMatrix
public import Theory.Representation.Suzuki.SmallDegree

/-!
# Natural Suzuki module recognition on the source domain

The source hypotheses and the actual central quotient give a faithful,
irreducible representation of the matrix Suzuki group with binary dimension
strictly below 10(2m+1). This module converts the small-degree representation
classification into the literal natural-module identification, retaining the
original central projection in the group marking.

The proved small-degree classifier selects the natural representation,
including for Sz(8), with an actual binary intertwiner on the original matrix
group. Thus the source hypotheses alone construct the natural-module model
and give its exact binary dimension 4(2m+1). The conditional assembly API is
retained alongside this unconditional recognition.

Source: Aschbacher–Smith, K.3.5–K.3.6, printed p.457; Guralnick–Malle,
*Classification of 2F-modules, II*, Theorem 8.1, Lemma 8.3 and Table 17.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterK.RankOne
open BenderSuzuki BenderSuzuki.MatrixGroups PFAppendixIII Representation

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

namespace SourceHypotheses
variable (h : SourceHypotheses ρ L) {m : ℕ} (hm : 1 ≤ m)
  (e : (L ⧸ Subgroup.center L) ≃* SuzukiMatrixGroup m)

/-- Turn a genuine representation equivalence into the source's matrix model.
The group marking is precisely the one induced by the central projection. -/
noncomputable def suzukiModelOfEquiv
    (E : (h.suzukiRepresentation hm e).Equiv (SuzukiNatural.natural m)) :
    SuzukiModel m ρ L where
  groupEquiv := h.suzukiEquiv hm e
  coordinates := E.toLinearEquiv
  intertwines g v := by
    have he := LinearMap.congr_fun (E.isIntertwining' (h.suzukiEquiv hm e g)) v
    simpa only [LinearMap.comp_apply, suzukiRepresentation_apply,
      SuzukiNatural.natural_apply, Representation.Equiv.toLinearEquiv_apply,
      Representation.IntertwiningMap.toLinearMap_apply] using he

/-- The literal source quotient is retained by the natural-module model. -/
@[simp] theorem suzukiModelOfEquiv_groupEquiv_apply
    (E : (h.suzukiRepresentation hm e).Equiv (SuzukiNatural.natural m)) (g : L) :
    (h.suzukiModelOfEquiv hm e E).groupEquiv g = e (QuotientGroup.mk g) :=
  h.suzukiEquiv_apply hm e g

/-- In source coordinates the action is exactly multiplication by the marked matrix. -/
theorem suzukiModelOfEquiv_intertwines
    (E : (h.suzukiRepresentation hm e).Equiv (SuzukiNatural.natural m)) (g : L) (v : V) :
    E.toLinearEquiv (ρ (g : G) v) =
      Matrix.mulVec (e (QuotientGroup.mk g)).val.val (E.toLinearEquiv v) := by
  simpa only [suzukiModelOfEquiv, suzukiEquiv_apply] using
    (h.suzukiModelOfEquiv hm e E).intertwines g v

/-- A genuine natural-module equivalence gives the exact binary dimension 4r. -/
theorem suzuki_finrank_of_equiv
    (E : (h.suzukiRepresentation hm e).Equiv (SuzukiNatural.natural m)) :
    Module.finrank (ZMod 2) V = 4 * (2 * m + 1) :=
  (h.suzukiModelOfEquiv hm e E).finrank_eq

include h hm e

/-- Source assembly once the independent small-degree Suzuki classifier is proved.
All of its numerical and irreducibility hypotheses are discharged here. -/
theorem suzukiModel_of_smallDegree_classification
    (hclass : ∀ σ : Representation (ZMod 2) (SuzukiMatrixGroup m) V,
      Function.Injective σ → IsIrreducible σ →
      Module.finrank (ZMod 2) V < 10 * (2 * m + 1) →
      Nonempty (σ.Equiv (SuzukiNatural.natural m))) :
    Nonempty (SuzukiModel m ρ L) := by
  obtain ⟨E⟩ := hclass (h.suzukiRepresentation hm e)
    (h.suzukiRepresentation_faithful hm e) (h.suzukiRepresentation_irreducible hm e)
    (h.suzuki_finrank_lt_ten_mul hm e)
  exact ⟨h.suzukiModelOfEquiv hm e E⟩

/-- The source degree window selects the natural Suzuki representation.
Faithfulness, irreducibility and the strict degree bound all follow from the
original source hypotheses; the matrix group marking is unchanged. -/
noncomputable def suzukiNaturalEquiv :
    (h.suzukiRepresentation hm e).Equiv (SuzukiNatural.natural m) :=
  Classical.choice (SuzukiSmallDegree.natural_equiv_of_smallDegree hm
    (h.suzukiRepresentation hm e) (h.suzukiRepresentation_faithful hm e)
    (h.suzukiRepresentation_irreducible hm e) (h.suzuki_finrank_lt_ten_mul hm e))

/-- The natural Suzuki model required by K.3.6, constructed from the source
hypotheses and the actual central quotient, including the case Sz(8). -/
noncomputable def suzukiModel : SuzukiModel m ρ L :=
  h.suzukiModelOfEquiv hm e (h.suzukiNaturalEquiv hm e)

/-- The recognized model uses precisely the given central-quotient marking. -/
@[simp] theorem suzukiModel_groupEquiv_apply (g : L) :
    (h.suzukiModel hm e).groupEquiv g = e (QuotientGroup.mk g) :=
  h.suzukiModelOfEquiv_groupEquiv_apply hm e (h.suzukiNaturalEquiv hm e) g

/-- In the recognized binary coordinates, the layer action is literally the
matrix action of the specified central quotient. -/
theorem suzukiModel_intertwines (g : L) (v : V) :
    (h.suzukiModel hm e).coordinates (ρ (g : G) v) =
      Matrix.mulVec (e (QuotientGroup.mk g)).val.val
        ((h.suzukiModel hm e).coordinates v) :=
  h.suzukiModelOfEquiv_intertwines hm e (h.suzukiNaturalEquiv hm e) g v

/-- The Suzuki source branch has binary dimension exactly 4r, where r=2m+1. -/
theorem suzuki_finrank : Module.finrank (ZMod 2) V = 4 * (2 * m + 1) :=
  (h.suzukiModel hm e).finrank_eq

end SourceHypotheses
end CFSG.Quasithin.ChapterK.RankOne
