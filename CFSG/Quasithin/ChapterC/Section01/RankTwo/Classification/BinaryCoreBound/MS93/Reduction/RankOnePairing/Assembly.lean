module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.LocalStructure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Reduction.RankOnePairing.Incidence

/-!
# Original MS93 (1.7) over the binary field

`theorem_1_7_i` proves the five fixed-space conclusions, including an actual
equivariant isomorphism U/C_U(W) ≃ Z. `theorem_1_7_ii` constructs the dual
coordinates and proves [U,w] = C_Z(Q_alpha) for precisely the elements in
C_W(X_alpha) outside C_W(U). The latter retains the printed assumption that
U/C_U(W) is natural for L.

First `SourceData.localFacts` discharges every local-structure premise of
the incidence argument from the marked extension and source subgroup data.
In case (i), the fixed pencil propagates centralizers and gives [W,L,U] = 1.
Irreducibility makes every nonzero commutator evaluation onto Z, and the
binary seed makes its kernel exactly C_U(W). Evaluation therefore supplies
the intrinsic quotient isomorphism and its actual conjugation formula.
`fixedNaturalFactor` gives the same module in coordinates, with Z's marking.
In case (ii), the graph-automorphism argument constructs the contragredient
coordinates, and the dual pencil gives the local commutator identity.

No MS3, characteristic minimality, ambient normality of X_alpha, two-group
kernel, additional local facts or pencil identities are assumed. The local
normalizers and untilded O^{2′} residuals remain those of the source, even
when E/Q has odd order. A common quotient marking and arbitrary flag are
retained throughout, including either natural/dual orientation of Z.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.7), printed pp.847--848; extension and local notation on
pp.828--829,832. Applications to quotient groups occur in (4.3), pp.883--890.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
open Subgroup
open scoped commutatorElement
universe u
variable {M : Type u} [Group M] [Finite M]
variable {e : Extension (M := M)} {i : Bool} {Z W X : Subgroup M} [Z.Normal] [W.Normal]

namespace SourceData

/-- Every local-structure premise of the incidence argument follows from
(WBN), (A), the common Sylow choice and the source natural subgroup. -/
theorem localFacts (d : SourceData e i Z W X) : Incidence.LocalFacts e Z where
  core_le := extensionCore_le_localParabolic e
  core_eq j := (selectedCore_eq_localCore e j).symm
  parabolic_image := localParabolic_map e
  residual_image := localResidual_map e
  core_image := localCore_map e
  generation := localParabolic_generation e
  component_normal := component_normal e
  component_image := component_map _ e.base.surjective _
  z_central := d.z_le_centralizer_extensionCore
  z_irreducible := d.natural_irreducible

/-- The pairing has a noncentral second argument; this is proved from the
source's nontrivial commutator hypothesis. -/
theorem exists_noncentral (d : SourceData e i Z W X) :
    ∃ w : W, (w : M) ∉ centralizer (generated X : Set M) := by
  classical
  by_contra h
  have hW : W ≤ centralizer (generated X : Set M) := by
    intro w hw
    by_contra hn
    exact h ⟨⟨w, hw⟩, hn⟩
  apply d.generated_commutator_ne_bot
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr hW

/-- Every noncentral evaluation in case (i) maps onto the actual Z. -/
theorem fixed_evaluation_surjective (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥)
    (w : W) (hw : (w : M) ∉ centralizer (generated X : Set M)) :
    Function.Surjective (evaluation (generated X) W Z d.generated_commutator
      (d.localFacts.z_central_generated d) w) :=
  evaluation_surjective (generated X) W Z d.generated_commutator
    (d.localFacts.z_central_generated d) (component e.projection e.flag)
    (Incidence.fixed_case d d.localFacts h).2.1 d.natural_irreducible w hw

/-- Evaluation at any noncentral w constructs the source quotient isomorphism.
The denominator is intrinsically C_U(W), not an abstract isomorphic subgroup. -/
noncomputable def fixedQuotientEquiv (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥)
    (w : W) (hw : (w : M) ∉ centralizer (generated X : Set M)) :
    generated X ⧸ leftRadical (generated X) W ≃* Z :=
  evaluationQuotientEquiv (generated X) W Z d.generated_commutator
    (d.localFacts.z_central_generated d) w
    ((Incidence.fixed_case d d.localFacts h).2.2.2 w hw)
    (d.fixed_evaluation_surjective h w hw)

@[simp] theorem fixedQuotientEquiv_apply (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥)
    (w : W) (hw : (w : M) ∉ centralizer (generated X : Set M)) (x : generated X) :
    (d.fixedQuotientEquiv h w hw
      (QuotientGroup.mk' (leftRadical (generated X) W) x) : M) =
      ⁅(w : M), (x : M)⁆ := rfl

/-- This is equivariance for the actual conjugation actions, expressed on
arbitrary quotient representatives. In characteristic two the group
isomorphism is also GF(2)-linear. -/
theorem fixedQuotientEquiv_conj (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥)
    (w : W) (hw : (w : M) ∉ centralizer (generated X : Set M))
    (l : M) (hl : l ∈ component e.projection e.flag) (x y : generated X)
    (hy : (y : M) = l * (x : M) * l⁻¹) :
    (d.fixedQuotientEquiv h w hw
      (QuotientGroup.mk' (leftRadical (generated X) W) y) : M) =
      l * (d.fixedQuotientEquiv h w hw
        (QuotientGroup.mk' (leftRadical (generated X) W) x) : M) * l⁻¹ :=
  evaluationQuotientEquiv_conj (generated X) W Z d.generated_commutator
    (d.localFacts.z_central_generated d) (component e.projection e.flag)
    (Incidence.fixed_case d d.localFacts h).2.1 w
    ((Incidence.fixed_case d d.localFacts h).2.2.2 w hw)
    (d.fixed_evaluation_surjective h w hw) l hl x y hy

/-- Case (i) also gives actual natural coordinates on U/C_U(W), using
exactly the marking of Z. This construction is useful when a later pairing
application needs a natural-factor witness. -/
noncomputable def fixedNaturalFactor (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥)
    (w : W) (hw : (w : M) ∉ centralizer (generated X : Set M)) :
    NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set M)) where
  marking := d.natural.marking
  coordinates := d.natural.coordinates.comp (evaluation (generated X) W Z
    d.generated_commutator (d.localFacts.z_central_generated d) w)
  surjective := d.natural.surjective.comp (d.fixed_evaluation_surjective h w hw)
  kernel := by
    have hk := evaluation_ker_of_cyclic (generated X) W Z d.generated_commutator
      (d.localFacts.z_central_generated d) w
      ((Incidence.fixed_case d d.localFacts h).2.2.2 w hw)
    ext x
    change d.natural.coordinates _ = 1 ↔
      x ∈ (centralizer (W : Set M)).subgroupOf (generated X)
    have hinj : Function.Injective d.natural.coordinates := d.natural.equivOfBot.injective
    rw [← d.natural.coordinates.map_one, hinj.eq_iff]
    exact SetLike.ext_iff.mp hk x
  normalized := le_normalizer_of_normal
  action l hl x y hy := d.natural.action l hl _ _
    (evaluation_conj (generated X) W Z d.generated_commutator
      (d.localFacts.z_central_generated d) (component e.projection e.flag)
      (Incidence.fixed_case d d.localFacts h).2.1 l hl w x y hy)

@[simp] theorem fixedNaturalFactor_marking (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥)
    (w : W) (hw : (w : M) ∉ centralizer (generated X : Set M)) :
    (d.fixedNaturalFactor h w hw).marking = d.natural.marking := rfl

/-- Compatible inverse-transpose coordinates in case (ii), with every
local-structure premise discharged. The natural quotient is exactly the
additional hypothesis printed in this branch. -/
noncomputable def dualFactor (d : SourceData e i Z W X)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set M)))
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥) :
    DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural :=
  Duality.contragredient d n (component_map _ e.base.surjective _)
    d.z_le_centralizer_extensionCore h

end SourceData

/-- Original MS93 (1.7)(i), q=2. All five conclusions follow from the source
hypotheses. The displayed isomorphism uses the intrinsic centralizer quotient
and intertwines ambient conjugation on arbitrary representatives. -/
theorem theorem_1_7_i (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) ≠ ⊥) :
    ⁅fixedPreimage (component e.projection e.flag) X Z, W⁆ = ⊥ ∧
    ⁅⁅W, component e.projection e.flag⁆, generated X⁆ = ⊥ ∧
    (∃ f : generated X ⧸ leftRadical (generated X) W ≃* Z,
      ∀ l ∈ component e.projection e.flag, ∀ x y : generated X,
        (y : M) = l * (x : M) * l⁻¹ →
        (f (QuotientGroup.mk' (leftRadical (generated X) W) y) : M) =
          l * (f (QuotientGroup.mk' (leftRadical (generated X) W) x) : M) * l⁻¹) ∧
    W ⊓ centralizer (X : Set M) = W ⊓ centralizer (generated X : Set M) ∧
    ∀ w : W, (w : M) ∉ centralizer (generated X : Set M) →
      ⁅generated X, zpowers (w : M)⁆ = Z := by
  obtain ⟨hCW, htriple, hcent, _⟩ := Incidence.fixed_case d d.localFacts h
  refine ⟨hCW, htriple, ?_, hcent, ?_⟩
  · obtain ⟨w, hw⟩ := d.exists_noncentral
    exact ⟨d.fixedQuotientEquiv h w hw, d.fixedQuotientEquiv_conj h w hw⟩
  · intro w hw
    exact commutator_eq_of_evaluation_surjective (generated X) W Z
      d.generated_commutator (d.localFacts.z_central_generated d) w
      (d.fixed_evaluation_surjective h w hw)

/-- Original MS93 (1.7)(ii), q=2. The constructed dual factor has kernel
C_U(W) and inverse-transpose action for Z's own quotient marking. The
commutator value is the fixed subgroup of the actual local two-core. -/
theorem theorem_1_7_ii (d : SourceData e i Z W X)
    (h : Z ⊓ centralizer (localResidual (localParabolic e i) : Set M) = ⊥)
    (n : NaturalFactor e.projection (component e.projection e.flag)
      (generated X) (centralizer (W : Set M))) :
    Nonempty (DualFactor e.projection (component e.projection e.flag) (generated X)
      (centralizer (W : Set M)) Z d.natural) ∧
    ∀ w : ↥(W ⊓ centralizer (X : Set M)),
      (w : M) ∉ centralizer (generated X : Set M) →
      ⁅generated X, zpowers (w : M)⁆ =
        Z ⊓ centralizer (localCore (localParabolic e i) : Set M) :=
  ⟨⟨d.dualFactor n h⟩, fun w hw =>
    Incidence.dual_case d d.localFacts (d.dualFactor n h) h w hw⟩

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.RankOnePairing
