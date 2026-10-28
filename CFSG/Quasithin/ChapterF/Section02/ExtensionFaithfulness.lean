module

public import CFSG.Quasithin.ChapterF.Section02.UniversalAutomorphisms.Complete
public import Theory.GroupTheory.LocalCentralizerSylow
import all CFSG.Quasithin.ChapterF.Section02

/-!
# Faithfulness for the repaired amalgam extension

This module supplies the kernel argument for the sound version of
Aschbacher--Smith F.2.11 used in F.4.23(5). A kernel element of the local
extension action centralizes the smaller vertex. The additional condition
`C_{Y_d}(X_d) ≤ Y_e` puts it in the least vertex, where source condition (e)
kills it. The condition follows from the Sylow, quotient and center hypotheses
available in the finite Lie-amalgam application.

We also construct the inner completion and prove F.2.11(4) when the completion
is centerless. The unrestricted source statement remains refuted in
`Section02.Obstruction`; centerlessness is used only for the final equivalence.
-/

public section
namespace CFSG.Quasithin.ChapterF
universe u v w

namespace AmalgamCompletion
variable {D : Type u} [PartialOrder D] {A : D → Type v} [∀ d, Group (A d)]
variable {δ : AmalgamDiagram D A} {G H : Type w} [Group G] [Group H]

/-- A surjective image of a completion is a completion. -/
def mapSurjective (μ : AmalgamCompletion δ G) (f : G →* H)
    (hf : Function.Surjective f) : AmalgamCompletion δ H where
  map d := f.comp (μ.map d)
  compatible h := by rw [MonoidHom.comp_assoc, μ.compatible h]
  generated := by
    have ht := congrArg (Subgroup.map f) μ.generated
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective f hf] at ht
    simpa only [Set.image_iUnion, ← Set.range_comp, MonoidHom.coe_comp] using ht

/-- The completion obtained by conjugating the original vertex images. -/
def innerCompletion (μ : AmalgamCompletion δ G) :
    AmalgamCompletion δ (MulAut.conj : G →* MulAut G).range :=
  μ.mapSurjective (MulAut.conj : G →* MulAut G).rangeRestrict
    (MulAut.conj : G →* MulAut G).rangeRestrict_surjective

@[simp] theorem innerCompletion_map (μ : AmalgamCompletion δ G) (d : D) (x : A d) :
    (μ.innerCompletion.map d x).val = MulAut.conj (μ.map d x)  := by rfl

private theorem conj_injective_of_center_eq_bot
    (hz : Subgroup.center G = ⊥) : Function.Injective (MulAut.conj : G →* MulAut G) := by
  apply (MulAut.conj : G →* MulAut G).ker_eq_bot_iff.mp
  apply bot_unique
  intro g hg
  have hc : g ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro x
    have he := DFunLike.congr_fun hg x
    change g * x * g⁻¹ = x at he
    exact ((mul_inv_eq_iff_eq_mul).mp he).symm
  simpa only [hz] using hc

/-- F.2.11(4): the inner completion is equivalent to the original one when
its ambient group is centerless. No faithfulness assumption is needed here. -/
noncomputable def equivalenceInnerOfCenterEqBot (μ : AmalgamCompletion δ G)
    (hz : Subgroup.center G = ⊥) : CompletionEquivalence μ μ.innerCompletion where
  equiv := MonoidHom.ofInjective (conj_injective_of_center_eq_bot hz)
  commutes d := by ext x; rfl

/-- In a centerless group a faithful completion remains faithful after conjugation. -/
theorem innerCompletion_faithful_of_center_eq_bot (μ : AmalgamCompletion δ G)
    (hμ : μ.Faithful) (hz : Subgroup.center G = ⊥) : μ.innerCompletion.Faithful := by
  intro d x y hxy
  apply hμ d
  apply conj_injective_of_center_eq_bot hz
  exact congrArg Subtype.val hxy
end AmalgamCompletion

namespace YAmalgam.NormalIn
variable {D : Type u} [PartialOrder D] {Y : Type v} [Group Y]
variable {X : Subgroup Y} {α : YAmalgam D X} {γ : YAmalgam D Y}
variable (h : α.NormalIn γ) {e : D} (he : ∀ d, e ≤ d)
variable {U G : Type w} [Group U] [Group G]
variable (uc : UniversalCompletion α.diagram U) (μ : AmalgamCompletion α.diagram G)

/-- The smaller vertex regarded as a normal subgroup of the larger vertex. -/
abbrev localSubgroup (d : D) : Subgroup (γ.subgroup d) :=
  ((α.subgroup d).map X.subtype).subgroupOf (γ.subgroup d)

/-- The faithful identification of the original vertex with its local subgroup. -/
noncomputable def localEquiv (d : D) : α.subgroup d ≃* localSubgroup (α := α) (γ := γ) d :=
  ((α.subgroup d).equivMapOfInjective X.subtype Subtype.val_injective).trans
    (Subgroup.subgroupOfEquivOfLe (h.le d)).symm

@[simp] theorem localEquiv_apply (d : D) (x : α.subgroup d) :
    (((h.localEquiv d x : localSubgroup (α := α) (γ := γ) d) : γ.subgroup d) : Y) =
      (x : X) := by
  exact Subgroup.coe_equivMapOfInjective_apply (α.subgroup d) X.subtype Subtype.val_injective x

/-- The original completion map transported to the local normal subgroup. -/
noncomputable def localMap (d : D) : localSubgroup (α := α) (γ := γ) d →* G :=
  (μ.map d).comp (h.localEquiv d).symm.toMonoidHom

@[simp] theorem localMap_localEquiv (d : D) (x : α.subgroup d) :
    h.localMap μ d (h.localEquiv d x) = μ.map d x := by
  simp only [localMap, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]

theorem localMap_injective (hμ : μ.Faithful) (d : D) :
    Function.Injective (h.localMap μ d) :=
  (hμ d).comp (h.localEquiv d).symm.injective

/-- Descent of least-vertex conjugation, under source hypothesis (d). -/
noncomputable def leastAction
    (hs : ∀ y, h.conjugation he y ∈ uc.kernelStabilizer μ) :
    γ.subgroup e →* MulAut G :=
  (uc.piMinus μ).comp ((h.conjugation he).codRestrict _ hs)

@[simp] theorem leastAction_map
    (hs : ∀ y, h.conjugation he y ∈ uc.kernelStabilizer μ)
    (y : γ.subgroup e) (d : D) (x : α.subgroup d) :
    h.leastAction he uc μ hs y (μ.map d x) = μ.map d ((h.conjugation he y).map d x) :=
  uc.piMinus_map μ _ d x

/-- Source condition (e) makes the descended least-vertex action faithful. -/
theorem leastAction_injective
    (hs : ∀ y, h.conjugation he y ∈ uc.kernelStabilizer μ)
    (hμ : μ.Faithful)
    (hc : (⨅ d, (Subgroup.centralizer
      (((α.subgroup d).map X.subtype : Subgroup Y) : Set Y)).comap
        (γ.subgroup e).subtype) = ⊥) :
    Function.Injective (h.leastAction he uc μ hs) := by
  have hi : Function.Injective (h.conjugation he) :=
    (h.conjugation he).ker_eq_bot_iff.mp ((h.conjugation_ker he).trans hc)
  intro a b hab
  apply hi
  exact congrArg Subtype.val (uc.piMinus_injective μ hμ hab)

/-- The descended least-vertex action restricts to the prescribed inner action. -/
theorem leastAction_leastInclusion
    (hs : ∀ y, h.conjugation he y ∈ uc.kernelStabilizer μ)
    (x : α.subgroup e) :
    h.leastAction he uc μ hs (h.leastInclusion x) = MulAut.conj (μ.map e x) := by
  change uc.piMinus μ _ = _
  have heq : ((h.conjugation he).codRestrict _ hs) (h.leastInclusion x) =
      h.innerConjugationToStabilizer he uc μ x := by
    apply Subtype.ext
    simp only [MonoidHom.codRestrict_apply,
      innerConjugationToStabilizer_apply, innerConjugation_apply]
  rw [heq, h.piMinus_innerConjugation he uc μ x]
  ext z
  rfl

/-- Conjugation in a larger vertex acts on its normal smaller vertex. -/
def localConjugation (d : D) :
    γ.subgroup d →* MulAut (localSubgroup (α := α) (γ := γ) d) :=
  let := h.normal d
  MulAut.conjNormal

@[simp] theorem localConjugation_apply (d : D) (y : γ.subgroup d)
    (x : localSubgroup (α := α) (γ := γ) d) :
    (h.localConjugation d y x : γ.subgroup d) = y * x * y⁻¹ := by rfl

/-- The repaired kernel argument at one vertex. Equivariance and the extra
local centralizer containment promote faithfulness on `Y_e` to `Y_d`. -/
theorem localAction_injective (hμ : μ.Faithful) (d : D)
    (ρ : γ.subgroup d →* MulAut G)
    (hcompat : ∀ y x, h.localMap μ d (h.localConjugation d y x) =
      ρ y (h.localMap μ d x))
    (hcentralizer : Subgroup.centralizer
      (localSubgroup (α := α) (γ := γ) d : Set (γ.subgroup d)) ≤
        (γ.subgroup e).subgroupOf (γ.subgroup d))
    (hfaithful : Function.Injective (ρ.comp (γ.diagram.map (he d)))) :
    Function.Injective ρ := by
  let := h.normal d
  apply Theory.GroupTheory.automorphismHom_injective_of_local_centralizer
    ((γ.subgroup e).subgroupOf (γ.subgroup d))
    (localSubgroup (α := α) (γ := γ) d)
    (h.localMap μ d) (h.localMap_injective μ hμ d) ρ hcompat hcentralizer
  intro a b hab
  let E := Subgroup.subgroupOfEquivOfLe (γ.le (he d))
  have heq : E a = E b := hfaithful hab
  exact E.injective heq

/-- Assembly of faithfulness once the local extension maps have been constructed.
The hypotheses are source (d), source (e), local equivariance, agreement at the
least vertex, and the additional local centralizer condition. -/
theorem extensionMaps_injective
    (hs : ∀ y, h.conjugation he y ∈ uc.kernelStabilizer μ)
    (hμ : μ.Faithful)
    (hc : (⨅ d, (Subgroup.centralizer
      (((α.subgroup d).map X.subtype : Subgroup Y) : Set Y)).comap
        (γ.subgroup e).subtype) = ⊥)
    (ρ : ∀ d, γ.subgroup d →* MulAut G)
    (hcompat : ∀ d y x, h.localMap μ d (h.localConjugation d y x) =
      ρ d y (h.localMap μ d x))
    (hrestrict : ∀ d y, ρ d (γ.diagram.map (he d) y) =
      h.leastAction he uc μ hs y)
    (hcentralizer : ∀ d, Subgroup.centralizer
      (localSubgroup (α := α) (γ := γ) d : Set (γ.subgroup d)) ≤
        (γ.subgroup e).subgroupOf (γ.subgroup d)) :
    ∀ d, Function.Injective (ρ d) := by
  intro d
  apply h.localAction_injective he μ hμ d (ρ d) (hcompat d) (hcentralizer d)
  intro a b hab
  apply h.leastAction_injective he uc μ hs hμ hc
  simpa only [MonoidHom.comp_apply, hrestrict] using hab

/-- F.2.11(3) follows from the faithful local extension maps and their restriction
formula, without assuming that the whole completion is centerless. -/
theorem innerCompletion_faithful_of_extensionMaps
    (ρ : ∀ d, γ.subgroup d →* MulAut G)
    (hρ : ∀ d, Function.Injective (ρ d))
    (hrestrict : ∀ d x,
      ρ d (h.localEquiv d x : γ.subgroup d) = MulAut.conj (μ.map d x)) :
    μ.innerCompletion.Faithful := by
  intro d x y hxy
  apply (h.localEquiv d).injective
  apply Subtype.ext
  apply hρ d
  rw [hrestrict, hrestrict]
  exact congrArg Subtype.val hxy

/-- The source-specific two-local hypotheses imply the missing containment.
No finiteness is needed when the quotient two-group condition is supplied. -/
theorem localCentralizer_le_of_sylow
    (d : D)
    (hq : letI := h.normal d;
      IsPGroup 2 ((γ.subgroup d) ⧸ localSubgroup (α := α) (γ := γ) d))
    (hz : IsPGroup 2 (Subgroup.center (α.subgroup d)))
    (S : Sylow 2 (γ.subgroup d))
    (hS : (S : Subgroup (γ.subgroup d)) =
      (γ.subgroup e).subgroupOf (γ.subgroup d)) :
    Subgroup.centralizer
      (localSubgroup (α := α) (γ := γ) d : Set (γ.subgroup d)) ≤
        (γ.subgroup e).subgroupOf (γ.subgroup d) := by
  let := h.normal d
  rw [← hS]
  exact Theory.GroupTheory.centralizer_le_sylow_of_quotient_center _ hq
    (hz.of_equiv (Subgroup.centerCongr (h.localEquiv d))) S

include h in
/-- The finite index-at-most-two version used for the exceptional Lie amalgams. -/
theorem localCentralizer_le_of_index_le_two
    (d : D) [Finite (γ.subgroup d)]
    (hi : (localSubgroup (α := α) (γ := γ) d).index ≤ 2)
    (hz : IsPGroup 2 (Subgroup.center (α.subgroup d)))
    (S : Sylow 2 (γ.subgroup d))
    (hS : (S : Subgroup (γ.subgroup d)) =
      (γ.subgroup e).subgroupOf (γ.subgroup d)) :
    Subgroup.centralizer
      (localSubgroup (α := α) (γ := γ) d : Set (γ.subgroup d)) ≤
        (γ.subgroup e).subgroupOf (γ.subgroup d) := by
  let := h.normal d
  rw [← hS]
  exact Theory.GroupTheory.centralizer_le_sylow_of_index_le_two _ hi
    (hz.of_equiv (Subgroup.centerCongr (h.localEquiv d))) S

end YAmalgam.NormalIn
end CFSG.Quasithin.ChapterF
