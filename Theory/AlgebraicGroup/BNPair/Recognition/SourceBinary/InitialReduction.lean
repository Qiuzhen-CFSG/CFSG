module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.NormalGeneration
public import Theory.GroupTheory.Amalgam.LocalStructure

/-!
# The literal initial Fong–Seitz quotient

Fong–Seitz first passes from Y to G₀ = U^Y and then factors the normal
core Z of B ∩ G₀ IN G₀. If U normally generates Y and B has trivial normal
core, this relative Z is trivial. The canonical equivalence G₀/Z ≃ Y
sends each quotient representative to its original element. Consequently
it preserves the actual Borel, normalizer, unipotent group and both marked
parabolics, and gives an isomorphism of inclusion amalgams with both squares.

These are conditional transport results at the exact Theorem A reduction;
no Lie recognition is assumed. MinimalConfiguration supplies both premises
from the original F.1.1 marking, including the nonperfect endpoint cases.

Source: Fong–Seitz I, Invent. Math. 21 (1973), Theorem A and (1A)–(1B),
pp.1–3; DGS, Groups and Graphs, pp.80–81 and224. Subgroups are intersected
with G₀ before the quotient is taken, so no ambient normal-core convention
is substituted for the relative source convention.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
variable {Y : Type*} [Group Y] {T : Theory.AlgebraicGroup.TitsSystem (X := Y)}
  (split : SplitData T)

/-- Fong–Seitz's Z is the normal core of B ∩ G₀ inside G₀, not inside the original carrier. -/
@[expose] def initialCore : Subgroup split.unipotentClosure :=
  (T.B.subgroupOf split.unipotentClosure).normalCore

/-- The relative Borel core is normal in the unipotent normal closure. -/
instance initialCore_normal : split.initialCore.Normal := inferInstanceAs
  (T.B.subgroupOf split.unipotentClosure).normalCore.Normal

/-- The actual carrier G₀/Z of Fong–Seitz I, Theorem A. -/
abbrev InitialQuotient := split.unipotentClosure ⧸ split.initialCore

/-- Intersect with G₀ and then take the image under the same quotient map G₀ → G₀/Z. -/
@[expose] def initialSubgroup (H : Subgroup Y) : Subgroup split.InitialQuotient :=
  (H.subgroupOf split.unipotentClosure).map (QuotientGroup.mk' split.initialCore)

/-- Normal generation and a core-free Borel kill the relative core used in Theorem A. -/
theorem initialCore_eq_bot (hgen : split.unipotentClosure = ⊤)
    (hcore : T.B.normalCore = ⊥) : split.initialCore = ⊥ := by
  apply eq_bot_iff.mpr
  intro z hz
  apply Subtype.ext
  apply mem_bot.mp
  rw [← hcore]
  intro g
  exact hz ⟨g, hgen ▸ mem_top g⟩

/-- The initial reduction is canonically the given carrier when its reduction hypotheses hold. -/
@[expose] def initialEquiv (hgen : split.unipotentClosure = ⊤)
    (hcore : T.B.normalCore = ⊥) : split.InitialQuotient ≃* Y :=
  ((QuotientGroup.quotientMulEquivOfEq (split.initialCore_eq_bot hgen hcore)).trans
    QuotientGroup.quotientBot).trans
      ((MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv)

/-- The equivalence is the original inclusion on every quotient representative. -/
@[simp] theorem initialEquiv_mk (hgen : split.unipotentClosure = ⊤)
    (hcore : T.B.normalCore = ⊥) (x : split.unipotentClosure) :
    split.initialEquiv hgen hcore (QuotientGroup.mk' split.initialCore x) = (x : Y) := by
  rfl

/-- Every literal reduced subgroup, including B, N and both parabolics, returns to the original one. -/
theorem initialEquiv_subgroup (hgen : split.unipotentClosure = ⊤)
    (hcore : T.B.normalCore = ⊥) (H : Subgroup Y) :
    (split.initialSubgroup H).map (split.initialEquiv hgen hcore).toMonoidHom = H := by
  rw [initialSubgroup, map_map]
  have he : (split.initialEquiv hgen hcore).toMonoidHom.comp
      (QuotientGroup.mk' split.initialCore) = split.unipotentClosure.subtype := by
    ext x
    exact split.initialEquiv_mk hgen hcore x
  rw [he, map_subgroupOf_eq_of_le (show H ≤ split.unipotentClosure by rw [hgen]; exact le_top)]

/-- The inverse equivalence is the canonical restriction-then-quotient operation on subgroups. -/
theorem initialEquiv_symm_subgroup (hgen : split.unipotentClosure = ⊤)
    (hcore : T.B.normalCore = ⊥) (H : Subgroup Y) :
    H.map (split.initialEquiv hgen hcore).symm.toMonoidHom = split.initialSubgroup H := by
  apply map_injective (f := (split.initialEquiv hgen hcore).toMonoidHom)
    (split.initialEquiv hgen hcore).injective
  rw [split.initialEquiv_subgroup hgen hcore]
  have he : (split.initialEquiv hgen hcore).toMonoidHom.comp
      (split.initialEquiv hgen hcore).symm.toMonoidHom = MonoidHom.id Y := by
    ext x
    exact (split.initialEquiv hgen hcore).apply_symm_apply x
  rw [map_map, he, map_id]

/-- Apply the same initial reduction to both endpoints and the entire middle group. -/
@[expose] def initialAmalgam (P₀ B P₁ : Subgroup Y) (h₀ : B ≤ P₀) (h₁ : B ≤ P₁) :=
  RankTwoAmalgam.ofSubgroups (split.initialSubgroup P₀) (split.initialSubgroup B)
    (split.initialSubgroup P₁) (map_mono (comap_mono h₀)) (map_mono (comap_mono h₁))

/-- Both inclusion squares survive the initial reduction; the three isomorphisms use one ambient map. -/
@[expose] def initialAmalgamIso (hgen : split.unipotentClosure = ⊤)
    (hcore : T.B.normalCore = ⊥) (P₀ B P₁ : Subgroup Y) (h₀ : B ≤ P₀) (h₁ : B ≤ P₁) :
    RankTwoAmalgam.Iso (RankTwoAmalgam.ofSubgroups P₀ B P₁ h₀ h₁)
      (split.initialAmalgam P₀ B P₁ h₀ h₁) :=
  RankTwoAmalgam.ofSubgroupsIso (split.initialEquiv hgen hcore).symm h₀ h₁
    (map_mono (comap_mono h₀)) (map_mono (comap_mono h₁))
    (split.initialEquiv_symm_subgroup hgen hcore P₀)
    (split.initialEquiv_symm_subgroup hgen hcore B)
    (split.initialEquiv_symm_subgroup hgen hcore P₁)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.SplitData
