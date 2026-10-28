module

public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parabolic.Model
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parabolic.Blocks
public import CFSG.Quasithin.ChapterF.Section01.GreenBook.UnitaryFive.LocalStructure.LineCore.Parabolic.Perfect

/-!
# Assembly of the parameter-four line-parabolic calculation

The radical and SU₃ have a faithful semidirect-product realization. A full
parabolic projection agreeing with its SU₃ coordinate is surjective. Together
with a character whose kernel is this split subgroup, it identifies the
unipotent subgroup as the common kernel, hence normal in the entire parabolic.

If the split subgroup is perfect and the character has solvable image, this
subgroup is the solvable residual. A surjective character to a group of order
three gives the residual index. Restricting the full projection then gives a
surjection onto SU₃ with precisely the radical coordinate group as kernel.

The full block calculation and the radical commutator calculation are supplied
by `Parabolic.Blocks` and `Parabolic.Perfect`. The named parabolic maps below
have no additional premises. The residual identification, index three and
coordinate-kernel equivalence assume only perfectness of the actual SU₃ Levi.
The source assembly owner supplies that independent fact and identifies the
kernel with the canonical two-core; this module concerns the line-parabolic
part of F.1.12(7).

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
F.1.11--12(7), printed pp.262--264. The residual is the intersection of the
derived series, taken inside the line parabolic.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
open Theory.SpecificGroups.UnitaryFive.LineCore
open Theory.SpecificGroups.UnitaryFive.LineCore.Parabolic
variable (M : Model 4)

/-- Agreement on radical-Levi matrices determines the map on their actual subgroup. -/
theorem lineLeviProjection_restrict
    (π : M.leftParabolic →* M.LocalUnitaryGroup)
    (hπ : π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom) :
    π.comp M.lineRadicalLeviSubgroup.subtype = M.lineRadicalLeviProjection := by
  apply MonoidHom.ext
  intro g
  obtain ⟨x, rfl⟩ := M.lineRadicalLeviEquiv.surjective g
  change π (M.lineRadicalLeviMap x) = _
  rw [M.lineRadicalLeviProjection_equiv x]
  exact DFunLike.congr_fun hπ x

/-- The full projection is onto as soon as it has the prescribed Levi block. -/
theorem lineLeviProjection_surjective
    (π : M.leftParabolic →* M.LocalUnitaryGroup)
    (hπ : π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom) :
    Function.Surjective π := by
  intro A
  refine ⟨M.lineRadicalLeviMap (SemidirectProduct.inr A), ?_⟩
  exact DFunLike.congr_fun hπ (SemidirectProduct.inr A)

section Character
variable {C : Type*} [Group C]
variable (χ : M.leftParabolic →* C) (hχ : χ.ker = M.lineRadicalLeviSubgroup)
include hχ

/-- The two Levi characters together have exactly the full coordinate subgroup as kernel. -/
theorem lineUnipotent_eq_ker_levi_char
    (π : M.leftParabolic →* M.LocalUnitaryGroup)
    (hπ : π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom) :
    M.lineUnipotent = (π.prod χ).ker := by
  have hπH := M.lineLeviProjection_restrict π hπ
  ext g
  constructor
  · intro hg
    have hgH := projectiveUnipotent_le_radicalLeviSubgroup M.form M.matrix hg
    have hc : χ g = 1 := by
      change g ∈ χ.ker
      rwa [hχ]
    have hq : M.lineRadicalLeviProjection ⟨g, hgH⟩ = 1 := by
      change (⟨g, hgH⟩ : M.lineRadicalLeviSubgroup) ∈ M.lineRadicalLeviProjection.ker
      rw [M.lineRadicalLeviProjection_ker]
      exact hg
    have hp : π g = 1 := (DFunLike.congr_fun hπH ⟨g, hgH⟩).trans hq
    exact Prod.ext hp hc
  · intro hg
    have hp : π g = 1 := congrArg Prod.fst hg
    have hc : χ g = 1 := congrArg Prod.snd hg
    have hgH : g ∈ M.lineRadicalLeviSubgroup := hχ ▸ hc
    have hq : M.lineRadicalLeviProjection ⟨g, hgH⟩ = 1 :=
      (DFunLike.congr_fun hπH ⟨g, hgH⟩).symm.trans hp
    change (⟨g, hgH⟩ : M.lineRadicalLeviSubgroup) ∈ M.lineRadicalLeviProjection.ker at hq
    rw [M.lineRadicalLeviProjection_ker] at hq
    exact hq

/-- Normality is in the entire parabolic once both block characters are constructed. -/
theorem lineUnipotent_normal_of_character
    (π : M.leftParabolic →* M.LocalUnitaryGroup)
    (hπ : π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom) :
    M.lineUnipotent.Normal := by
  rw [M.lineUnipotent_eq_ker_levi_char χ hχ π hπ]
  infer_instance

variable [Group.IsSolvable C] [Group.IsPerfect M.LineRadicalLevi]

/-- A perfect radical-Levi subgroup with solvable character quotient is the residual. -/
theorem leftLocal_eq_radicalLevi_of_character : M.leftLocal = M.lineRadicalLeviSubgroup := by
  have : Group.IsPerfect M.lineRadicalLeviSubgroup :=
    Group.IsPerfect.range M.lineRadicalLeviMap
  apply le_antisymm
  · have h := Subgroup.map_solvableResidual_le χ
    rw [Subgroup.solvableResidual_eq_bot (G := C), le_bot_iff, Subgroup.map_eq_bot_iff, hχ] at h
    exact h
  · exact Subgroup.le_solvableResidual_of_isPerfect M.lineRadicalLeviSubgroup

/-- The source residual has index three once the explicit character is onto. -/
theorem leftLocal_index_of_character (honto : Function.Surjective χ) (hcard : Nat.card C = 3) :
    M.leftLocal.index = 3 := by
  rw [M.leftLocal_eq_radicalLevi_of_character χ hχ, ← hχ, ← MonoidHom.comap_bot,
    (⊥ : Subgroup C).index_comap_of_surjective honto, Subgroup.index_bot, hcard]

noncomputable def leftLocalEquivRadicalLevi_of_character :
    M.leftLocal ≃* M.lineRadicalLeviSubgroup :=
  MulEquiv.subgroupCongr (M.leftLocal_eq_radicalLevi_of_character χ hχ)

/-- The full Levi map restricts to a surjection from the actual solvable residual. -/
theorem leftLocalLevi_surjective_of_character
    (π : M.leftParabolic →* M.LocalUnitaryGroup)
    (hπ : π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom) :
    Function.Surjective (π.comp M.leftLocal.subtype) := by
  let e := M.leftLocalEquivRadicalLevi_of_character χ hχ
  have hf : π.comp M.leftLocal.subtype = M.lineRadicalLeviProjection.comp e.toMonoidHom := by
    rw [← M.lineLeviProjection_restrict π hπ]
    rfl
  rw [hf]
  exact M.lineRadicalLeviProjection_surjective.comp e.surjective

/-- The actual residual restriction has the coordinate kernel, after character and perfection. -/
noncomputable def leftLocalLeviKernelEquiv_of_character
    (π : M.leftParabolic →* M.LocalUnitaryGroup)
    (hπ : π.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom) :
    (π.comp M.leftLocal.subtype).ker ≃* M.LineRadicalCoordinates := by
  let e := M.leftLocalEquivRadicalLevi_of_character χ hχ
  have hf : π.comp M.leftLocal.subtype = M.lineRadicalLeviProjection.comp e.toMonoidHom := by
    rw [← M.lineLeviProjection_restrict π hπ]
    rfl
  exact (MulEquiv.subgroupCongr
    (congrArg MonoidHom.ker hf |>.trans (M.lineRadicalLeviProjection.ker_comp_mulEquiv e))).trans
      ((e.symm.subgroupMap M.lineRadicalLeviProjection.ker).symm.trans
        M.lineRadicalLeviProjectionKernelEquiv)

end Character

/-- The actual full line-parabolic projection, using a trace-one scalar from the model. -/
noncomputable def lineParabolicProjection : M.leftParabolic →* M.LocalUnitaryGroup :=
  M.lineBlockProjection (Classical.choose M.exists_lineTraceOne)
    (Classical.choose_spec M.exists_lineTraceOne)

/-- The actual cubic character, with the same choice of Witt coordinates as the projection. -/
noncomputable def lineParabolicCharacter : M.leftParabolic →* M.LineCubic :=
  M.lineBlockCharacter (Classical.choose M.exists_lineTraceOne)
    (Classical.choose_spec M.exists_lineTraceOne)

theorem lineParabolicProjection_comp_radicalLeviMap :
    M.lineParabolicProjection.comp M.lineRadicalLeviMap = SemidirectProduct.rightHom :=
  M.lineBlockProjection_comp_radicalLeviMap _ _

/-- The prescribed SU₃ block makes the full parabolic projection surjective. -/
theorem lineParabolicProjection_surjective : Function.Surjective M.lineParabolicProjection :=
  M.lineLeviProjection_surjective _ M.lineParabolicProjection_comp_radicalLeviMap

/-- The original flag overlap is exactly the preimage of the marked middle line stabilizer. -/
theorem lineParabolicProjection_flag_preimage :
    M.localUnitaryLineStabilizer.comap M.lineParabolicProjection =
      M.overlap.subgroupOf M.leftParabolic :=
  M.lineBlockProjection_flag_preimage _ _

theorem lineParabolicCharacter_surjective : Function.Surjective M.lineParabolicCharacter :=
  M.lineBlockCharacter_surjective _ _

theorem lineParabolicCharacter_ker :
    M.lineParabolicCharacter.ker = M.lineRadicalLeviSubgroup :=
  M.lineBlockCharacter_ker _ _

/-- The full unipotent radical is the common kernel of the SU₃ and cubic coordinates. -/
theorem lineUnipotent_eq_ker_parabolicMaps :
    M.lineUnipotent = (M.lineParabolicProjection.prod M.lineParabolicCharacter).ker :=
  M.lineUnipotent_eq_ker_levi_char _ M.lineParabolicCharacter_ker
    _ M.lineParabolicProjection_comp_radicalLeviMap

/-- Normality is relative to the full line parabolic. -/
instance lineUnipotent_normal : M.lineUnipotent.Normal :=
  M.lineUnipotent_normal_of_character _ M.lineParabolicCharacter_ker
    _ M.lineParabolicProjection_comp_radicalLeviMap

/-- The actual SU₃ matrix embedding acts on the radical by its middle vector action. -/
theorem lineRadicalEmbedding_leviAction (A : M.LocalUnitaryGroup)
    (u : M.LineRadicalCoordinates) :
    M.lineRadicalEmbedding (leviAction M.form A u) =
      M.lineLeviEmbedding A * M.lineRadicalEmbedding u * (M.lineLeviEmbedding A)⁻¹ :=
  toParabolic_leviAction M.form M.matrix A u

section Residual
variable (hperfect : Group.IsPerfect M.LocalUnitaryGroup)
include hperfect

/-- Perfectness of SU₃ identifies the matrix radical–Levi subgroup with the source residual. -/
theorem leftLocal_eq_radicalLevi : M.leftLocal = M.lineRadicalLeviSubgroup := by
  let : Group.IsPerfect M.LineRadicalLevi := M.lineRadicalLevi_isPerfect hperfect
  exact M.leftLocal_eq_radicalLevi_of_character _ M.lineParabolicCharacter_ker

/-- The source residual is precisely the kernel of the actual cubic character. -/
theorem leftLocal_eq_ker_lineParabolicCharacter :
    M.leftLocal = M.lineParabolicCharacter.ker :=
  (M.leftLocal_eq_radicalLevi hperfect).trans M.lineParabolicCharacter_ker.symm

/-- The actual solvable residual has index three in the full line parabolic. -/
theorem leftLocal_index : M.leftLocal.index = 3 := by
  let : Group.IsPerfect M.LineRadicalLevi := M.lineRadicalLevi_isPerfect hperfect
  exact M.leftLocal_index_of_character _ M.lineParabolicCharacter_ker
    M.lineParabolicCharacter_surjective M.lineCubic_card

/-- The residual itself, with its actual multiplication, is the radical–SU₃ semidirect product. -/
noncomputable def leftLocalEquivRadicalLevi : M.leftLocal ≃* M.LineRadicalLevi :=
  (MulEquiv.subgroupCongr (M.leftLocal_eq_radicalLevi hperfect)).trans
    M.lineRadicalLeviEquiv.symm

/-- Restriction of the named full projection to the original solvable residual. -/
noncomputable def leftLocalLevi : M.leftLocal →* M.LocalUnitaryGroup :=
  M.lineParabolicProjection.comp M.leftLocal.subtype

/-- The residual restriction remains onto the actual SU₃ group. -/
theorem leftLocalLevi_surjective : Function.Surjective M.leftLocalLevi := by
  let : Group.IsPerfect M.LineRadicalLevi := M.lineRadicalLevi_isPerfect hperfect
  exact M.leftLocalLevi_surjective_of_character _ M.lineParabolicCharacter_ker
    _ M.lineParabolicProjection_comp_radicalLeviMap

/-- The residual Levi kernel is the full coordinate group, with no character or action premise. -/
noncomputable def leftLocalLeviKernelEquiv : M.leftLocalLevi.ker ≃* M.LineRadicalCoordinates := by
  letI := M.lineRadicalLevi_isPerfect hperfect
  exact M.leftLocalLeviKernelEquiv_of_character _ M.lineParabolicCharacter_ker
    _ M.lineParabolicProjection_comp_radicalLeviMap

/-- The coordinate kernel is the literal unipotent subgroup inside the residual. -/
theorem leftLocalLevi_ker :
    M.leftLocalLevi.ker = M.lineUnipotent.subgroupOf M.leftLocal := by
  ext g
  have hc : M.lineParabolicCharacter g.val = 1 := by
    change g.val ∈ M.lineParabolicCharacter.ker
    rw [← M.leftLocal_eq_ker_lineParabolicCharacter hperfect]
    exact g.property
  change M.lineParabolicProjection g.val = 1 ↔ g.val ∈ M.lineUnipotent
  rw [M.lineUnipotent_eq_ker_parabolicMaps]
  change M.lineParabolicProjection g.val = 1 ↔
    (M.lineParabolicProjection g.val, M.lineParabolicCharacter g.val) = (1, 1)
  simp only [hc, Prod.mk.injEq, and_true]

end Residual
end CFSG.Quasithin.ChapterF.GreenBook.UnitaryFive.Model
