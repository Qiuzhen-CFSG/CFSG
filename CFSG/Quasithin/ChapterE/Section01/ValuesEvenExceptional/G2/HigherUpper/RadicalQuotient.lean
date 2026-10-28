module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.Transport
public import Theory.AtlasPort.LinearGroups.G2.HigherParabolicRadical.Short
public import Theory.AtlasPort.LinearGroups.G2.HigherParabolicRadical.Long
public import Theory.GroupTheory.GeneralizedFitting.RadicalTwoExtension
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support
public import Theory.Comparator.Defs
public import GorensteinWalter.PSL2PerfectOfCard

/-!
# Radical quotients of the nonbinary G₂ parabolic overgroups

A normal subgroup with nonabelian simple radical quotient and two-group
ambient quotient has the same simple group as the generalized Fitting
subgroup of the ambient radical quotient. Applying this to the transported
full root parabolic includes arbitrary outer two-extensions, without any
splitting assumption. Coefficient transport identifies the resulting PSL₂
with the matrix model over the exact field `GaloisField 2 f`.

The full short and long parabolics have determinant-normalized matrix actions
with exact solvable-radical kernels. These calculations include the scalar
torus contribution and discharge both model premises in the structural
reduction. The final structure theorem uses only normality of L and the given
Sylow alignment, so it applies in particular to L = F*(G) in E.1.14.
The E-generation argument remains with the caller.

Source: Aschbacher--Smith, E.1.14(1), printed p.214 (citing Aschbacher 1982,
Lemma 4.7), and the rank-one local structure in F.1.12, pp.262--264.
The imported octonion model and coefficient transport retain the ATLAS
attribution and license in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.RadicalQuotient
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Field F] [Finite F] in
private theorem four_le_card {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f) :
    4 ≤ Nat.card F := by
  rw [hF]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)

/-- The coefficient isomorphism preserves the exponent in the comparator's
actual PSL₂ matrix model. -/
private noncomputable def coefficientModelEquiv {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) : PSL(2,F) ≃* PSL2Model f := by
  let := Fintype.ofFinite F
  let := Fintype.ofFinite (GaloisField 2 f)
  let a : F ≃+* GaloisField 2 f := FiniteField.ringEquivOfCardEq (by
    simp only [← Nat.card_eq_fintype_card]
    rw [hF, GaloisField.card 2 f (by omega)])
  exact Atlas.fieldEquivPSL 2 a

/-- Transport the radical quotient of the full model parabolic to the
literal normal subgroup of the T-overgroup. -/
noncomputable def fullParabolicRadicalEquiv {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (L : Subgroup G)
    (e : L ≃* commutator (Model F)) (T : Sylow 2 G) (i : Fin 2)
    (a : ((if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F)) ⧸
      solvableRadical (if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F)))
      ≃* PSL(2,F)) :
    ((ambientParabolic L e i).subgroupOf (parabolicOvergroup L T e i)) ⧸
      solvableRadical ((ambientParabolic L e i).subgroupOf (parabolicOvergroup L T e i))
      ≃* PSL(2,F) := by
  let b := (subgroupOfEquivOfLe (show ambientParabolic L e i ≤ parabolicOvergroup L T e i
    from le_sup_left)).trans (higherAmbientParabolicEquiv hf hF L e i)
  exact (QuotientGroup.congr _ _ b (map_solvableRadical_equiv b)).trans a

/-- All required rank-one structure of the actual radical quotient follows
from the full-parabolic radical calculation. The latter remains an explicit
model premise, to be discharged separately for both root parabolics. -/
theorem structure_of_fullParabolic {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2)
    (a : ((if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F)) ⧸
      solvableRadical (if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F)))
      ≃* PSL(2,F)) :
    let Q := (parabolicOvergroup L T e i) ⧸ solvableRadical (parabolicOvergroup L T e i)
    IsSimpleGroup (generalizedFitting Q) ∧
      Nonempty (generalizedFitting Q ≃* PSL2Model f) ∧
      ∀ S : Sylow 2 Q, generalizedFitting Q ⊔ (S : Subgroup Q) = ⊤ := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let P := parabolicOvergroup L T e i
  let N := (ambientParabolic L e i).subgroupOf P
  let : N.Normal := ambientParabolic_normal_in_overgroup L T e he i
  let b := fullParabolicRadicalEquiv hf hF L e T i a
  let : IsSimpleGroup PSL(2,F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (four_le_card hf hF)
  let : IsSimpleGroup (N ⧸ solvableRadical N) := b.isSimpleGroup
  let : Group.IsPerfect PSL(2,F) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three F (by have := four_le_card hf hF; omega)
  let : Group.IsPerfect (N ⧸ solvableRadical N) :=
    Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have ha : ¬ IsMulCommutative (N ⧸ solvableRadical N) :=
    Group.IsPerfect.not_isMulCommutative _
  have hquot : IsPGroup 2 (P ⧸ N) :=
    parabolicOvergroup_quotient_isTwoGroup L T e he i
  refine ⟨radicalTwoExtension_fitting_simple N ha hquot, ⟨?_, ?_⟩⟩
  · exact ⟨((radicalTwoExtensionFittingEquiv N ha hquot).trans b).trans
      (coefficientModelEquiv hf hF)⟩
  · exact radicalTwoExtension_fitting_sup_sylow N ha hquot

/-- Both full model parabolics have the required radical quotient, including
their scalar torus. Characteristic two follows from the field cardinality. -/
@[no_expose] noncomputable def modelParabolicRadicalEquiv {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (i : Fin 2) :
    ((if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F)) ⧸
      solvableRadical (if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F)))
      ≃* PSL(2,F) := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := f)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := lt_of_lt_of_le (by decide : 2 < 4) (four_le_card hf hF)
  apply Classical.choice
  fin_cases i
  · exact ⟨HigherParabolicRadical.Short.parabolic₁RadicalQuotientEquivPSL hq⟩
  · exact ⟨HigherParabolicRadical.Long.parabolic₂RadicalQuotientEquivPSL hq⟩

/-- The literal radical quotient of either nonbinary G₂ parabolic overgroup
has simple generalized Fitting subgroup PSL₂(2^f), which supplements every
Sylow two-subgroup. This covers every ambient outer two-extension. -/
theorem parabolicOvergroup_structure {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    let Q := (parabolicOvergroup L T e i) ⧸ solvableRadical (parabolicOvergroup L T e i)
    IsSimpleGroup (generalizedFitting Q) ∧
      Nonempty (generalizedFitting Q ≃* PSL2Model f) ∧
      ∀ S : Sylow 2 Q, generalizedFitting Q ⊔ (S : Subgroup Q) = ⊤ :=
  structure_of_fullParabolic hf hF L T e he i (modelParabolicRadicalEquiv hf hF i)

/-- An actual equivalence to the comparator's projective matrix group over
`GaloisField 2 f`, for the generalized Fitting subgroup of the literal quotient. -/
noncomputable def parabolicOvergroupFittingEquiv {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    generalizedFitting ((parabolicOvergroup L T e i) ⧸
      solvableRadical (parabolicOvergroup L T e i)) ≃* PSL2Model f :=
  Classical.choice (parabolicOvergroup_structure hf hF L T e he i).2.1

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.RadicalQuotient
