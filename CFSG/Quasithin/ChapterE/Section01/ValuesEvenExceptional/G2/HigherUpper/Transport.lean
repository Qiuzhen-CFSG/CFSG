module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.ParabolicCover
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.HigherUpper.SolvableKernel
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Nonbinary G₂ parabolic transport and solvable-kernel reduction

For q = 2^f with f > 1, perfectness identifies the derived octonion model
with the full model. Consequently the transported restricted parabolic is
actually isomorphic to the full short or long root parabolic. It is normal
in its join with T, and that join modulo the parabolic is a two-group.

Positive-rank E-generation lifts from the intrinsic solvable-radical quotient
of each literal parabolic overgroup. This module supplies the transport and
conditional lifting used by `HigherUpper.RadicalQuotient`; `HigherUpper` then
discharges the quotient-generation premise for every allowed outer two-extension.

Source: Aschbacher--Smith, E.1.12 and E.1.14(1), printed p.214, citing
Aschbacher (1982), Lemma 4.7. The imported concrete model retains the licensed
ATLAS attribution; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.G2.SylowParabolicRecognition
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Finite G] in
/-- The actual nonbinary model makes the source socle perfect. -/
theorem higher_socle_isPerfect {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (L : Subgroup G)
    (e : L ≃* commutator (Model F)) : Group.IsPerfect L := by
  let : Group.IsPerfect (Model F) := Atlas.G2.isPerfect (by
    rw [hF]
    exact (by simpa using (Nat.pow_lt_pow_right (by decide : 1 < 2) hf)))
  let a := e.trans (DerivedEvenOrder.derivedEquivModel hf hF)
  exact Group.IsPerfect.ofSurjective (f := a.symm.toMonoidHom) a.symm.surjective

omit [Finite G] in
/-- This supplies nonabelianness for the existing simple-socle structural
producer; in the source, simplicity supplies the nontriviality instance. -/
theorem higher_socle_not_isMulCommutative {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (L : Subgroup G) [Nontrivial L]
    (e : L ≃* commutator (Model F)) : ¬ IsMulCommutative L := by
  let := higher_socle_isPerfect hf hF L e
  exact Group.IsPerfect.not_isMulCommutative L

/-- Above F₂ the restricted parabolic is the actual full root parabolic. -/
noncomputable def higherRootParabolicEquiv {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (i : Fin 2) :
    rootParabolic (F := F) i ≃*
      (if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F)) :=
  subgroupOfEquivOfLe (by
    rw [DerivedEvenOrder.commutator_eq_top_of_card hf hF]
    exact le_top)

/-- The ambient image is isomorphic to the full model parabolic, not just
an abstract group with a matching family name or order. -/
noncomputable def higherAmbientParabolicEquiv {f : ℕ} (hf : 1 < f)
    (hF : Nat.card F = 2 ^ f) (L : Subgroup G)
    (e : L ≃* commutator (Model F)) (i : Fin 2) :
    ambientParabolic L e i ≃*
      (if i = 0 then parabolic₁ (F := F) else parabolic₂ : Subgroup (Model F)) :=
  ((rootParabolic i).equivMapOfInjective (derivedEmbedding L e)
    (L.subtype_injective.comp e.symm.injective)).symm.trans
      (higherRootParabolicEquiv hf hF i)

variable [CharP F 2]

/-- Normality is relative to the actual T-overgroup. -/
theorem ambientParabolic_normal_in_overgroup (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    ((ambientParabolic L e i).subgroupOf (parabolicOvergroup L T e i)).Normal :=
  normal_subgroupOf_of_le_normalizer
    (sup_le (ambientParabolic L e i).le_normalizer
      (sylow_normalizes_ambientParabolic L T e he i))

/-- Every outer extension retained in the local problem has two-group
quotient by the transported full parabolic. -/
theorem parabolicOvergroup_quotient_isTwoGroup (L : Subgroup G) [L.Normal]
    (T : Sylow 2 G) (e : L ≃* commutator (Model F))
    (he : ((T : Subgroup G).subgroupOf L).map e.toMonoidHom =
      unipotent.subgroupOf (commutator (Model F))) (i : Fin 2) :
    let _ := ambientParabolic_normal_in_overgroup L T e he i
    IsPGroup 2 ((parabolicOvergroup L T e i) ⧸
      (ambientParabolic L e i).subgroupOf (parabolicOvergroup L T e i)) := by
  let _ := ambientParabolic_normal_in_overgroup L T e he i
  apply isPGroup_quotient_of_sup_eq_top _
    ((T : Subgroup G).subgroupOf (parabolicOvergroup L T e i))
    T.isPGroup'.comap_subtype
  rw [← subgroupOf_sup (show ambientParabolic L e i ≤ parabolicOvergroup L T e i
      from le_sup_left) (le_parabolicOvergroup L T e i)]
  exact subgroupOf_self _

omit [CharP F 2] [Finite F] in
/-- The literal radical quotient is the only remaining generation input.
Its rank-one model and outer action must still be proved in the application. -/
theorem higher_parabolicOvergroup_isEGenerated_of_radical_quotient
    {f : ℕ} (hf : 1 < f) (L : Subgroup G) (T : Sylow 2 G)
    (e : L ≃* commutator (Model F)) (i : Fin 2)
    (hquot : IsEGenerated f ((parabolicOvergroup L T e i) ⧸
      solvableRadical (parabolicOvergroup L T e i))) :
    IsEGenerated f (parabolicOvergroup L T e i) :=
  IsEGenerated.of_solvableRadical_quotient (by omega) hquot

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2
