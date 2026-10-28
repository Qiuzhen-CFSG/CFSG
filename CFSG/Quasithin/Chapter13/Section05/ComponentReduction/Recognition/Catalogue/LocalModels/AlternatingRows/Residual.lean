module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Configuration.Prefix
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.GeneralizedFitting.SimpleSocleStructure

/-!
# Residual inputs for the alternating rows of 13.5.21

The image of L₁ in the literal X/C_X(K*) is two-perfect, since the source
L₁ is the embedded O²(L ∩ Gz). The nontrivial image of Y makes this local
image nontrivial. Condition (ii), with its actual O₂,₃ preimage, places it
in the marked involution centralizer. The simple generalized Fitting
subgroup is self-centralizing, so its conjugation action is faithful.

These facts are applied in `AlternatingRows.Six`; the other alternating
rows can use exactly the same original quotient and residual subgroup.
Source: Aschbacher–Smith, combined manuscript of 1 March 2004, 13.5.21,
printed pp.923–924 (PDF pp.940–941), conditions (i),(ii).
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels
open Configuration
variable {G : Type*} [Group G] [Finite G]
  {D : ChapterF.Section09.Setup G} {K : Subgroup G}
  (s : Selected D K) (h : D.Hypothesis) [(componentCentralizer s h).Normal]

/-- The actual local image is two-perfect because L₁ is the embedded O² of
L ∩ Gz. No residual condition on an unrelated abstract subgroup is used. -/
theorem source_L1hat_twoPerfect : IsPPerfect 2 (L1hat s h) := by
  have hp : IsPPerfect 2 D.L₁ := isPPerfect_embedded_pResidual 2 (D.L ⊓ D.Gz)
  have hLX : D.L₁ ≤ X D K := le_sup_left.trans le_sup_right
  let f := (subgroupOfEquivOfLe hLX).symm
  have hLP : IsPPerfect 2 (D.L₁.subgroupOf (X D K)) :=
    hp.of_surjective f.toMonoidHom f.surjective
  let q := QuotientGroup.mk' (componentCentralizer s h)
  exact hLP.of_surjective (q.subgroupMap (D.L₁.subgroupOf (X D K)))
    (q.subgroupMap_surjective _)

/-- Condition (ii) places the nontrivial, two-perfect image of the original
L₁ in the original involution centralizer. The O₂,₃ preimage is used literally. -/
theorem source_condition_ii_residual (Y : Subgroup G) (p : Prefix s h Y)
    (hc : LocalCoreCondition s h) :
    L1hat s h ≠ ⊥ ∧ IsPPerfect 2 (L1hat s h) ∧
      L1hat s h ≤ centralizer (Vhat s h : Set (Xhat s h)) := by
  refine ⟨fun he => p.Y_ne_bot (bot_unique (p.Y_le_local.trans_eq he)),
    source_L1hat_twoPerfect s h, ?_⟩
  exact hc.trans (map_subtype_le _)

/-- The literal simple generalized Fitting subgroup acts faithfully on itself. -/
theorem source_centralizer_eq_bot (Y : Subgroup G) (p : Prefix s h Y) :
    centralizer (Khat s h : Set (Xhat s h)) = ⊥ := by
  let : IsSimpleGroup (Khat s h) := p.khat_simple
  let : Group.IsPerfect (Khat s h) := Khat_perfect s h
  let e := MulEquiv.subgroupCongr p.khat_fitting
  let : IsSimpleGroup (generalizedFitting (Xhat s h)) := e.isSimpleGroup
  let : Group.IsPerfect (generalizedFitting (Xhat s h)) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  rw [← p.khat_fitting]
  exact SimpleSocle.centralizer_eq_bot (Group.IsPerfect.not_isMulCommutative _)

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Recognition.Catalogue.LocalModels
