module

public import CFSG.Quasithin.Chapter8.Section02.Centralizer.Definitions
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# The point residual in the full involution-centralizer quotient

The image of L_z = C_L(z)^∞ is formed in C_G(z)/O₂(C_G(z)), using the
literal inclusions. Its projection is onto and has kernel L_z ∩ O₂(C_G(z)),
with the two-core embedded back into G. In particular the kernel is a
two-group. These constructions retain the full quotient kernel for the
marked Mathieu calculation.

Source: Aschbacher–Smith, Proposition 8.2.13, printed pp.722–723.
The chosen-module application is in NonFFSourceMathieuM24FullQuotient.
-/

public noncomputable section

namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
open Subgroup Chapter8.Section02.Centralizer

/-- The literal image of the point residual in the full centralizer quotient. -/
@[expose] def pointResidualImage {G : Type*} [Group G] (L : Subgroup G) (z : G) :
    Subgroup ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))) :=
  ((localResidual L z).subgroupOf (centralizer ({z} : Set G))).map
    (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))))

/-- The restriction of the full centralizer quotient map to the point residual. -/
@[expose] def pointResidualProjection {G : Type*} [Group G] (L : Subgroup G) (z : G) :
    localResidual L z →* pointResidualImage L z :=
  ((QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))).subgroupMap
    ((localResidual L z).subgroupOf (centralizer ({z} : Set G)))).comp
      (subgroupOfEquivOfLe ((localResidual_le L z).trans inf_le_right)).symm.toMonoidHom

theorem pointResidualProjection_surjective {G : Type*} [Group G] (L : Subgroup G) (z : G) :
    Function.Surjective (pointResidualProjection L z) :=
  (MonoidHom.subgroupMap_surjective _ _).comp (subgroupOfEquivOfLe _).symm.surjective

theorem pointResidualProjection_kernel {G : Type*} [Group G] (L : Subgroup G) (z : G) :
    (pointResidualProjection L z).ker =
      ((centralizer ({z} : Set G)).pCoreIn 2).subgroupOf (localResidual L z) := by
  let C := centralizer ({z} : Set G)
  have hRC : localResidual L z ≤ C := (localResidual_le L z).trans inf_le_right
  ext r
  change pointResidualProjection L z r=1 ↔ (r : G) ∈ (pCore 2 C).map C.subtype
  rw [Subtype.ext_iff]
  change (QuotientGroup.mk' (pCore 2 C)) (inclusion hRC r)=1 ↔ _
  change ((inclusion hRC r : C) : C ⧸ pCore 2 C)=1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  constructor
  · exact mem_map_of_mem C.subtype
  · rintro ⟨c,hc,he⟩
    exact (show c = inclusion hRC r from Subtype.ext he) ▸ hc

theorem pointResidualProjection_kernel_isTwoGroup {G : Type*} [Group G]
    (L : Subgroup G) (z : G) : IsPGroup 2 (pointResidualProjection L z).ker := by
  rw [pointResidualProjection_kernel]
  exact (isPGroup_pCoreIn 2 _).comap_subtype

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuSextet
