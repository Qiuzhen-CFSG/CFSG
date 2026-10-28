module

public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.RootVerification
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison.Center
public import Theory.SpecificGroups.Tits.ExceptionalParabolics.FirstQuotient

/-!
# Verified marked comparisons for the binary Ree and Tits first parabolics

The actual fixed roots satisfy all the coordinate relations. The resulting
root-and-Weyl homomorphism is faithful because its last root is Parrott's
nonidentity r5. Its image is the specified first parabolic, and its Sylow
restriction has image the specified positive subgroup and whole overlap.

The preimage of the ambient derived group is exactly the mixed character
kernel. Restriction yields the marked Atlas Tits first-parabolic isomorphism,
compatible with Sylow inclusions, both intrinsic cores and the distinguished
involution. The last root generates the literal source Ω₁(Z(T)) in both
models. The quotient comparisons commute with the ambient owner's literal
Suzuki projections. None of the exports in `Verified` has an additional relation premise.

Sources: Shinoda (1975), pp.81–83; Parrott (1972), pp.672,683;
Aschbacher (1982), Section 3; Aschbacher–Smith 14.2.21, printed p.989.
-/

@[expose] public section
noncomputable section
namespace ReeTwo.ParabolicMarkedComparison.Verified
open ReeF4 Tits.ExceptionalParabolics
open Centralizer.IndexTwo

abbrev localMap := ParabolicMarkedComparison.localMap RootVerification.relations
abbrev firstEquiv := ParabolicMarkedComparison.firstEquiv RootVerification.relations
abbrev sylowMap := ParabolicMarkedComparison.sylowMap RootVerification.relations
abbrev sylowEquiv := ParabolicMarkedComparison.sylowEquiv RootVerification.relations
abbrev titsFirstEquiv := ParabolicMarkedComparison.titsFirstEquiv RootVerification.relations
abbrev titsSylowEquiv := ParabolicMarkedComparison.titsSylowEquiv RootVerification.relations

@[simp] theorem localMap_root (i : CoreRoot) : localMap (Centralizer.root i) = Ambient.root i :=
  ParabolicMarkedComparison.localMap_root _ i

@[simp] theorem localMap_rootOne : localMap Centralizer.rootOne = Ambient.rootOne :=
  ParabolicMarkedComparison.localMap_rootOne _

@[simp] theorem localMap_weyl : localMap Centralizer.weyl = Ambient.weyl :=
  ParabolicMarkedComparison.localMap_weyl _

/-- The chosen order-five complement element keeps its specified Weyl/root word. -/
theorem localMap_fiveGenerator : localMap Centralizer.fiveGenerator =
    (Ambient.rootOne⁻¹) ^ 2 * Ambient.weyl := by
  have he : Centralizer.fiveGenerator =
      (Centralizer.rootOne⁻¹) ^ 2 * Centralizer.weyl := by
    simp [Centralizer.fiveGenerator, Centralizer.rootOne, Centralizer.weyl]
  rw [he, map_mul, map_pow, map_inv, localMap_rootOne, localMap_weyl]

theorem localMap_injective : Function.Injective localMap :=
  ParabolicMarkedComparison.localMap_injective _

theorem localMap_range : localMap.range = FullRee.first :=
  ParabolicMarkedComparison.localMap_range _

theorem sylowMap_range : sylowMap.range = FullRee.S :=
  ParabolicMarkedComparison.sylowMap_range _

theorem sylowMap_range_overlap : sylowMap.range = FullRee.first ⊓ FullRee.second :=
  ParabolicMarkedComparison.sylowMap_range_overlap _

@[simp] theorem firstEquiv_coe (g : Centralizer) :
    (firstEquiv g : Model 0) = localMap g := rfl

@[simp] theorem sylowEquiv_coe (g : SylowModel) :
    (sylowEquiv g : Model 0) = localMap (SylowModel.embedding g) := rfl

theorem sylow_first_commutes (g : SylowModel) :
    Subgroup.inclusion FullRee.sylow_le_first (sylowEquiv g) =
      firstEquiv (SylowModel.embedding g) := rfl

/-- This is the preimage under the actual ambient map, not an intrinsic guess. -/
theorem derived_preimage : (commutator (Model 0)).comap localMap = mixedLocal :=
  ParabolicMarkedComparison.derived_preimage _

theorem mixed_image : mixedLocal.map localMap =
    Tits.ExceptionalParabolics.first.map FullRee.atlasEmbedding :=
  ParabolicMarkedComparison.mixed_image _

theorem titsFirstEquiv_coe (g : mixedLocal) :
    FullRee.atlasEmbedding (titsFirstEquiv g : Tits.Atlas1600Group) = localMap g :=
  ParabolicMarkedComparison.titsFirstEquiv_coe _ g

theorem titsSylowEquiv_coe (g : titsSylow) :
    FullRee.atlasEmbedding (titsSylowEquiv g : Tits.Atlas1600Group) = sylowMap g :=
  ParabolicMarkedComparison.titsSylowEquiv_coe _ g

theorem titsSylow_first_commutes (g : titsSylow) :
    Subgroup.inclusion Tits.ExceptionalParabolics.sylow_le_first (titsSylowEquiv g) =
      titsFirstEquiv (titsSylowInclusion g) :=
  ParabolicMarkedComparison.titsSylow_first_commutes _ g

theorem titsSylow_image_overlap : titsSylow.map sylowMap =
    Tits.ExceptionalParabolics.overlap.map FullRee.atlasEmbedding :=
  ParabolicMarkedComparison.titsSylow_image_overlap _

theorem firstEquiv_core : Centralizer.core.map firstEquiv.toMonoidHom =
    pCore 2 FullRee.first := ParabolicMarkedComparison.firstEquiv_core _

theorem titsFirstEquiv_core :
    (Centralizer.core.subgroupOf mixedLocal).map titsFirstEquiv.toMonoidHom =
      pCore 2 Tits.ExceptionalParabolics.first := ParabolicMarkedComparison.titsFirstEquiv_core _

theorem atlas_last_root : FullRee.atlasEmbedding Tits.atlas1600R5 = Ambient.root 9 :=
  ParabolicMarkedComparison.atlas_last_root RootVerification.relations

theorem titsFirstEquiv_last_root :
    (titsFirstEquiv mixedLastRoot : Tits.Atlas1600Group) = Tits.atlas1600R5 :=
  ParabolicMarkedComparison.titsFirstEquiv_last_root _

theorem sylow_omega_center :
    (omega₁ (Subgroup.center FullRee.S) (p := 2)).map
      (FullRee.S.subtype.comp (Subgroup.center FullRee.S).subtype) =
        Subgroup.zpowers (Ambient.root 9) :=
  ParabolicMarkedComparison.sylow_omega_center RootVerification.relations

theorem tits_sylow_omega_center :
    (omega₁ (Subgroup.center Tits.ExceptionalParabolics.S) (p := 2)).map
      (Tits.ExceptionalParabolics.S.subtype.comp
        (Subgroup.center Tits.ExceptionalParabolics.S).subtype) =
        Subgroup.zpowers Tits.atlas1600R5 :=
  ParabolicMarkedComparison.tits_sylow_omega_center RootVerification.relations

/-- The quotient comparison retains the literal projection from the ten-root core. -/
def firstQuotientEquiv : (Centralizer ⧸ Centralizer.core) ≃*
    (FullRee.first ⧸ pCore 2 FullRee.first) :=
  QuotientGroup.congr _ _ firstEquiv firstEquiv_core

@[simp] theorem firstQuotientEquiv_mk (x : Centralizer) :
    firstQuotientEquiv (QuotientGroup.mk' Centralizer.core x) =
      QuotientGroup.mk' (pCore 2 FullRee.first) (firstEquiv x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

/-- The restricted quotient comparison uses the actual mixed-kernel core. -/
def titsFirstQuotientEquiv :
    (mixedLocal ⧸ Centralizer.core.subgroupOf mixedLocal) ≃*
      (Tits.ExceptionalParabolics.first ⧸ pCore 2 Tits.ExceptionalParabolics.first) :=
  QuotientGroup.congr _ _ titsFirstEquiv titsFirstEquiv_core

@[simp] theorem titsFirstQuotientEquiv_mk (x : mixedLocal) :
    titsFirstQuotientEquiv (QuotientGroup.mk' (Centralizer.core.subgroupOf mixedLocal) x) =
      QuotientGroup.mk' (pCore 2 Tits.ExceptionalParabolics.first) (titsFirstEquiv x) :=
  QuotientGroup.congr_mk' _ _ _ _ x

/-- The Tits restriction commutes with the ambient owner's literal parabolic embedding. -/
theorem tits_embedding_commutes (g : mixedLocal) :
    FirstQuotient.embedding (titsFirstEquiv g) = firstEquiv g := by
  apply Subtype.ext
  exact titsFirstEquiv_coe g

/-- The same compatibility holds for the actual Suzuki matrix quotient projection. -/
theorem tits_projection_commutes (g : mixedLocal) :
    FirstQuotient.projection (titsFirstEquiv g) =
      FullRee.firstProjection (firstEquiv g) := by
  exact congrArg FullRee.firstProjection (tits_embedding_commutes g)

/-- The full coordinate core quotient maps to the actual Suzuki matrix group. -/
def firstSuzukiEquiv : (Centralizer ⧸ Centralizer.core) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  firstQuotientEquiv.trans FullRee.firstCoreQuotientEquiv

@[simp] theorem firstSuzukiEquiv_mk (g : Centralizer) :
    firstSuzukiEquiv (QuotientGroup.mk' Centralizer.core g) =
      FullRee.firstProjection (firstEquiv g) := by
  simp only [firstSuzukiEquiv, MulEquiv.trans_apply, firstQuotientEquiv_mk,
    FullRee.firstCoreQuotientEquiv_mk]

/-- The actual Tits core quotient uses the restricted ambient Suzuki projection. -/
def titsFirstSuzukiEquiv :
    (mixedLocal ⧸ Centralizer.core.subgroupOf mixedLocal) ≃*
      BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 :=
  titsFirstQuotientEquiv.trans FirstQuotient.coreQuotientEquiv

@[simp] theorem titsFirstSuzukiEquiv_mk (g : mixedLocal) :
    titsFirstSuzukiEquiv (QuotientGroup.mk' (Centralizer.core.subgroupOf mixedLocal) g) =
      FullRee.firstProjection (firstEquiv g) := by
  simp only [titsFirstSuzukiEquiv, MulEquiv.trans_apply, titsFirstQuotientEquiv_mk,
    FirstQuotient.coreQuotientEquiv_mk, tits_embedding_commutes]

end ReeTwo.ParabolicMarkedComparison.Verified
