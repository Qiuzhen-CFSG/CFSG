module

public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics
public import Theory.SpecificGroups.ReeTwo.ParabolicMarkedComparison

/-!
# Actual marked Ree and Tits comparisons for Lemma 14.2.21

The coordinate local group is identified with the actual first full-Ree
parabolic, preserving its positive Sylow subgroup, whole overlap, core and
source central involution. The actual Tits intersection is the mixed-character
kernel. Its restricted comparison has the same markings in the Atlas carrier.
In particular the Tits core is the order-512 character-kernel core; the
parity kernel with its dihedral quotient is not assigned to the Tits model.

These unconditional comparisons connect the intrinsic calculations exported
by `ReeLocal.Parabolics` to the actual exceptional models. They do not assert
the full ambient conclusion H = Mc of 14.2.21, whose remaining argument
belongs to the source assembly owner.

Sources: Aschbacher–Smith, Lemma 14.2.21, printed p.989; Aschbacher (1982),
Section 3; Parrott (1972), pp.672,683; Shinoda (1975), pp.81–83.
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics
open ReeTwo ReeTwo.ParabolicMarkedComparison
open Tits.ExceptionalParabolics

/-- The full root-coordinate group, in the specified ambient parabolic. -/
public noncomputable def ree_first_model : Centralizer ≃* FullRee.first := Verified.firstEquiv

/-- The actual Tits local group is the mixed character kernel. -/
public noncomputable def tits_first_model :
    Centralizer.IndexTwo.mixedLocal ≃* Tits.ExceptionalParabolics.first := Verified.titsFirstEquiv

public theorem ree_sylow_and_overlap :
    Verified.sylowMap.range = FullRee.S ∧
      Verified.sylowMap.range = FullRee.first ⊓ FullRee.second :=
  ⟨Verified.sylowMap_range, Verified.sylowMap_range_overlap⟩

public theorem tits_preimage :
    (commutator (ReeF4.Model 0)).comap Verified.localMap = Centralizer.IndexTwo.mixedLocal :=
  Verified.derived_preimage

/-- Both inclusions are the literal restrictions of the same ambient map. -/
public theorem tits_sylow_compatible (g : titsSylow) :
    Subgroup.inclusion Tits.ExceptionalParabolics.sylow_le_first (Verified.titsSylowEquiv g) =
      tits_first_model (titsSylowInclusion g) := Verified.titsSylow_first_commutes g

public theorem ree_core_compatible :
    Centralizer.core.map ree_first_model.toMonoidHom = pCore 2 FullRee.first :=
  Verified.firstEquiv_core

public theorem tits_core_compatible :
    (Centralizer.core.subgroupOf Centralizer.IndexTwo.mixedLocal).map
      tits_first_model.toMonoidHom = pCore 2 Tits.ExceptionalParabolics.first :=
  Verified.titsFirstEquiv_core

/-- Source Z = Ω₁(Z(T)) uses the actual positive Sylow and source root 12. -/
public theorem ree_source_Z :
    ((omega₁ (Subgroup.center FullRee.S) (p := 2)).map
      (Subgroup.center FullRee.S).subtype).map FullRee.S.subtype =
        Subgroup.zpowers (Ambient.root 9) := by
  rw [Subgroup.map_map]
  exact Verified.sylow_omega_center

/-- The Tits source Z has the same distinguished Atlas involution. -/
public theorem tits_source_Z :
    ((omega₁ (Subgroup.center Tits.ExceptionalParabolics.S) (p := 2)).map
      (Subgroup.center Tits.ExceptionalParabolics.S).subtype).map
      Tits.ExceptionalParabolics.S.subtype = Subgroup.zpowers Tits.atlas1600R5 := by
  rw [Subgroup.map_map]
  exact Verified.tits_sylow_omega_center

public theorem source_last_root_compatible :
    FullRee.atlasEmbedding Tits.atlas1600R5 = Ambient.root 9 ∧
      (tits_first_model mixedLastRoot : Tits.Atlas1600Group) = Tits.atlas1600R5 :=
  ⟨Verified.atlas_last_root, Verified.titsFirstEquiv_last_root⟩

/-- Both source locals use the same actual ambient Suzuki projection after restriction. -/
public theorem tits_quotient_projection_compatible
    (g : Centralizer.IndexTwo.mixedLocal) :
    FirstQuotient.projection (tits_first_model g) =
      FullRee.firstProjection (ree_first_model g) :=
  Verified.tits_projection_commutes g

/-- The full local quotient is identified through its actual core projection. -/
public noncomputable def ree_quotient_model : (Centralizer ⧸ Centralizer.core) ≃*
    BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 := Verified.firstSuzukiEquiv

/-- The Tits quotient uses the order-512 core and the same Suzuki matrix carrier. -/
public noncomputable def tits_quotient_model :
    (Centralizer.IndexTwo.mixedLocal ⧸
      Centralizer.core.subgroupOf Centralizer.IndexTwo.mixedLocal) ≃*
        BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0 := Verified.titsFirstSuzukiEquiv

public theorem ree_quotient_model_mk (g : Centralizer) :
    ree_quotient_model (QuotientGroup.mk' Centralizer.core g) =
      FullRee.firstProjection (ree_first_model g) := Verified.firstSuzukiEquiv_mk g

public theorem tits_quotient_model_mk (g : Centralizer.IndexTwo.mixedLocal) :
    tits_quotient_model
      (QuotientGroup.mk' (Centralizer.core.subgroupOf Centralizer.IndexTwo.mixedLocal) g) =
        FullRee.firstProjection (ree_first_model g) := Verified.titsFirstSuzukiEquiv_mk g

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.Parabolics
