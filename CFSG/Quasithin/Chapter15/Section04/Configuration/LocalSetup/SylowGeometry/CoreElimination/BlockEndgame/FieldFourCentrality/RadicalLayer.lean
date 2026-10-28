module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockEndgame.FieldFourCentrality.Setup

/-!
# The conjugate seed in the elementary radical layer

The residual description makes K normal inside H. Since H = KU and U is
the supplied Sylow two-subgroup, characteristic two passes from K to H.
The source equality C_G(Z) = T restricts to C_H(Z) = U. Self-centralization
of O₂(H) then puts the normal closure of Z in Ω₁(Z(O₂(H))). In particular,
the actual embedded seed closure is elementary abelian.

Inside H, the first block is subnormal and two-perfect. The normal
two-subgroup given by the seed closure therefore has its commutator with
the block in the intrinsic layer [O₂(L), L]. The equivalence between L
inside H and L inside G transports this containment to `firstLayer`.
These conclusions do not require a restriction on the field parameter.

The generalized-Fitting extension uses the comparison in
`ChapterB.QuasisimpleSections.Group`: both sides use nilpotent normal
subgroups and relatively subnormal quasisimple components.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.11–13, printed pp.123–125; the characteristic-two paragraph in the
proof of 15.4.20, printed p.1164, invoking B.2.14.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
open Subgroup ChapterC Theory.GroupTheory Stellmacher
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {d : Source.Geometry G} {i j : Bool}
variable (c : ContraryData κ d i j)

/-- Characteristic two passes from the actual normal residual K to H = KU. -/
theorem overgroup_characteristic_two : generalizedFitting c.H = pCore 2 c.H := by
  have hKH : c.K ≤ c.H := c.product ▸ le_sup_left
  have hN : c.K.subgroupOf c.H = primeToResidual 3 c.H := by
    apply map_injective c.H.subtype_injective
    rw [map_subgroupOf_eq_of_le hKH, c.residual]
  let _ : (c.K.subgroupOf c.H).Normal := hN.symm ▸ inferInstance
  have hgen : c.K.subgroupOf c.H ⊔ (c.sylow : Subgroup c.H) = ⊤ := by
    apply map_injective c.H.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKH, c.sylow_image, c.product,
      ← MonoidHom.range_eq_map, range_subtype]
  exact generalizedFitting_eq_twoCore _ c.sylow hgen
    (generalizedFitting_eq_twoCore_of_equiv (subgroupOfEquivOfLe hKH) c.characteristic_two)

private theorem seed_centralizer :
    centralizer (d.Z.subgroupOf c.H : Set c.H) = (c.sylow : Subgroup c.H) :=
  TwoFactors.FFBranch.centralizer_seed_subgroupOf c.H (d.T : Subgroup G) d.Z c.sylow
    d.T.isPGroup' (c.sylow_image ▸ c.upper_lt.le) (Z_le_H c) c.centralizer_Z

private theorem intrinsic_seedClosure_elementary :
    IsElementaryAbelian 2 (normalClosure (d.Z.subgroupOf c.H : Set c.H)) := by
  let _ : IsElementaryAbelian 2 d.Z :=
    c.omega_center ▸ omegaOneCenterAmbient_elementaryAbelian _
  let _ : IsElementaryAbelian 2 (d.Z.subgroupOf c.H) :=
    IsElementaryAbelian.subgroupOf (Z_le_H c)
  exact TwoFactors.FFBranch.moduleClosure_elementary c.sylow (d.Z.subgroupOf c.H)
    (seed_centralizer c) (overgroup_characteristic_two c)

/-- The H-conjugate closure of the source omega-center is elementary abelian. -/
theorem seedClosure_elementary : IsElementaryAbelian 2 (seedClosure c) := by
  let _ := intrinsic_seedClosure_elementary c
  exact IsElementaryAbelian.map c.H.subtype

/-- The seed and all its H-conjugates lie in the embedded Ω₁(Z(O₂(H))). -/
theorem seedClosure_le_omegaCenter :
    seedClosure c ≤ omegaOneCenterAmbient ((pCore 2 c.H).map c.H.subtype) := by
  rw [omegaOneCenterAmbient_map_injective c.H.subtype c.H.subtype_injective]
  apply map_mono
  let _ := intrinsic_seedClosure_elementary c
  have hQ := TwoFactors.FFBranch.moduleClosure_le_twoCore c.sylow (d.Z.subgroupOf c.H)
    (seed_centralizer c) (overgroup_characteristic_two c)
  have hC := TwoFactors.FFBranch.moduleClosure_centralizer c.sylow (d.Z.subgroupOf c.H)
    (seed_centralizer c)
  intro z hz
  exact (mem_omegaOneCenterAmbient_iff _ _).mpr
    ⟨hQ hz, elemPow_eq_one_of_isElementaryAbelian z hz,
      fun q hq => (mem_centralizer_iff.mp (hC.symm.le hq) z hz).symm⟩

/-- Relative subnormality puts the seed commutator in the intrinsic block layer. -/
theorem seedClosure_commutator_le_firstLayer (b : ExchangedBlock c) :
    ⁅seedClosure c, b.first⁆ ≤ firstLayer b := by
  let L := b.first.subgroupOf c.H
  let V := normalClosure (d.Z.subgroupOf c.H : Set c.H)
  let _ : IsElementaryAbelian 2 V := intrinsic_seedClosure_elementary c
  have hc := commutator_le_core_commutator_of_isSubnormal L V
    b.relative_block.subnormal b.relative_block.short.twoPerfect
    (IsElementaryAbelian.isPGroup 2 V) (by rw [normalizer_eq_top]; exact le_top)
  have hm := map_mono (f := c.H.subtype) hc
  rw [map_commutator, map_subgroupOf_eq_of_le b.first_le] at hm
  change ⁅seedClosure c, b.first⁆ ≤ firstLayer b
  apply hm.trans
  let e : L ≃* b.first := subgroupOfEquivOfLe b.first_le
  have he : c.H.subtype.comp L.subtype = b.first.subtype.comp e.toMonoidHom := rfl
  change ((blockU L).map L.subtype).map c.H.subtype ≤ (blockU b.first).map b.first.subtype
  rw [map_map, he, ← map_map, map_blockU e]

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockEndgame.FieldFourCentrality
