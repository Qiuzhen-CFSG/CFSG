module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann.RankOne.Generation
public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore

/-!
# Localizing the rank-one Baumann hypotheses inside H

The native block is O²(H), and the native module is the literal restriction
of U(L). The supplied centralizer identity identifies its action kernel
with O₂(H), so the faithful action quotient has trivial two-core. The
module remains elementary abelian and normal, satisfies [U,L] = U, and
is moved by the actual Thompson subgroup of the supplied Sylow subgroup.

These facts supply the elementary hypotheses of B.6.10 inside H, without
an SQTK assumption on the original ambient group. Applying that theorem
still requires its natural-module calculation, including the A₃ case.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
B.6.10, printed p.117; C.1.11 and C.5.4, printed pp.124 and 155.
-/

public section

namespace CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann
open Subgroup Stellmacher Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G]
variable {K : GroupClass.{u}} {A H R L : Subgroup G}

/-- The native group has the generalized-Fitting hypothesis of B.6.10. -/
theorem native_generalizedFitting (h : Configuration K A H R L) :
    generalizedFitting H = pCore 2 H :=
  generalizedFitting_eq_pCore_of_selfCentralizing 2 h.characteristicTwo

omit [Finite G] in
/-- The block becomes the literal two-residual when H is the ambient group. -/
theorem native_block_eq_residual (h : Configuration K A H R L) :
    L.subgroupOf H = pResidual 2 H := by
  rw [← h.residual]
  exact comap_map_eq_self_of_injective H.subtype_injective _

omit [Finite G] in
/-- The block is normal inside H; ambient normality in G is not asserted. -/
theorem native_block_normal (h : Configuration K A H R L) :
    (L.subgroupOf H).Normal := by
  rw [native_block_eq_residual h]
  infer_instance

/-- The actual module U(L), restricted to H, is normal. -/
theorem native_module_normal (h : Configuration K A H R L) :
    ((U L).subgroupOf H).Normal :=
  (normal_subgroupOf_iff_le_normalizer ((module_le_HCore h).trans (pCoreIn_le 2 H))).mpr
    (normalizes_module h)

/-- Restriction of the embedded module retains elementary abelianness. -/
theorem native_module_elementary (h : Configuration K A H R L) :
    IsElementaryAbelian 2 ((U L).subgroupOf H) := by
  let _ := module_elementary h
  exact IsElementaryAbelian.subgroupOf ((module_le_HCore h).trans (pCoreIn_le 2 H))

/-- The supplied C.1.11 equality gives exactly the native action kernel. -/
theorem native_module_centralizer (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H) :
    centralizer ((U L).subgroupOf H : Set H) = pCore 2 H := by
  apply map_injective H.subtype_injective
  rw [map_centralizer_subtype, map_subgroupOf_eq_of_le
    ((module_le_HCore h).trans (pCoreIn_le 2 H))]
  exact hc

/-- The native module is two-reduced, the R₂(H) condition in B.6.10. -/
theorem native_module_reduced (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H) :
    let _ := native_module_normal h
    pCore 2 (H ⧸ centralizer ((U L).subgroupOf H : Set H)) = ⊥ := by
  let _ := native_module_normal h
  let e := QuotientGroup.quotientMulEquivOfEq (native_module_centralizer h hc)
  have hn : ((pCore 2 (H ⧸ centralizer ((U L).subgroupOf H : Set H))).map
      e.toMonoidHom).Normal := Subgroup.Normal.map inferInstance e.toMonoidHom e.surjective
  have he : (pCore 2 (H ⧸ centralizer ((U L).subgroupOf H : Set H))).map
      e.toMonoidHom ≤ pCore 2 (H ⧸ pCore 2 H) :=
    le_sSup ⟨hn, pCore_isPGroup.map e.toMonoidHom⟩
  apply (map_eq_bot_iff_of_injective _ (f := e.toMonoidHom) e.injective).mp
  exact le_bot_iff.mp (he.trans_eq (pCore_quotient_pCore_eq_bot 2))

/-- The commutator module in B.6.10 is the native copy of U(L). -/
theorem native_module_commutator (h : Configuration K A H R L) :
    ⁅(U L).subgroupOf H, L.subgroupOf H⁆ = (U L).subgroupOf H := by
  apply map_injective H.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le
    ((module_le_HCore h).trans (pCoreIn_le 2 H)),
    map_subgroupOf_eq_of_le (h.join_eq ▸ le_sup_left)]
  exact module_commutator_eq h

/-- The specified Sylow's actual Thompson subgroup moves the native module. -/
theorem native_thompson_moves_module (h : Configuration K A H R L)
    (hc : H ⊓ centralizer (U L : Set G) = pCoreIn 2 H)
    (T : Sylow 2 H) (hT : (T : Subgroup H).map H.subtype = R) :
    ¬ elementaryAbelianMaxJ (T : Subgroup H) ≤
      centralizer ((U L).subgroupOf H : Set H) := by
  intro hJ
  rw [native_module_centralizer h hc] at hJ
  apply thompson_not_le_HCore h
  have hm := map_mono (f := H.subtype) hJ
  rwa [← elementaryAbelianMaxJ_map_injective H.subtype H.subtype_injective, hT] at hm

end CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Baumann

end
