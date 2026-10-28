module

public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreSurjective
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.CommutatorPreimage

/-!
# Sylow centralizers of a residual section

A p-subgroup centralizing O^p(G) lies in O_p(G): intersect that centralizer
with a containing Sylow subgroup. The intersection is normalized by the
Sylow and centralized by the residual, and these generate G. Passing to G/O_p(G) gives the same conclusion for
centralization modulo O_p(G).

For a normal subgroup K, form the literal section centralizer
C_G(D/O_p(D)), where D is the embedded O^p(K). It contains O_p(G).
Every p-subgroup of this section centralizer meets K inside O_p(G).
Consequently, when O_p(G) lies in K, a Sylow subgroup of the section
centralizer meets K in exactly O_p(G).

Source application: Aschbacher–Smith, the opening of 13.4.8 and the
larger-kernel alternative of 13.4.4(2), printed pp.897 and904–905.
-/

@[expose] public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A p-subgroup fixing the p-residual is contained in the p-core. -/
theorem pSubgroup_le_pCore_of_centralizes_pResidual
    (R : Subgroup G) (hR : IsPGroup p R)
    (hc : R ≤ centralizer (pResidual p G : Set G)) : R ≤ pCore p G := by
  obtain ⟨T,hRT⟩ := hR.exists_le_sylow
  let A := (T : Subgroup G) ⊓ centralizer (pResidual p G : Set G)
  have hRA : pResidual p G ≤ centralizer (A : Set G) :=
    le_centralizer_iff.mp inf_le_right
  have hTn : (T : Subgroup G) ≤ normalizer (A : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have hn : A.Normal := normalizer_eq_top_iff.mp (top_unique (by
    have hh := sup_le (hRA.trans (centralizer_le_normalizer _)) hTn
    rwa [pResidual_sup_sylow_eq_top T] at hh))
  exact (le_inf hRT hc).trans (le_sSup ⟨hn,T.isPGroup'.to_le inf_le_left⟩)

/-- The same criterion holds for centralization modulo the p-core. -/
theorem pSubgroup_le_pCore_of_commutator_pResidual_le
    (R : Subgroup G) (hR : IsPGroup p R)
    (hc : ⁅R,pResidual p G⁆ ≤ pCore p G) : R ≤ pCore p G := by
  let q := QuotientGroup.mk' (pCore p G)
  have hcomm : ⁅R.map q,pResidual p (G ⧸ pCore p G)⁆ = ⊥ := by
    rw [← map_pResidual_of_surjective p q (QuotientGroup.mk'_surjective _),
      ← map_commutator]
    exact (map_eq_bot_iff _).mpr (by simpa only [q,QuotientGroup.ker_mk'] using hc)
  have hle := pSubgroup_le_pCore_of_centralizes_pResidual (R.map q) (hR.map q)
    (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have hh := (map_le_iff_le_comap).mp hle
  have hk : IsPGroup p q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup
  rwa [q.comap_pCore_of_ker_isPGroup (QuotientGroup.mk'_surjective _) hk] at hh

/-- The centralizer of the literal embedded residual modulo its own p-core. -/
def residualSectionCentralizer (p : ℕ) (K : Subgroup G) : Subgroup G :=
  let D := (pResidual p K).map K.subtype
  commutatorPreimage ⊤ D (D.pCoreIn p)

omit [Finite G] [Fact p.Prime] in
theorem residualSectionCentralizer_normal (K : Subgroup G) [K.Normal] :
    (residualSectionCentralizer p K).Normal := by
  let D := (pResidual p K).map K.subtype
  let : D.Normal := inferInstance
  let : (D.pCoreIn p).Normal := inferInstanceAs ((pCore p D).map D.subtype).Normal
  apply normalizer_eq_top_iff.mp
  apply top_unique
  exact commutatorPreimage_normalized ⊤ D (D.pCoreIn p) ⊤
    le_normalizer_of_normal le_normalizer_of_normal le_normalizer_of_normal
    le_normalizer_of_normal

omit [Finite G] [Fact p.Prime] in
theorem pCore_le_residualSectionCentralizer (K : Subgroup G) [K.Normal] :
    pCore p G ≤ residualSectionCentralizer p K := by
  let D := (pResidual p K).map K.subtype
  let : D.Normal := inferInstance
  apply le_commutatorPreimage le_top
  change ⁅pCore p G,D⁆ ≤ D.pCoreIn p
  rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype]
  exact le_inf (commutator_le_right _ _) (commutator_le_left _ _)

theorem pSubgroup_inf_le_pCore_of_residualSectionCentralizer
    (K R : Subgroup G) [K.Normal] (hR : IsPGroup p R)
    (hRC : R ≤ residualSectionCentralizer p K) : R ⊓ K ≤ pCore p G := by
  let D := (pResidual p K).map K.subtype
  let : D.Normal := inferInstance
  let : (D.pCoreIn p).Normal := inferInstanceAs ((pCore p D).map D.subtype).Normal
  have hDK : D ≤ K := map_subtype_le _
  have hcore : D.pCoreIn p ≤ K.pCoreIn p := by
    have hh : (pCore p D).map D.subtype ≤ pCore p G :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map D.subtype⟩
    have he : K.pCoreIn p = K ⊓ pCore p G := by
      rw [pCoreIn,pCore_eq_comap_of_normal,map_comap_eq,range_subtype]
    rw [he]
    exact le_inf ((pCoreIn_le p D).trans hDK) hh
  have hcomm : ⁅R,D⁆ ≤ K.pCoreIn p := by
    apply le_trans ((commutator_mono hRC le_rfl).trans
      (commutator_commutatorPreimage_le ⊤ D (D.pCoreIn p) le_normalizer_of_normal)) hcore
  have hi : ⁅R.subgroupOf K,pResidual p K⁆ ≤ pCore p K := by
    apply (map_le_map_iff_of_injective K.subtype_injective).mp
    rw [map_commutator,subgroupOf_map_subtype]
    exact (commutator_mono inf_le_left le_rfl).trans hcomm
  have hp := pSubgroup_le_pCore_of_commutator_pResidual_le
    (R.subgroupOf K) hR.comap_subtype hi
  have hm := map_mono (f := K.subtype) hp
  rw [subgroupOf_map_subtype] at hm
  exact hm.trans (le_sSup ⟨inferInstance,pCore_isPGroup.map K.subtype⟩)

/-- The Sylow centralizer intersection used in the larger action-kernel case. -/
theorem sylow_residualSectionCentralizer_inf_eq_pCore
    (K : Subgroup G) [K.Normal] (hQK : pCore p G ≤ K)
    (S : Sylow p (residualSectionCentralizer p K)) :
    (S : Subgroup (residualSectionCentralizer p K)).map
      (residualSectionCentralizer p K).subtype ⊓ K = pCore p G := by
  let C := residualSectionCentralizer p K
  let R := (S : Subgroup C).map C.subtype
  have hQC : pCore p G ≤ C := pCore_le_residualSectionCentralizer K
  have hQR : pCore p G ≤ R := by
    have hh := map_mono (f := C.subtype)
      ((pCore_isPGroup (p := p) (G := G)).comap_subtype.le_sylow_of_normal S)
    change ((pCore p G).subgroupOf C).map C.subtype ≤ R at hh
    rwa [map_subgroupOf_eq_of_le hQC] at hh
  exact le_antisymm
    (pSubgroup_inf_le_pCore_of_residualSectionCentralizer K R (S.isPGroup'.map C.subtype)
      (map_subtype_le _)) (le_inf hQR hQK)

end Subgroup
