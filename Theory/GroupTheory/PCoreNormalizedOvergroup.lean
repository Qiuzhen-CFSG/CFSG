module
public import Theory.PGroupCore

/-!
# Identifying the core of a local Sylow overgroup

Let P be a Sylow p-subgroup of a finite group, with P≤M≤N. If N normalizes
the p-core of M mapped into the ambient group, the mapped p-cores of M
and N coincide. The supplied Sylow subgroup and literal subtype embeddings
are retained throughout.

The core of N lies in P and hence in M. Its normality in N gives normality
in M, putting it in the core of M. Conversely, the normalization hypothesis
makes the core of M a normal p-subgroup of N, giving the reverse inclusion.

This is the standard core transfer used for the ambient middle-center
normalizer in Stellmacher (10.1)(a3), printed p.61, assertion (7), source
`refs/files/stellmacher-n-group.pdf`. The result applies to any prime p.
-/

namespace Subgroup
/-- A Sylow overgroup normalizing the local core has that same ambient core. -/
public theorem mapped_pCore_eq_of_normalized_local_pCore
    {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (P : Sylow p H) (M N : Subgroup H)
    (hPM : (P : Subgroup H) ≤ M) (hMN : M ≤ N)
    (hnorm : N ≤ normalizer ((pCore p M).map M.subtype : Set H)) :
    (pCore p N).map N.subtype = (pCore p M).map M.subtype := by
  let R := (pCore p N).map N.subtype
  let Q := (pCore p M).map M.subtype
  let PN : Sylow p N := P.subtype (hPM.trans hMN)
  have hRP : R ≤ (P : Subgroup H) := by
    rintro x ⟨r,hr,rfl⟩
    exact pCore_isPGroup.le_sylow_of_normal PN hr
  have hRM : R ≤ M := hRP.trans hPM
  have hNR : N ≤ normalizer (R : Set H) := by
    have hn := (pCore p N).le_normalizer_map N.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at hn
  let _ : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer (hMN.trans hNR)
  have hRp : IsPGroup p R := pCore_isPGroup.map N.subtype
  have hRQ : R ≤ Q := by
    rw [← map_subgroupOf_eq_of_le hRM]
    exact map_mono (show R.subgroupOf M ≤ pCore p M from
      le_sSup ⟨inferInstance, hRp.comap_subtype⟩)
  have hQN : Q ≤ N := (map_subtype_le (pCore p M)).trans hMN
  let _ : (Q.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer hnorm
  have hQp : IsPGroup p Q := pCore_isPGroup.map M.subtype
  have hQR : Q ≤ R := by
    rw [← map_subgroupOf_eq_of_le hQN]
    exact map_mono (show Q.subgroupOf N ≤ pCore p N from
      le_sSup ⟨inferInstance, hQp.comap_subtype⟩)
  exact le_antisymm hRQ hQR
end Subgroup
