module
public import Theory.Mathieu.M22.Properties.HexadSplitCoordinates.Coordinates
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.Mathieu.M22.ChapterHLocalClassification.Sylow.Marking
public import Theory.SpecificGroups.AlternatingSix.ProperSylowOvergroups
public import Mathlib.GroupTheory.IsSubnormal
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Exclusion of the hexad core for a local A5 in M22

Let B be subnormal in its join with the fixed compatible full Sylow two-group
of M22, with B/O₂(B) isomorphic to A5. Its embedded two-core cannot be the
hexad kernel: characteristicity and the marked Sylow put the join in the
literal hexad stabilizer. The six-point quotient sends B to order sixty
and the Sylow to a full Sylow of A6. The proper Sylow-overgroup theorem
forces the join onto A6, contradicting simplicity and subnormality.

All maps retain the original degree-22 hexad and ambient two-core; no
classification of abstract E16:A5 embeddings is used.

Source: Aschbacher--Smith, A.3.12 and A.3.14(6), the M22 local A5 row.
-/

public section

open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped Pointwise
namespace Sporadic.Mathieu.M22LocalA5Placement

/-- The actual hexad kernel is incompatible with a locally subnormal A5 quotient. -/
theorem core_ne_hexad_kernel (B : Subgroup M22)
    (hsub : (B.subgroupOf (B ⊔ M22ChapterH.CompatibleSylow.inner.toSubgroup)).IsSubnormal)
    (eB : B ⧸ pCore 2 B ≃* alternatingGroup (Fin 5))
    : B.pCoreIn 2 ≠ m22InnerHexadKernel m22SourceOctad := by
  intro hcore
  let N := MulAction.stabilizer M22 M22HexadCoordinates.base
  let S := M22ChapterH.CompatibleSylow.inner
  let H := B ⊔ S.toSubgroup
  have hBN : B ≤ N := by
    have hn : B ≤ normalizer (B.pCoreIn 2 : Set M22) := by
      simpa only [pCoreIn, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
        using (pCore 2 B).le_normalizer_map B.subtype
    rw [hcore, ← M22HexadCoordinates.base_kernel,
      m22HexadPointwiseKernel_normalizer m22Hexad24Ten_mem] at hn
    exact hn
  have hSN : S.toSubgroup ≤ N := by
    change S.toSubgroup ≤ MulAction.stabilizer M22 M22HexadCoordinates.base
    rw [M22HexadCoordinates.base_stabilizer]
    exact comap_mono M22ChapterH.CompatibleSylow.ambient_le_octad
  have hHN : H ≤ N := sup_le hBN hSN
  let q := m22HexadSixMap m22Hexad24Ten_mem
  let fB : B →* alternatingGroup (Fin 6) := q.comp (inclusion hBN)
  let fH : H →* alternatingGroup (Fin 6) := q.comp (inclusion hHN)
  have hk : fB.ker = pCore 2 B := by
    ext x
    change q (inclusion hBN x) = 1 ↔ x ∈ pCore 2 B
    rw [← MonoidHom.mem_ker, m22HexadSixMap_ker, mem_m22SetAction_ker]
    change (∀ a ∈ M22HexadCoordinates.base, x.val • a = a) ↔ _
    rw [← mem_m22HexadPointwiseKernel, M22HexadCoordinates.base_kernel, ← hcore]
    change x.val ∈ (pCore 2 B).map B.subtype ↔ x ∈ pCore 2 B
    exact mem_map_iff_mem B.subtype_injective
  have hc : Nat.card fB.range = 60 := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange fB).toEquiv, hk,
      Nat.card_congr eB.toEquiv, nat_card_alternatingGroup]
    norm_num
  have hBR : fB.range ≤ fH.range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨⟨b.val, (show B ≤ H from le_sup_left) b.property⟩, rfl⟩
  let T := (S.subtype hSN).mapSurjective (m22HexadSixMap_surjective m22Hexad24Ten_mem)
  have hTR : T.toSubgroup ≤ fH.range := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨⟨x.val, (show S.toSubgroup ≤ H from le_sup_right) hx⟩, rfl⟩
  have htop : fH.range = ⊤ := by
    by_contra hn
    have hd := card_dvd_of_le hBR
    rw [hc] at hd
    rcases AlternatingSix.ProperSylowOvergroups.card_eight_or_twentyFour T _ hTR hn with h | h <;>
      rw [h] at hd <;> norm_num at hd
  have himage : (B.subgroupOf H).map fH = fB.range := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y.val, hy⟩, rfl⟩
    · rintro ⟨b, rfl⟩
      exact ⟨⟨b.val, (show B ≤ H from le_sup_left) b.property⟩, b.property, rfl⟩
  have hs : fB.range.IsSubnormal := by
    rw [← himage]
    exact hsub.map (MonoidHom.range_eq_top.mp htop)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  rcases hs.eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
  · rw [h, card_bot] at hc
    norm_num at hc
  · rw [h, card_top, nat_card_alternatingGroup] at hc
    norm_num at hc

end Sporadic.Mathieu.M22LocalA5Placement
