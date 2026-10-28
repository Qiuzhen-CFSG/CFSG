module

public import Theory.SpecificGroups.ReeF4.MaximalSubgroups.SimpleNormal.UnitaryOvergroups.ProjectiveExtension

/-!
# Reduction of the unitary Ree overgroup calculation

Let S be normal in a maximal proper subgroup M of a Ree group. Relative
normality puts M in the ambient normalizer of S. Once that normalizer is
proved proper, maximality identifies it with M. An embedded PGU extension
then gives an actual subgroup of M; its relative normality and index two
transport from the ambient normalizer calculation.

This is conditional assembly. Constructing the projective extension and
proving its proper normalizer and quotient calculation remain separate
obligations. This file does not yet prove `unitaryOvergroups`.

Source: Malle, J. Algebra 139 (1991), 52–69,
DOI 10.1016/0021-8693(91)90283-E; PGU₃(q):2 is case 7 of the unconditional
list in the proof of Theorem 5 of Himstedt–Nguyen–Tiep, arXiv:0910.4758, p.3.
-/

public section

namespace ReeF4.MaximalSubgroups.SimpleNormal

open Subgroup

/-- Construct the required normal subgroup of M from an extension and the
geometric calculation of its ambient normalizer. Both missing inputs are
explicit and must be discharged before obtaining the unconditional theorem. -/
theorem unitaryOvergroups_of_extension_and_normalizer
    (hExtension : UnitaryEmbeddingExtensions)
    (hNormalizer : UnitaryExtensionNormalizers) : UnitaryOvergroups := by
  intro m hm M hM hsolv hR S hSn hSs hSa hC F _ _ J hcard hconj e
  let := hSn
  obtain ⟨E⟩ := hExtension m hm M hM hsolv hR S hSn hSs hSa hC F J hcard hconj e
  obtain ⟨hproper, hnormal, hindex⟩ :=
    hNormalizer m hm M hM hsolv hR S hSn hSs hSa hC F J hcard hconj e E
  have hle : M ≤ normalizer (S.map M.subtype) := by
    calc
      M = (normalizer (S : Set M)).map M.subtype := by
        rw [normalizer_eq_top, ← MonoidHom.range_eq_map, M.range_subtype]
      _ ≤ normalizer (S.map M.subtype) := le_normalizer_map M.subtype
  have heq : normalizer (S.map M.subtype) = M := (hM.le_iff_eq hproper).mp hle
  have hEM : E.embedding.range ≤ M := E.range_le_normalizer.trans heq.le
  refine ⟨E.embedding.range.subgroupOf M, ?_, ?_, ?_⟩
  · exact (congrArg (fun K : Subgroup (Model m) =>
      (E.embedding.range.subgroupOf K).Normal) heq).mp hnormal
  · exact ⟨(subgroupOfEquivOfLe hEM).trans (MonoidHom.ofInjective E.injective).symm⟩
  · exact (congrArg (fun K : Subgroup (Model m) =>
      Nat.card (K ⧸ E.embedding.range.subgroupOf K)) heq).symm.trans hindex

end ReeF4.MaximalSubgroups.SimpleNormal
