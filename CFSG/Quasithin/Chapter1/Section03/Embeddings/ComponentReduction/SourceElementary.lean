module
public import Theory.GroupAction.IrreducibleElementaryContainment
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceIntersections

/-!
# Intrinsic containment for a normal component and elementary complement

The original elementary complement embeds in H/O₂(H). The established
inner-action and rank bounds force its image into the normal detected
component. Coprime quotient absorption then puts the original complement
in L, and the source conjugate-generation identity puts X in L as well.
This closes the elementary branch of normal-component containment; the
extraspecial complement and the exchanged-component case remain separate.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.510. Genuine Theorems
A and C remain the earlier source inputs used by the inner-action step.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
open Subgroup Theory.GroupTheory
variable {G : Type u} [Group G] [Finite G]

theorem LocalInput.quotient_complement_le_normal_component_of_elementary
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (quotientImage H L).Normal)
    (he : IsElementaryAbelian p P) :
    quotientImage H P ≤ quotientImage H L := by
  let : Fact p.Prime := ⟨h.prime⟩
  let : IsElementaryAbelian p (quotientImage H P) :=
    he.of_surjective h.quotientComplementEquiv.toMonoidHom h.quotientComplementEquiv.surjective
  have hc : Nat.card (quotientImage H P) = p ^ 2 := by
    rcases h.quotient_odd_complement with ⟨_, hc⟩ | ⟨hex, hc, _⟩
    · exact hc
    · exact ((QuotientGroup.nontrivial_iff.mp hex.quotient_nontrivial)
        (center_eq_top (G := quotientImage H P))).elim
  let := hn
  have hi : IsNormalizerFrattiniIrreducible (quotientImage H P) :=
    h.quotient_normalizer_irreducible
  exact hi.le_normal_of_elementary_inner hc
    (quotient_stronglyQuasithin hH.stronglyQuasithin p h.prime h.odd) _
    (h.quotient_complement_le_component_centralizer hA hC hH hL hn)
    (hL.quotient_commutator_ne_bot h.complement_le_overgroup)

theorem LocalInput.complement_and_X_le_normal_component_of_elementary
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (L.subgroupOf H).Normal)
    (he : IsElementaryAbelian p P) : P ≤ L ∧ X ≤ L := by
  let : Fact p.Prime := ⟨h.prime⟩
  let := hn
  have hbar : (quotientImage H L).Normal :=
    Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hinc := LocalInput.quotient_complement_le_normal_component_of_elementary hA hC h hH hL hbar he
  have hsup : P.subgroupOf H ≤ L.subgroupOf H ⊔ pCore 2 H := by
    have hh := map_le_iff_le_comap.mp hinc
    change P.subgroupOf H ≤ ((L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).comap (QuotientGroup.mk' (pCore 2 H)) at hh
    rw [comap_map_eq, QuotientGroup.ker_mk'] at hh
    exact hh
  have hsub : P.subgroupOf H ≤ L.subgroupOf H :=
    le_normal_of_le_sup_coprime_pGroup _ _ _
      h.odd_complement.isPGroup.comap_subtype pCore_isPGroup
      (Nat.coprime_two_right.mpr h.odd) hsup
  have hPL : P ≤ L := by
    have hm := map_mono (f := H.subtype) hsub
    simpa only [map_subgroupOf_eq_of_le h.complement_le_overgroup,
      map_subgroupOf_eq_of_le hL.mem.1] using hm
  exact ⟨hPL, h.le_of_complement_le hPL
    ((normal_subgroupOf_iff_le_normalizer hL.mem.1).mp hn)⟩

end CFSG.Quasithin.Chapter1.XiEmbedding
