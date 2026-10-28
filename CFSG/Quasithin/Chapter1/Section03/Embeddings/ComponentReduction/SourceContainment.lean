module
public import Theory.GroupAction.IrreducibleInnerContainment
public import CFSG.Quasithin.Chapter1.Section03.Embeddings.ComponentReduction.SourceElementary

/-!
# Complete intrinsic containment in a normal component

The original quotient complement induces inner automorphisms on the detected
normal component and has irreducible normalizer action. A noncentral element
of order p in that same component forces containment by the ambient odd-rank
two theorem. Coprime absorption through O₂(H) gives P ≤ L, and the original
conjugate-generation equation then gives X ≤ L.

The center-coprime branch constructs the prime-order witness from the detected
nontrivial action. This includes extraspecial complements with no elementary
assumption. The final theorem also discharges the p-center branch using the actual
exponent-p complement and perfect component. It proves the full normal-component
containment. The exchanged-component branch and subsequent model classification
remain separate source obligations.

Source: Aschbacher–Smith, Proposition 1.3.4, printed p.510. Genuine universal
Theorems A and C supply the earlier inner-action theorem.
-/

public section
namespace CFSG.Quasithin.Chapter1.XiEmbedding
universe u
open Subgroup Theory.GroupTheory
variable {G : Type u} [Group G] [Finite G]

theorem LocalInput.quotient_complement_le_normal_component_of_noncentral_prime
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (quotientImage H L).Normal)
    (x : quotientImage H L) (hx : orderOf x = p)
    (hxZ : x ∉ center (quotientImage H L)) :
    quotientImage H P ≤ quotientImage H L := by
  let : Fact p.Prime := ⟨h.prime⟩
  let := hn
  have hi : IsNormalizerFrattiniIrreducible (quotientImage H P) := h.quotient_normalizer_irreducible
  exact hi.le_normal_of_inner_of_noncentral_prime
    h.quotient_odd_complement.isPGroup h.odd h.quotient_complement_not_cyclic
    (quotient_stronglyQuasithin hH.stronglyQuasithin p h.prime h.odd) _
    (h.quotient_complement_le_component_centralizer hA hC hH hL hn) x hx hxZ

theorem LocalInput.quotient_complement_le_normal_component_of_coprime_center
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (quotientImage H L).Normal)
    (hZ : ¬ p ∣ Nat.card (center (quotientImage H L))) :
    quotientImage H P ≤ quotientImage H L := by
  let : Fact p.Prime := ⟨h.prime⟩
  let := hn
  have hi : IsNormalizerFrattiniIrreducible (quotientImage H P) := h.quotient_normalizer_irreducible
  exact hi.le_normal_of_inner_of_coprime_center
    h.quotient_odd_complement.isPGroup h.odd h.quotient_complement_not_cyclic
    (quotient_stronglyQuasithin hH.stronglyQuasithin p h.prime h.odd) _
    (h.quotient_complement_le_component_centralizer hA hC hH hL hn)
    (hL.quotient_commutator_ne_bot h.complement_le_overgroup) hZ

omit [Finite G] in
private theorem LocalInput.complement_and_X_le_of_quotient_containment
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hL : ComponentDetection P H L) (hn : (L.subgroupOf H).Normal)
    (hinc : quotientImage H P ≤ quotientImage H L) : P ≤ L ∧ X ≤ L := by
  let : Fact p.Prime := ⟨h.prime⟩
  let := hn
  have hsup : P.subgroupOf H ≤ L.subgroupOf H ⊔ pCore 2 H := by
    have hh := map_le_iff_le_comap.mp hinc
    change P.subgroupOf H ≤ ((L.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H))).comap
      (QuotientGroup.mk' (pCore 2 H)) at hh
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

theorem LocalInput.complement_and_X_le_normal_component_of_noncentral_prime
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (L.subgroupOf H).Normal)
    (x : quotientImage H L) (hx : orderOf x = p)
    (hxZ : x ∉ center (quotientImage H L)) : P ≤ L ∧ X ≤ L := by
  let := hn
  have hbar : (quotientImage H L).Normal :=
    Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)
  exact h.complement_and_X_le_of_quotient_containment hL hn
    (h.quotient_complement_le_normal_component_of_noncentral_prime hA hC hH hL hbar x hx hxZ)

theorem LocalInput.complement_and_X_le_normal_component_of_coprime_center
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (L.subgroupOf H).Normal)
    (hZ : ¬ p ∣ Nat.card (center (quotientImage H L))) : P ≤ L ∧ X ≤ L := by
  let := hn
  have hbar : (quotientImage H L).Normal :=
    Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)
  exact h.complement_and_X_le_of_quotient_containment hL hn
    (h.quotient_complement_le_normal_component_of_coprime_center hA hC hH hL hbar hZ)

/-- The complete normal-component containment on the literal quotient images. -/
theorem LocalInput.quotient_complement_le_normal_component
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (quotientImage H L).Normal) :
    quotientImage H P ≤ quotientImage H L := by
  let : Fact p.Prime := ⟨h.prime⟩
  let := hn
  let : IsQuasisimple (quotientImage H L) := hL.component.2
  have hi : IsNormalizerFrattiniIrreducible (quotientImage H P) := h.quotient_normalizer_irreducible
  apply hi.le_normal_of_inner_of_exponent_p h.quotient_odd_complement.isPGroup h.odd
    h.quotient_complement_not_cyclic ?_
    (quotient_stronglyQuasithin hH.stronglyQuasithin p h.prime h.odd) _
    (h.quotient_complement_le_component_centralizer hA hC hH hL hn)
    (hL.quotient_commutator_ne_bot h.complement_le_overgroup)
  intro a
  rcases h.quotient_odd_complement with ⟨he,_⟩ | ⟨_,_,hexp⟩
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp he.exponent_dvd_p a
  · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (dvd_of_eq hexp) a

/-- Both original groups lie in the normal detected component, for either
source complement alternative, including extraspecial order p³ exponent p. -/
theorem LocalInput.complement_and_X_le_normal_component
    (hA : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremA KnownSimple.IsKnownSimple Y)
    (hC : ∀ (Y : Type u) [Group Y] [Finite Y],
      ChapterA.Section02.TheoremC KnownSimple.IsKnownSimple Y)
    {p : ℕ} {T X P H L : Subgroup G} (h : LocalInput p T X P H)
    (hH : IsSQTK KnownSimple.IsKnownSimple H)
    (hL : ComponentDetection P H L) (hn : (L.subgroupOf H).Normal) : P ≤ L ∧ X ≤ L := by
  let := hn
  have hbar : (quotientImage H L).Normal :=
    Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)
  exact h.complement_and_X_le_of_quotient_containment hL hn
    (h.quotient_complement_le_normal_component hA hC hH hL hbar)

end CFSG.Quasithin.Chapter1.XiEmbedding
