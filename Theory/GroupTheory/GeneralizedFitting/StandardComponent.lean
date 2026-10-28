module

public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.TightlyEmbedded
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Terminal components and standard form

A quasisimple subgroup is in standard form when its centralizer is tightly
embedded, their normalizers coincide, and no conjugate of the subgroup
centralizes it. If the subgroup is a component of every involution centralizer
containing it, two distinct such components commute. Cauchy's theorem then
turns even intersections of conjugate centralizers into equality of the
corresponding components.

The terminal-to-standard criterion retains the separate hypothesis excluding
conjugate components in the centralizer, and the even order of the component.
These are genuine inputs; this general result does not establish them for a
particular finite group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, Lemma 16.3.2 and Remark 16.3.3, pp.1177–1178.
-/

@[expose] public section
namespace Theory.GroupTheory
open Subgroup
variable {G H : Type*} [Group G] [Group H]

/-- The involution-centralizer condition called terminal in §16.3. -/
def IsTerminalComponent (L : Subgroup G) : Prop :=
  ∀ t : G, t ∈ centralizer (L : Set G) → orderOf t = 2 →
    IsComponentIn L (centralizer ({t} : Set G))

/-- Standard form, with actual conjugate subgroups and ambient normalizers. -/
structure IsStandardComponent [Finite G] (L : Subgroup G) : Prop where
  quasisimple : IsQuasisimple L
  tightlyEmbedded : IsTightlyEmbedded (centralizer (L : Set G))
  normalizer_eq : normalizer (L : Set G) = normalizer (centralizer (L : Set G) : Set G)
  no_commuting_conjugate : ∀ g : G,
    ¬ L.map (MulAut.conj g).toMonoidHom ≤ centralizer (L : Set G)

/-- Isomorphisms carry a set centralizer to the centralizer of its image. -/
theorem map_centralizer_equiv (s : Set G) (e : G ≃* H) :
    (centralizer s).map e.toMonoidHom = centralizer (e '' s) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) ⟨y, hy, rfl⟩

/-- The terminal condition is preserved by an actual group isomorphism. -/
theorem IsTerminalComponent.map {L : Subgroup G} (h : IsTerminalComponent L)
    (e : G ≃* H) : IsTerminalComponent (L.map e.toMonoidHom) := by
  intro t ht ht2
  have hc : e.symm t ∈ centralizer (L : Set G) := by
    intro x hx
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using ht (e x) (mem_map_of_mem _ hx)
  have hi : orderOf (e.symm t) = 2 := (e.symm.orderOf_eq t).trans ht2
  have hm := (h (e.symm t) hc hi).map e
  simpa only [map_centralizer_equiv, Set.image_singleton, e.apply_symm_apply] using hm

/-- Under terminality, a commuting conjugate would already be a component
of the full centralizer. An involution inside L supplies the intermediate
involution centralizer; its existence is not assumed without justification. -/
theorem IsTerminalComponent.no_commuting_conjugate [Finite G]
    {L : Subgroup G} (h : IsTerminalComponent L) (heven : Even (Nat.card L))
    (hexclude : ∀ g : G, ¬ IsComponentIn (L.map (MulAut.conj g).toMonoidHom)
      (centralizer (L : Set G))) (g : G) :
    ¬ L.map (MulAut.conj g).toMonoidHom ≤ centralizer (L : Set G) := by
  intro hcomm
  obtain ⟨i, hi⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 (even_iff_two_dvd.mp heven)
  have hi2 : orderOf (i : G) = 2 := (orderOf_coe i).trans hi
  have hc : (i : G) ∈ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) :=
    (le_centralizer_iff.mp hcomm) i.property
  have hcomponent := h.map (MulAut.conj g) i hc hi2
  have hCL : centralizer (L : Set G) ≤ centralizer ({(i : G)} : Set G) :=
    centralizer_le (Set.singleton_subset_iff.mpr i.property)
  exact hexclude g (hcomponent.restrict hcomm hCL)

/-- Even intersection of conjugate centralizers forces equality of the two
components, if terminality and the absence of commuting conjugates hold. -/
theorem IsTerminalComponent.mem_normalizer_of_even_intersection [Finite G]
    {L : Subgroup G} (h : IsTerminalComponent L)
    (hcomm : ∀ g : G, ¬ L.map (MulAut.conj g).toMonoidHom ≤ centralizer (L : Set G))
    (g : G) (heven : Even (Nat.card ↥(centralizer (L : Set G) ⊓
      (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom))) :
    g ∈ normalizer (L : Set G) := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := ↥(centralizer (L : Set G) ⊓
      (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom))
    2 (even_iff_two_dvd.mp heven)
  have ht2 : orderOf (t : G) = 2 := (orderOf_coe t).trans ht
  have htC : (t : G) ∈ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G) :=
    map_centralizer_le_centralizer_image _ _ t.property.2
  have hL := h t t.property.1 ht2
  have hLg := h.map (MulAut.conj g) t htC ht2
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  exact hcomm g (commutator_eq_bot_iff_le_centralizer.mp
    (hLg.commutator_eq_bot_of_ne hL hne))

/-- The general terminal-to-standard argument, after exclusion of commuting
conjugates. The source-specific exclusions remain separate obligations. -/
theorem IsTerminalComponent.standard_of_no_commuting_conjugate [Finite G]
    {L : Subgroup G} (h : IsTerminalComponent L)
    (heven : Even (Nat.card (centralizer (L : Set G))))
    (hcomm : ∀ g : G, ¬ L.map (MulAut.conj g).toMonoidHom ≤ centralizer (L : Set G)) :
    IsStandardComponent L := by
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card'
    (G := centralizer (L : Set G)) 2 (even_iff_two_dvd.mp heven)
  have hq := (h t t.property ((orderOf_coe t).trans ht)).quasisimple
  have hNL := normalizer_le_normalizer_centralizer L
  have hn : normalizer (L : Set G) = normalizer (centralizer (L : Set G) : Set G) := by
    apply le_antisymm hNL
    intro g hg
    apply h.mem_normalizer_of_even_intersection hcomm g
    have heq : (centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom =
        centralizer (L : Set G) := mem_normalizer_iff_map_conj_eq.mp hg
    rw [heq, inf_idem]
    exact heven
  refine ⟨hq, ⟨heven, ?_⟩, hn, hcomm⟩
  intro g hg
  apply Nat.not_even_iff_odd.mp
  intro hev
  exact hg (hNL (h.mem_normalizer_of_even_intersection hcomm g hev))

/-- Lemma 16.3.2's component-theoretic argument, with the preceding
conjugate-component exclusion and both even-order inputs explicit. -/
theorem IsTerminalComponent.standard_of_no_conjugate_component [Finite G]
    {L : Subgroup G} (h : IsTerminalComponent L) (hL : Even (Nat.card L))
    (hC : Even (Nat.card (centralizer (L : Set G))))
    (hexclude : ∀ g : G, ¬ IsComponentIn (L.map (MulAut.conj g).toMonoidHom)
      (centralizer (L : Set G))) : IsStandardComponent L :=
  h.standard_of_no_commuting_conjugate hC (h.no_commuting_conjugate hL hexclude)

/-- A nontrivial two-subgroup of the centralizer controls its ambient
normalizer. This is Remark 16.3.3 without any classification hypothesis. -/
theorem IsStandardComponent.normalizer_le [Finite G] {L Q : Subgroup G}
    (h : IsStandardComponent L) (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hle : Q ≤ centralizer (L : Set G)) : normalizer (Q : Set G) ≤ normalizer (L : Set G) := by
  rw [h.normalizer_eq]
  exact h.tightlyEmbedded.normalizer_le hQ hne hle

/-- In particular, the centralizer of an involution centralizing a standard
component normalizes that component. -/
theorem IsStandardComponent.involution_centralizer_le [Finite G] {L : Subgroup G}
    (h : IsStandardComponent L) {t : G} (ht : t ∈ centralizer (L : Set G))
    (ht2 : orderOf t = 2) : centralizer ({t} : Set G) ≤ normalizer (L : Set G) := by
  have hp : IsPGroup 2 (zpowers t) := by
    apply IsPGroup.of_card (n := 1)
    simpa only [Nat.card_zpowers, pow_one] using ht2
  have hne : zpowers t ≠ ⊥ := by
    intro he
    have ht1 : t = 1 := by simpa only [he, mem_bot] using mem_zpowers t
    simp [ht1] at ht2
  rw [← normalizer_zpowers_eq_centralizer_of_order_two t ht2]
  exact h.normalizer_le hp hne (zpowers_le.mpr ht)

/-- A standard component is terminal: it is normal and quasisimple in
any involution centralizer containing it. -/
theorem IsStandardComponent.terminal [Finite G] {L : Subgroup G}
    (h : IsStandardComponent L) : IsTerminalComponent L := by
  intro t ht ht2
  have hLC : L ≤ centralizer ({t} : Set G) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (ht x hx)
  let : (L.subgroupOf (centralizer ({t} : Set G))).Normal :=
    (normal_subgroupOf_iff_le_normalizer hLC).mpr (h.involution_centralizer_le ht ht2)
  let := h.quasisimple
  exact ⟨hLC, (inferInstance : (L.subgroupOf (centralizer ({t} : Set G))).Normal).isSubnormal,
    IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hLC).symm⟩

end Theory.GroupTheory
