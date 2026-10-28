module

public import CFSG.Quasithin.ChapterA.Section02.Statements
public import Theory.GroupTheory.GeneralizedFitting.ComponentLayerStructure
public import Theory.Quasithin.Rank
public import Theory.Quasithin.LocalRankEmbedding

/-!
# Minimal covering in Theorem A

Aschbacher–Smith, *The Classification of Quasithin Groups*, A.2.8–9,
printed pp.34–35. A counterexample minimal on proper sections cannot have
its offending section covered by a proper subgroup. Rank monotonicity
transports both inequalities, and an embedding transports the entire unitary
exception, including its embedded-center equality. The section is therefore
a quotient of the ambient group. Since the section is semisimple, its perfectness
also forces the ambient group to be perfect by the same covering argument.

The induction premise is the exact `TheoremAOnProperSections` predicate;
no structural or classification conclusion is assumed.
-/

@[expose] public section

open Theory.GroupTheory Subgroup
namespace CFSG.Quasithin.ChapterA.Section02
universe u v w
variable {G : Type u} {H : Type v} {S : Type w} [Group G] [Group H] [Group S]

private theorem map_center_equiv (e : G ≃* H) :
    (center G).map e.toMonoidHom = center H := by
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact (centerCongr e ⟨a, ha⟩).property
  · intro hx
    exact ⟨e.symm x, (centerCongr e.symm ⟨x, hx⟩).property, e.apply_symm_apply x⟩

private theorem embedded_center_map (L : Subgroup G) (e : G ≃* H) :
    (center (L.map e.toMonoidHom)).map (L.map e.toMonoidHom).subtype =
      ((center L).map L.subtype).map e.toMonoidHom := by
  have hc := map_center_equiv (Subgroup.equivMapOfInjective L e.toMonoidHom e.injective)
  rw [← hc, map_map, map_map]
  rfl

/-- Transport the complete unitary-pair witness along an isomorphism. -/
def TheoremAUnitaryPair.map (d : TheoremAUnitaryPair G) (e : G ≃* H) :
    TheoremAUnitaryPair H where
  first := d.first.map e.toMonoidHom
  second := d.second.map e.toMonoidHom
  first_component := d.first_component.map_equiv e
  second_component := d.second_component.map_equiv e
  product h := by
    obtain ⟨a, b, hab⟩ := d.product (e.symm h)
    refine ⟨e.subgroupMap d.first a, e.subgroupMap d.second b, ?_⟩
    change e (a : G) * e (b : G) = h
    rw [← map_mul, hab, e.apply_symm_apply]
  n₁ := d.n₁
  n₂ := d.n₂
  first_large := d.first_large
  second_large := d.second_large
  first_odd := d.first_odd
  second_odd := d.second_odd
  first_model := d.first_model.of_mulEquiv (e.subgroupMap d.first).symm
  second_model := d.second_model.of_mulEquiv (e.subgroupMap d.second).symm
  centers_eq := by rw [embedded_center_map, embedded_center_map, d.centers_eq]
  gcd_eq := d.gcd_eq

/-- The exceptional subgroup remains a witness in any ambient overgroup. -/
theorem TheoremAException.ambient_injective [Finite G] [Finite H] {p : ℕ}
    (h : TheoremAException G S p) (f : G →* H) (hf : Function.Injective f) :
    TheoremAException H S p := by
  obtain ⟨rfl, U, hr, ⟨a⟩, ⟨d⟩⟩ := h
  let e := Subgroup.equivMapOfInjective U f hf
  refine ⟨rfl, U.map f, ?_, ⟨a.trans (QuotientGroup.congr _ _ e (map_center_equiv e))⟩,
    ⟨d.map e⟩⟩
  exact (primeRank_equiv 3 e).symm.trans hr

/-- Both conclusions of A ascend through an embedding into a group of local rank at most two. -/
theorem TheoremAConclusion.ambient_injective [Finite G] [Finite H] {p : ℕ}
    (h : TheoremAConclusion G S p) (f : G →* H) (hf : Function.Injective f)
    (hH : twoLocalPrimeRank p H ≤ 2) : TheoremAConclusion H S p := by
  have hr := Theory.GroupTheory.primeRank_le_of_injective p f hf
  refine ⟨?_, fun hle => (h.2 (hr.trans hle)).trans hr⟩
  rcases h.1 with hl | he
  · exact .inl ⟨hl.1.trans (twoLocalPrimeRank_le_of_injective p f hf), hH⟩
  · exact .inr (he.ambient_injective f hf)

end CFSG.Quasithin.ChapterA.Section02

namespace CFSG.Quasithin.ChapterA.Section02
universe u
variable {K : GroupClass.{u}} {G S : Type u}
    [Group G] [Group S] [Finite G] [Finite S] {p : ℕ}

/-- A.2.8: every subgroup covering the offending section is the whole group. -/
theorem lemma_A_2_8 (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremAOnProperSections K G) {U : Subgroup G}
    (hSU : IsSectionOf S U) : U = ⊤ := by
  by_contra hU
  have hA := ih U (IsProperSectionOf.subgroup U hU)
  have hc := hA (h.1.subgroup U) (h.2.1.subgroup U) S hSU h.2.2.2.1 p
    h.2.2.2.2.1 h.2.2.2.2.2.1
  apply h.2.2.2.2.2.2
  exact hc.ambient_injective U.subtype U.subtype_injective
    (isQuasithin_iff_twoLocalPrimeRank.mp h.1 p h.2.2.2.2.1 h.2.2.2.2.2.1)

/-- Minimal covering realizes the offending section as a surjective image of G. -/
theorem CounterexampleToTheoremA.exists_surjective
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    ∃ f : G →* S, Function.Surjective f := by
  obtain ⟨U, f, hf⟩ := h.2.2.1
  have hU := lemma_A_2_8 h ih (IsSectionOf.of_surjective f hf)
  subst U
  exact ⟨f.comp (Subgroup.topEquiv (G := G)).symm.toMonoidHom,
    hf.comp (Subgroup.topEquiv (G := G)).symm.surjective⟩

/-- The actual normal quotient in Notation A.2.9. -/
theorem lemma_A_2_9 (h : CounterexampleToTheoremA K G S p)
    (ih : TheoremAOnProperSections K G) :
    ∃ (N : Subgroup G) (_ : N.Normal), Nonempty ((G ⧸ N) ≃* S) := by
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  exact ⟨f.ker, inferInstance, ⟨QuotientGroup.quotientKerEquivOfSurjective f hf⟩⟩

omit [Finite S] in
/-- A group generated by its components is perfect. -/
theorem IsSemisimple.isPerfect (h : IsSemisimple S) : Group.IsPerfect S := by
  have hc := componentLayer_isPerfect (G := S)
  rw [show componentLayer S = ⊤ from h] at hc
  exact Group.IsPerfect.top_iff.mp hc

/-- The derived subgroup also covers S, so minimal covering makes G perfect. -/
theorem CounterexampleToTheoremA.isPerfect
    (h : CounterexampleToTheoremA K G S p) (ih : TheoremAOnProperSections K G) :
    Group.IsPerfect G := by
  let := h.2.2.2.1.isPerfect
  obtain ⟨f, hf⟩ := h.exists_surjective ih
  have hmap : (commutator G).map f = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective f hf,
      ← commutator_def, Group.IsPerfect.commutator_eq_top]
  have hsur : Function.Surjective (f.comp (commutator G).subtype) := by
    rw [← MonoidHom.range_eq_top]
    simpa only [MonoidHom.range_comp, Subgroup.range_subtype] using hmap
  exact ⟨lemma_A_2_8 h ih (IsSectionOf.of_surjective _ hsur)⟩

end CFSG.Quasithin.ChapterA.Section02
