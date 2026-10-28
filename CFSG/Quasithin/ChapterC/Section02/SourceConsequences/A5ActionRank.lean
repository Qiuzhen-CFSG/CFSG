module
public import CFSG.Quasithin.ChapterC.Section02.SourceConsequences.SpanOddRank
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.SourceOrbits
public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.GroupTheory.CComponent.PairActionKernel

/-!
# Five-rank in the original A₅ span action

When the selected component K is normal in H, its literal core-central
quotient action extends to H. The action kernel is therefore invariant
under M. If it killed either of the two conjugate A₅ components, it would
kill their full span. The nontrivial action consequently has a two-group
kernel on that span and preserves its odd-prime ranks.

For the original nonnormal A₅ configuration, the actual action image has
five-rank at least two. A local bound of one now forces M to normalize L.
No faithfulness of an abstract pair model is assumed.

Source: Aschbacher–Smith C.4.5–8, printed pp.152–154, specialized to the
original A₅ covering configuration in 4.2.12–13, printed pp.610–611.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
universe u
variable {G : Type u} [Group G] [Finite G] {H M L R V : Subgroup G}
variable {κ : GroupClass.{u}}

/-- The actual quotient action retains every odd-prime rank of the original span. -/
theorem a5_nonnormal_span_action_odd_rank
    (h : HypothesisC28 κ H M L R V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ M ≤ normalizer (L : Set G))
    (K : Subgroup H) [K.Normal]
    (hne : coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H) ≠ ⊥)
    {p : ℕ} [Fact p.Prime] (ho : Odd p) :
    primeRank p (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) =
      primeRank p (conjugateSpanBy L M) := by
  let A := L.subgroupOf M
  let X := conjugateSpanBy A (⊤ : Subgroup M)
  let Y := conjugateSpanBy L M
  have hYM : Y ≤ M := conjugateSpanBy_le_self h.component_le
  have hYH : Y ≤ H := hYM.trans h.local_le
  have hmap : X.map M.subtype = Y := by
    change (conjugateSpanBy A ⊤).map M.subtype = Y
    rw [map_conjugateSpanBy, map_subgroupOf_eq_of_le h.component_le,
      ← MonoidHom.range_eq_map, range_subtype]
  have hM : IsSQTK κ M :=
    (IsSQTK.equiv (subgroupOfEquivOfLe h.local_le)).mp (h.sqtk.subgroup (M.subgroupOf H))
  have hQ : IsSQTK κ (M ⧸ pCore 2 M) := by
    refine ⟨?_,hM.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hM.stronglyQuasithin p hp ho)
  have hi : (normalizer (A : Set M)).index = 2 := by
    rcases Chapter1.Section02.proposition_1_2_1_three_orbit_source hQ h.component with hN | hi
    · let := hN
      apply (hn ?_).elim
      have hh := A.le_normalizer_map M.subtype
      simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype, A,
        map_subgroupOf_eq_of_le h.component_le] using hh
    · exact hi
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let ae := subgroupOfEquivOfLe h.component_le
  let : IsSimpleGroup (A ⧸ pCore 2 A) :=
    ((QuotientGroup.congr _ _ ae (pCore_map_iso 2 ae)).trans e).isSimpleGroup
  let j : H →* normalizer (K : Set H) :=
    { toFun := fun x => ⟨x, by rw [normalizer_eq_top]; exact mem_top x⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let f := (normalizerCoreCentralAction K).comp j
  have himage (U : Subgroup H) : U.map f = coreCentralActorImage K U := by
    apply le_antisymm
    · rintro x ⟨u,hu,rfl⟩
      exact mem_map_of_mem (normalizerCoreCentralAction K) (show j u ∈ U.subgroupOf _ from hu)
    · rintro x ⟨u,hu,rfl⟩
      exact ⟨(u : H), hu, rfl⟩
  let i := inclusion h.local_le
  have hiX : X.map i = Y.subgroupOf H := by
    apply map_injective H.subtype_injective
    rw [map_map, map_subgroupOf_eq_of_le hYH]
    exact hmap
  have hfinal : X.map (f.comp i) = coreCentralActorImage K (Y.subgroupOf H) := by
    rw [← map_map, hiX, himage]
  have hr := pair_span_action_odd_rank A h.component hi (f.comp i)
    (hfinal.symm ▸ hne) ho
  rw [hfinal] at hr
  have heq : primeRank p X = primeRank p Y := by
    rw [← hmap]
    exact primeRank_equiv p (X.equivMapOfInjective M.subtype M.subtype_injective)
  exact hr.trans heq

/-- Both A₅ factors survive in the literal action image at the prime five. -/
theorem two_le_a5_nonnormal_span_action_fiveRank
    (h : HypothesisC28 κ H M L R V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ M ≤ normalizer (L : Set G))
    (K : Subgroup H) [K.Normal]
    (hne : coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H) ≠ ⊥) :
    2 ≤ primeRank 5 (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  rw [h.a5_nonnormal_span_action_odd_rank e hn K hne (by decide : Odd 5)]
  exact h.two_le_span_fiveRank_of_a5_nonnormal e hn

/-- An action-image bound of one closes the original component-normality branch. -/
theorem normalizes_of_a5_component_action_fiveRank_le_one
    (h : HypothesisC28 κ H M L R V)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (K : Subgroup H) [K.Normal]
    (hne : coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H) ≠ ⊥)
    (hr : primeRank 5 (coreCentralActorImage K ((conjugateSpanBy L M).subgroupOf H)) ≤ 1) :
    M ≤ normalizer (L : Set G) := by
  by_contra hn
  have hh := h.two_le_a5_nonnormal_span_action_fiveRank e hn K hne
  omega

end CFSG.Quasithin.ChapterC.HypothesisC28
