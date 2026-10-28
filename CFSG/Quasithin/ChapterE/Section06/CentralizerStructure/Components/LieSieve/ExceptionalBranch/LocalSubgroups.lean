module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve
public import Theory.SpecificGroups.AlternatingFiveSolvableSylow
public import Theory.SpecificGroups.Alternating.FiveBorelOvergroups

/-!
# The local subgroup dichotomy for the exceptional PSL₂(4) component

The actual intersection L ∩ M is proper and contains the Sylow subgroup
L ∩ C_T(V). Transport to A₅ puts it inside the normalizer of that four-group.
The normalizer is an A₄ point stabilizer of order twelve, so there is no
intermediate subgroup between the four-group and its normalizer.

The center of L is trivial. Consequently the full-normalizer case gives
exactly the Borel preimage in L/Z(L), including the quotient map appearing
in the public specification. This proves only the local subgroup dichotomy;
the Borel action and the non-Borel fixed-kernel argument remain separate.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and the exceptional L₂(4) paragraph.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

omit [Finite G] in
private theorem alternating_equiv (hm : ClassicalGroup.IsPSL L 2 4) :
    Nonempty (L ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  obtain ⟨eA⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF
  exact ⟨e.trans eA⟩

private theorem proper_overgroup (e : L ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 L) (J : Subgroup L) (hJ : J ≠ ⊤) (hSJ : (S : Subgroup L) ≤ J) :
    J ≤ normalizer (S : Set L) := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  have hp : J.map e.toMonoidHom ≠ ⊤ := by
    intro he
    apply hJ
    apply (map_injective (f := e.toMonoidHom) e.injective)
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using he
  have hn := alternatingGroup.proper_sylow_overgroup_le_normalizer R
    (J.map e.toMonoidHom) hp (map_mono hSJ)
  change J.map e.toMonoidHom ≤ normalizer ((S : Subgroup L).map e.toMonoidHom : Set _) at hn
  rw [← map_equiv_normalizer_eq] at hn
  exact (map_le_map_iff_of_injective e.injective).mp hn

private theorem normalizer_card (e : L ≃* alternatingGroup (Fin 5)) (S : Sylow 2 L) :
    Nat.card (normalizer (S : Set L)) = 12 := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i, hi⟩ := Theory.SpecificGroups.Alternating.FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
  have hmap : (normalizer (S : Set L)).map e.toMonoidHom =
      MulAction.stabilizer (alternatingGroup (Fin 5)) i := by
    change (normalizer ((S : Subgroup L) : Set L)).map e.toMonoidHom = _
    rw [map_equiv_normalizer_eq]
    exact hi
  rw [← card_map_of_injective (K := normalizer (S : Set L)) (f := e.toMonoidHom) e.injective, hmap]
  have hc : ∀ i : Fin 5,
      Fintype.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
    decide +kernel
  rw [Nat.card_eq_fintype_card]
  exact hc i

private theorem overgroup_cases (e : L ≃* alternatingGroup (Fin 5))
    (S : Sylow 2 L) (J : Subgroup L) (hJ : J ≠ ⊤) (hSJ : (S : Subgroup L) ≤ J) :
    J = S ∨ J = normalizer (S : Set L) := by
  have hn := proper_overgroup e S J hJ hSJ
  have hSc := Theory.PSL2.SylowFixedQuotients.sylow_card_of_equiv_five e S
  have hNc := normalizer_card e S
  have hd4 : 4 ∣ Nat.card J := hSc ▸ card_dvd_of_le hSJ
  have hd12 : Nat.card J ∣ 12 := hNc ▸ card_dvd_of_le hn
  have hc : Nat.card J = 4 ∨ Nat.card J = 12 := by
    have hp := Nat.card_pos (α := J)
    have hb := Nat.le_of_dvd (by decide : 0 < 12) hd12
    interval_cases n : Nat.card J <;> omega
  rcases hc with hc | hc
  · exact Or.inl (eq_of_le_of_card_ge hSJ (by rw [hc, hSc])).symm
  · exact Or.inr (eq_of_le_of_card_ge hn (by rw [hc, hNc]))

omit [Finite G] in
private theorem center_eq_bot (e : L ≃* alternatingGroup (Fin 5)) : center L = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have he : e x ∈ center (alternatingGroup (Fin 5)) := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨a, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (mem_center_iff.mp hx a)
  rw [alternatingGroup.center_eq_bot (by simp)] at he
  exact mem_bot.mpr (e.injective ((mem_bot.mp he).trans (map_one e).symm))

private theorem borelPreimage_of_normalizer (hc : center L = ⊥)
    (S : Sylow 2 L) (hB : (L ⊓ M).subgroupOf L = normalizer (S : Set L)) :
    BorelPreimage L (L ⊓ M) := by
  let q := QuotientGroup.mk' (center L)
  have hq : Function.Bijective q := by
    refine ⟨(MonoidHom.ker_eq_bot_iff q).mp ?_, QuotientGroup.mk'_surjective _⟩
    rw [QuotientGroup.ker_mk', hc]
  let R := S.mapSurjective (f := q) hq.2
  refine ⟨inf_le_left, R, ?_⟩
  change (L ⊓ M).subgroupOf L =
    (normalizer ((S : Subgroup L).map q : Set _)).comap q
  rw [← map_normalizer_eq_of_bijective _ hq, comap_map_eq_self_of_injective hq.1]
  exact hB

/-- A full Sylow normalizer in the actual component gives the prescribed
Borel preimage in its central quotient. -/
theorem borelPreimage_of_intersection_normalizer
    (hm : ClassicalGroup.IsPSL L 2 4) (S : Sylow 2 L)
    (hB : (L ⊓ M).subgroupOf L = normalizer (S : Set L)) :
    BorelPreimage L (L ⊓ M) := by
  obtain ⟨e⟩ := alternating_equiv hm
  exact borelPreimage_of_normalizer (center_eq_bot e) S hB

/-- The actual intersection with M is either the Sylow four-group or its
full normalizer. All subgroups are inside the given component L. -/
theorem intersection_cases (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype =
      L ⊓ sylowCentralizer (T : Subgroup G) V) :
    (L ⊓ M).subgroupOf L = S ∨
      (L ⊓ M).subgroupOf L = normalizer (S : Set L) := by
  obtain ⟨e⟩ := alternating_equiv hm
  apply overgroup_cases e S
  · intro he
    apply component_not_le h earlier hU hL
    intro l hl
    have hh : (⟨l, hl⟩ : L) ∈ (L ⊓ M).subgroupOf L := by rw [he]; trivial
    exact hh.2
  · intro x hx
    have hxQ := hS ▸ mem_map_of_mem L.subtype hx
    exact ⟨x.property, h.sylow_le hxQ.2.1⟩

/-- The exceptional local subgroup alternatives, using the source Q and
retaining the literal quotient-normalizer definition of BorelPreimage. -/
theorem intersection_eq_sylow_or_borel (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) :
    L ⊓ M = L ⊓ sylowCentralizer (T : Subgroup G) V ∨
      BorelPreimage L (L ⊓ M) := by
  obtain ⟨S, hS⟩ := component_sylow_intersection h hU hL
  rcases intersection_cases h earlier hU hL hm S hS with hs | hn
  · left
    have he := congrArg (Subgroup.map L.subtype) hs
    rwa [map_subgroupOf_eq_of_le inf_le_left, hS] at he
  · right
    exact borelPreimage_of_intersection_normalizer hm S hn

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.ExceptionalBranch
