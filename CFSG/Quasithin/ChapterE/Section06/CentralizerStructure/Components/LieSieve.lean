module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.ExceptionalFour
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent

/-!
# The component action setup for the E.6.8 Lie sieve

Restrict the Sylow subgroup of C_G(U) along the component's subnormal
chain. An element centralizing that Sylow subgroup normalizes each component:
otherwise distinct conjugate components commute, forcing the component's Sylow
two-subgroup into its center. The simple central quotient has even order by the
odd-order theorem, contradicting that containment. In particular this argument
retains central covers, and gives the actual embedded Sylow subgroup on which
V acts trivially.

These are common preliminary results, not the characteristic-two alternative
sieve. The source explicitly sends the exceptional L2(4) case to E.6.8(5),
regarding it as L2(5), on printed p.248. `LieTypeComponent` includes L2(4), so
that case must be accounted for when assembling a sieve from that predicate.
`ExceptionalFour` supplies its actual prime-five model and the bound of two
on its action corank. Positivity gives the two possible coranks below. The
parabolic classification and full exceptional alternative remain required.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem sylow_not_le_center {X : Type*} [Group X] [Finite X]
    [IsQuasisimple X] (S : Sylow 2 X) : ¬ (S : Subgroup X) ≤ center X := by
  intro hle
  let _ : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let q := QuotientGroup.mk' (center X)
  let R := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hdiv : 2 ∣ Nat.card (X ⧸ center X) :=
    Chapter1.Section02.IndexTwo.two_dvd_card_of_not_isSolvable
      (Group.IsPerfect.not_isSolvable _)
  apply R.ne_bot_of_dvd_card hdiv
  change (S : Subgroup X).map q = ⊥
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  exact hle

private theorem component_normalized_of_centralizes_sylow
    (hL : IsComponent G L) (S : Sylow 2 G) {v : G}
    (hv : ∀ s : S, Commute v (s : G)) : v ∈ normalizer (L : Set G) := by
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra hne
  have hc := hL.commutator_eq_bot_of_ne (hL.map_conj v) (Ne.symm hne)
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.1
  let _ := hL.2
  apply sylow_not_le_center R
  intro x hx
  have hxS : (x : G) ∈ (S : Subgroup G) := by
    have hx' : x ∈ (S : Subgroup G).subgroupOf L := hR ▸ hx
    exact hx'
  have hfix : MulAut.conj v (x : G) = x := by
    change v * (x : G) * v⁻¹ = x
    rw [(hv ⟨x, hxS⟩).eq]
    simp
  have hxconj : (x : G) ∈ L.map (MulAut.conj v).toMonoidHom :=
    hfix ▸ mem_map_of_mem (MulAut.conj v).toMonoidHom x.property
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact ((commutator_eq_bot_iff_le_centralizer.mp hc y.property) x hxconj).symm

/-- The actual Sylow two-subgroup of L whose ambient image is L ∩ Q. -/
theorem component_sylow_intersection (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype =
      L ⊓ sylowCentralizer (T : Subgroup G) V := by
  obtain ⟨S, hS⟩ := h.sylow_obstruction hU
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal
    (L.subgroupOf (centralizer (U : Set G))) hL.2.1
  let e := subgroupOfEquivOfLe hL.1
  refine ⟨R.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change ((R : Subgroup (L.subgroupOf (centralizer (U : Set G)))).map
    e.toMonoidHom).map L.subtype = _
  rw [hR, ← hS]
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨z.property, ⟨z.val, hz, rfl⟩⟩
  · rintro ⟨hx, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨y, hx⟩, ⟨⟨y, hx⟩, hy, rfl⟩, rfl⟩

/-- Centrality in the local Sylow group forces V to preserve each component,
including components with nontrivial center. -/
theorem component_normalized_by_V (h : HypothesisE61 K T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    V ≤ normalizer (L : Set G) := by
  let _ := h.elementary
  obtain ⟨S, hS⟩ := h.sylow_obstruction hU
  have hVH : V ≤ centralizer (U : Set G) :=
    V.le_centralizer.trans (Subgroup.centralizer_le hU.1)
  intro v hv
  have hn := component_normalized_of_centralizes_sylow hL.2 S
    (v := ⟨v, hVH hv⟩) (by
      intro s
      apply Commute.symm
      change s.val * ⟨v, hVH hv⟩ = ⟨v, hVH hv⟩ * s.val
      apply Subtype.ext
      have hs : (s.val.val) ∈ sylowCentralizer (T : Subgroup G) V :=
        hS ▸ mem_map_of_mem _ s.property
      exact ((mem_centralizer_iff.mp hs.2) v hv).symm)
  apply mem_normalizer_iff_map_conj_eq.mpr
  have he := congrArg (Subgroup.map (centralizer (U : Set G)).subtype)
    (mem_normalizer_iff_map_conj_eq.mp hn)
  rw [map_subgroupOf_eq_of_le hL.1] at he
  calc
    L.map (MulAut.conj v).toMonoidHom =
        ((L.subgroupOf (centralizer (U : Set G))).map
          (MulAut.conj (⟨v, hVH hv⟩ : centralizer (U : Set G))).toMonoidHom).map
            (centralizer (U : Set G)).subtype := by
      ext x
      constructor
      · rintro ⟨l, hl, rfl⟩
        exact ⟨MulAut.conj (⟨v, hVH hv⟩ : centralizer (U : Set G)) ⟨l, hL.1 hl⟩,
          ⟨⟨l, hL.1 hl⟩, hl, rfl⟩, rfl⟩
      · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
        exact ⟨b.val, hb, rfl⟩
    _ = L := he

/-- The Sylow witness used by action consumers, with the actual ambient image
and pointwise conjugation identity. The named Q is the source C_T(V). -/
theorem component_sylow_action (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {Q : Subgroup G} (hQ : Q = sylowCentralizer (T : Subgroup G) V) :
    V ≤ normalizer (L : Set G) ∧
      ∃ R : Sylow 2 L, (R : Subgroup L).map L.subtype = L ⊓ Q ∧
        ∀ v ∈ V, ∀ x : R, v * ((x : L) : G) * v⁻¹ = ((x : L) : G) := by
  refine ⟨component_normalized_by_V h hU hL, ?_⟩
  obtain ⟨R, hR⟩ := component_sylow_intersection h hU hL
  refine ⟨R, by simpa only [hQ] using hR, ?_⟩
  intro v hv x
  have hx : ((x : L) : G) ∈ L ⊓ sylowCentralizer (T : Subgroup G) V :=
    hR ▸ mem_map_of_mem L.subtype x.property
  rw [(mem_centralizer_iff.mp hx.2.2) v hv]
  simp

/-- In the overlapping PSL₂(4) model, the genuine component action has
corank at most two. The witness is the actual L ∩ C_T(V). -/
theorem component_four_actionCorank_le_two (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) : actionCorank V L ≤ 2 := by
  obtain ⟨hN, S, _, hfix⟩ := component_sylow_action h hU hL rfl
  exact LieSieve.actionCorank_le_two hm hN S hfix

/-- Escape from M makes the exceptional action nontrivial. Distinguishing
these two cases, and proving the fixed-space identity in the odd case,
are separate from the exceptional group comparison. -/
theorem component_four_actionCorank_cases (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    (hm : ClassicalGroup.IsPSL L 2 4) :
    actionCorank V L = 1 ∨ actionCorank V L = 2 := by
  have hpos : 0 < actionCorank V L :=
    fixedSpace_corank_pos h (component_not_le h earlier hU hL)
  have hbound := component_four_actionCorank_le_two h hU hL hm
  omega

end CFSG.Quasithin.ChapterE.Section06.Components
