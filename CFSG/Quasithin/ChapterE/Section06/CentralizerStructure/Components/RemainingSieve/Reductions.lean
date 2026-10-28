module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Basic
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.Models
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.Intersections
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.IndexTwo.SmallSylow
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived

/-!+# Reductions for the remaining component cases in E.6.8

Restriction along the component's subnormal chain supplies the actual Sylow
intersection. A subgroup centralizing that intersection must stabilize the
component: otherwise distinct commuting components would put its Sylow subgroup
in its center. The simple central quotient rules this out.

The six-letter polar isomorphism puts the A6 endpoint in characteristic two.
For the remaining models, centralizer generation yields an escaping hyperplane,
and residual centralization provides the obstruction used in the sporadic sieve.
The model-specific bounds, generation, kernel equality, and invariant subgroups
are separate obligations; these reductions do not assert the full E.6.8 sieve.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259).
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
open Chapter1.Section02.LocalModels
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

omit [Finite G] in
/-- The exceptional endpoint uses the concrete polar equivalence, including
the commutator of the projective symplectic carrier. -/
theorem lieType_of_alternating_six (hL : IsAlternating L 6) : LieTypeComponent L := by
  obtain ⟨e⟩ := hL
  exact Or.inr (Or.inl (.symplectic_derived ⟨e.trans
    Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix.symm⟩))

/-- The source Q meets the component in an actual Sylow two-subgroup. -/
theorem component_sylow_intersection (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    ∃ S : Sylow 2 L, (S : Subgroup L).map L.subtype =
      L ⊓ sylowCentralizer (T : Subgroup G) V := by
  obtain ⟨S, hS⟩ := Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
    (h.sylow_obstruction hU) hL.1 hL.2.1
  exact ⟨S, hS.trans (inf_comm _ _)⟩

private theorem sylow_not_le_center {X : Type*} [Group X] [Finite X]
    [IsQuasisimple X] (S : Sylow 2 X) : ¬ (S : Subgroup X) ≤ center X := by
  intro hc
  let _ : IsSimpleGroup (X ⧸ center X) := IsQuasisimple.simple
  let q := QuotientGroup.mk' (center X)
  let R := S.mapSurjective (QuotientGroup.mk'_surjective (center X))
  have hr : (R : Subgroup (X ⧸ center X)) = ⊥ := by
    change (S : Subgroup X).map q = ⊥
    apply (Subgroup.map_eq_bot_iff _).mpr
    simpa only [q, QuotientGroup.ker_mk'] using hc
  have hb := Chapter1.Section02.IndexTwo.two_lt_card_sylow_of_simple_perfect R
  change 2 < Nat.card ↥(R : Subgroup (X ⧸ center X)) at hb
  rw [hr] at hb
  simp at hb

private theorem centralizer_sylow_normalizes_component {X : Type*}
    [Group X] [Finite X] {D : Subgroup X} (hD : IsComponent X D)
    (S : Sylow 2 D) :
    centralizer ((S : Subgroup D).map D.subtype : Set X) ≤ normalizer (D : Set X) := by
  let _ := hD.2
  intro x hx
  apply mem_normalizer_iff_map_conj_eq.mpr
  by_contra he
  have hc := hD.commutator_eq_bot_of_ne (hD.map_equiv (MulAut.conj x))
    (Ne.symm he)
  have hsc : (S : Subgroup D).map D.subtype ≤ D.map (MulAut.conj x).toMonoidHom := by
    rintro s ⟨d, hd, rfl⟩
    refine ⟨d, d.property, ?_⟩
    have hh := mem_centralizer_iff.mp hx d (mem_map_of_mem D.subtype hd)
    change x * (d : X) * x⁻¹ = d
    rw [← hh, mul_inv_cancel_right]
  apply sylow_not_le_center S
  intro s hs
  apply mem_center_iff.mpr
  intro d
  apply Subtype.ext
  exact mem_centralizer_iff.mp
    ((commutator_eq_bot_iff_le_centralizer.mp (by rwa [commutator_comm] :
      ⁅D.map (MulAut.conj x).toMonoidHom, D⁆ = ⊥))
      (hsc (mem_map_of_mem D.subtype hs))) d d.property

/-- The actual V normalizes each component; no model classification is used. -/
theorem component_normalized (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    V ≤ normalizer (L : Set G) := by
  let _ := h.elementary
  let H := centralizer (U : Set G)
  let D := L.subgroupOf H
  obtain ⟨S, hS⟩ := h.sylow_obstruction hU
  obtain ⟨R, hR⟩ := S.exists_subgroupOf_eq_of_subnormal D hL.2.1
  have hn := centralizer_sylow_normalizes_component hL.2 R
  have hVH : V ≤ H := V.le_centralizer.trans (Subgroup.centralizer_le hU.1)
  intro v hv
  have hvc : (⟨v, hVH hv⟩ : H) ∈
      centralizer ((R : Subgroup D).map D.subtype : Set H) := by
    rintro s ⟨d, hd, rfl⟩
    have hdS : d.val ∈ (S : Subgroup H) := by
      rw [hR] at hd
      exact hd
    have hdQ : (d.val : G) ∈ sylowCentralizer (T : Subgroup G) V :=
      hS ▸ mem_map_of_mem H.subtype hdS
    apply Subtype.ext
    exact (mem_centralizer_iff.mp hdQ.2 v hv).symm
  have hm := le_normalizer_map H.subtype (mem_map_of_mem H.subtype (hn hvc))
  change v ∈ normalizer ((L.subgroupOf H).map H.subtype : Set G) at hm
  rwa [map_subgroupOf_eq_of_le hL.1] at hm

omit [Finite G] in
/-- A one-dimensional faithful action supplies its own escaping hyperplane. -/
theorem escape_of_actionCorank_one
    (hUV : U ≤ V) (hLH : L ≤ centralizer (U : Set G)) (hLM : ¬ L ≤ M)
    (hd : actionCorank V L = 1) :
    ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ subgroupCorank V A = 1 ∧
      ¬ L ⊓ centralizer (A : Set G) ≤ M := by
  refine ⟨V ⊓ centralizer (L : Set G), fixedSpace_contains hUV hLH,
    inf_le_left, hd, ?_⟩
  have hLC : L ≤ centralizer (V ⊓ centralizer (L : Set G) : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  exact fun hc => hLM ((le_inf le_rfl hLC).trans hc)

omit [Finite G] in
/-- Centralizer generation gives an escaping member of the hyperplane family.
The generation identity is a model-specific input, not asserted here. -/
theorem escape_of_hyperplane_generation (hLM : ¬ L ≤ M)
    (hgen : L ≤ ⨆ (A : Subgroup G) (_ : U ≤ A) (_ : A ≤ V)
      (_ : subgroupCorank V A = 1), L ⊓ centralizer (A : Set G)) :
    ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ subgroupCorank V A = 1 ∧
      ¬ L ⊓ centralizer (A : Set G) ≤ M := by
  by_contra! hn
  exact hLM (hgen.trans (iSup_le fun A => iSup_le fun hUA =>
    iSup_le fun hAV => iSup_le fun hd => hn A hUA hAV hd))

/-- The alternating alternative follows after its two intrinsic action facts
are proved. The escaping hyperplane and global rank are constructed here. -/
theorem alternating_of_action_facts (h : HypothesisE61 K T M V)
    (hUV : U ≤ V) (hLH : L ≤ centralizer (U : Set G)) (hLM : ¬ L ≤ M)
    (hmodel : IsAlternating L 7 ∨ IsAlternatingCover L 6 ∨ IsAlternatingCover L 7)
    (hd : actionCorank V L ≤ 2)
    (hgen : actionCorank V L = 2 →
      L ≤ ⨆ (A : Subgroup G) (_ : U ≤ A) (_ : A ≤ V)
        (_ : subgroupCorank V A = 1), L ⊓ centralizer (A : Set G)) :
    AlternatingAlternative M V U L := by
  have hp : 0 < actionCorank V L := fixedSpace_corank_pos h hLM
  have he : ∃ A : Subgroup G, U ≤ A ∧ A ≤ V ∧ subgroupCorank V A = 1 ∧
      ¬ L ⊓ centralizer (A : Set G) ≤ M := by
    by_cases h1 : actionCorank V L = 1
    · exact escape_of_actionCorank_one hUV hLH hLM h1
    · exact escape_of_hyperplane_generation hLM (hgen (by omega))
  refine ⟨hmodel, he, ?_, hd⟩
  obtain ⟨A, _, hAV, hdim, hescape⟩ := he
  exact globalR_eq_one_of_hyperplane h.normalizer_le hAV hdim
    (fun hc => hescape (inf_le_right.trans hc))

/-- Once the model bound is at most one, nontriviality makes the action
dimension and the global weak-closure parameter exactly one. This does not
identify U with the action kernel. -/
theorem rank_one_of_action_bound (h : HypothesisE61 K T M V)
    (hLM : ¬ L ≤ M) (hd : actionCorank V L ≤ 1) :
    actionCorank V L = 1 ∧ globalR V = 1 := by
  have hp : 0 < actionCorank V L := fixedSpace_corank_pos h hLM
  have he : actionCorank V L = 1 := by omega
  refine ⟨he, le_antisymm ?_ (one_le_globalR V)⟩
  have hb : globalR V ≤ (actionCorank V L : ℕ∞) := fixedSpace_globalR_le h hLM
  simpa only [he, Nat.cast_one] using hb

/-- The fixed-point-free residual witness in the sporadic argument is
incompatible with the residual condition defining Γ. Both residuals and
centralizers concern the actual embedded subgroups. -/
theorem residual_fixedSpace_obstruction (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hLH : L ≤ centralizer (U : Set G))
    (hLM : ¬ L ≤ M) {R : Subgroup G}
    (hR : R ≤ (primeToResidual 2 ↥(L ⊓ M)).map (L ⊓ M).subtype)
    (hfixed : V ⊓ centralizer (R : Set G) ≤ centralizer (L : Set G)) : False := by
  have hRV := hR.trans ((component_intersection_residual hU hLH).trans inf_le_right)
  have hVR := le_centralizer_iff.mpr hRV
  have hVL := (le_inf le_rfl hVR).trans hfixed
  exact hLM (((le_centralizer_iff.mpr hVL).trans
    (Subgroup.centralizer_le_normalizer _)).trans h.normalizer_le)

end CFSG.Quasithin.ChapterE.Section06.Components.RemainingSieve
