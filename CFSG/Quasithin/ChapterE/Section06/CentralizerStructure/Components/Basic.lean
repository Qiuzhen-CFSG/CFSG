module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Local
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Sylow
public import CFSG.Quasithin.ChapterE.Section06.Obstructions
public import Theory.GroupTheory.PGroup.CharacteristicCenterReduction

/-!
# Common component deductions in E.6.8

A component cannot lie in a subgroup whose generalized Fitting subgroup is its
two-core: restriction preserves subnormality and quasisimplicity, whereas a
component inside that core would be solvable. Applying E.6.6 gives both escape
from M and trivial intersection of C_V(L) with C_V(T). The fixed-space bounds
come directly from the genuine weak-closure parameter and subgroup indices.

A nontrivial fixed point of T on V supplies the central involution, and E.6.5–6
then construct every hypothesis of 1.1.5. The restriction of O^{2'}(C_M(U))
controls the actual embedded O^{2'}(L ∩ M). None of the classification or
model-action conclusions of E.6.8 is assumed or asserted here.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248 (PDF pp.258–259), and 1.1.5, printed pp.501–502.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

/-- An actual component of H, embedded in G; subnormality is relative to H. -/
def ComponentIn (H L : Subgroup G) : Prop :=
  L ≤ H ∧ IsComponent H (L.subgroupOf H)

/-- A nonidentity element of the source Z = C_V(T). -/
theorem exists_sylow_fixed (h : HypothesisE61 K T M V) :
    ∃ z ∈ sylowFixedSpace (T : Subgroup G) V, z ≠ 1 := by
  let _ := h.normal_in_sylow
  have hn : V.subgroupOf (T : Subgroup G) ≠ ⊥ := by
    intro he
    have hh := congrArg (Subgroup.map (T : Subgroup G).subtype) he
    rw [map_subgroupOf_eq_of_le h.le_sylow, Subgroup.map_bot] at hh
    exact h.nontrivial hh
  have hc := Subgroup.center_inf_ne_bot_of_normal T.isPGroup'
    (V.subgroupOf (T : Subgroup G)) hn
  obtain ⟨z, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  refine ⟨z.val, ⟨z.property.2, ?_⟩, fun he => hne (Subtype.ext (Subtype.ext he))⟩
  intro t ht
  exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp z.property.1) ⟨t, ht⟩)

private theorem component_not_le_charTwo {H B : Subgroup G}
    (hL : ComponentIn H L) (hBH : B ≤ H)
    (hg : generalizedFitting B = pCore 2 B) : ¬ L ≤ B := by
  intro hLB
  let e : L.subgroupOf H ≃* L.subgroupOf B :=
    (subgroupOfEquivOfLe hL.1).trans (subgroupOfEquivOfLe hLB).symm
  let _ := hL.2.2
  let _ := IsQuasisimple.of_mulEquiv e
  have hs : (L.subgroupOf B).IsSubnormal :=
    hL.2.1.comap (inclusion hBH)
  have hl := component_le_generalizedFitting B (L.subgroupOf B) ⟨hs, inferInstance⟩
  rw [hg] at hl
  have hp := (pCore_isPGroup (p := 2) (G := B)).to_le hl
  let _ := hp.isNilpotent
  let _ : IsSimpleGroup ((L.subgroupOf B) ⧸ center (L.subgroupOf B)) :=
    IsQuasisimple.simple
  let _ : Nontrivial (L.subgroupOf B) :=
    (QuotientGroup.mk'_surjective (center (L.subgroupOf B))).nontrivial
  exact Group.IsPerfect.not_isSolvable (L.subgroupOf B) inferInstance

/-- The first assertion of E.6.8, using only E.6.6(1). -/
theorem component_not_le
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) : ¬ L ≤ M :=
  fun hLM => component_not_le_charTwo hL inf_le_left (h.lemma_E_6_6_1 earlier hU)
    (le_inf hL.1 hLM)

/-- No nonidentity element of Z can centralize a component of C_G(U). -/
theorem component_fixedSpace_disjoint_sylowFixed
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L) :
    (V ⊓ centralizer (L : Set G)) ⊓ sylowFixedSpace (T : Subgroup G) V = ⊥ := by
  apply le_bot_iff.mp
  rintro z ⟨hzL, hzZ⟩
  apply mem_bot.mpr
  by_contra hne
  have hc := (h.lemma_E_6_6_3 earlier hU hzZ hne).1
  apply component_not_le_charTwo hL inf_le_left hc
  apply le_inf hL.1
  intro l hl
  exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hzL.2) l hl)

omit [Finite G] in
/-- U is fixed by every subgroup of C_G(U). -/
theorem fixedSpace_contains (hUV : U ≤ V)
    (hLH : L ≤ centralizer (U : Set G)) :
    U ≤ V ⊓ centralizer (L : Set G) :=
  le_inf hUV (le_centralizer_iff.mpr hLH)

/-- The upper dimension bound common to E.6.8(1) and (2). -/
theorem fixedSpace_corank_le (hUV : U ≤ V)
    (hLH : L ≤ centralizer (U : Set G)) :
    subgroupCorank V (V ⊓ centralizer (L : Set G)) ≤ subgroupCorank V U :=
  subgroupCorank_antitone (fixedSpace_contains hUV hLH)

/-- The lower bound in the displayed inequality (*) on printed p.247. -/
theorem fixedSpace_globalR_le (h : HypothesisE61 K T M V)
    (hLM : ¬ L ≤ M) :
    globalR V ≤ (subgroupCorank V (V ⊓ centralizer (L : Set G)) : ℕ∞) := by
  apply globalR_le_corank inf_le_left
  intro hc
  exact hLM ((le_centralizer_iff.mpr inf_le_right).trans (hc.trans h.normalizer_le))

/-- An escaping subgroup acts nontrivially on V. -/
theorem fixedSpace_corank_pos (h : HypothesisE61 K T M V)
    (hLM : ¬ L ≤ M) :
    0 < subgroupCorank V (V ⊓ centralizer (L : Set G)) := by
  have hh := (one_le_globalR V).trans (fixedSpace_globalR_le h hLM)
  have : 1 ≤ subgroupCorank V (V ⊓ centralizer (L : Set G)) := by exact_mod_cast hh
  omega

/-- The actual intersection L ∩ M normalizes V. -/
theorem component_intersection_normalizes (h : HypothesisE61 K T M V)
    (hU : U ∈ obstructionFamily M V) (hLH : L ≤ centralizer (U : Set G)) :
    L ⊓ M ≤ normalizer (V : Set G) :=
  (le_inf inf_le_right (inf_le_left.trans hLH)).trans
    (h.localCentralizer_le_normalizer hU.2.1 hU.1)

private theorem residual_map_le {A B : Type*} [Group A] [Group B]
    (f : A →* B) (p : ℕ) :
    (primeToResidual p A).map f ≤ primeToResidual p B := by
  apply le_sInf
  rintro N ⟨hN, hcop⟩
  let _ := hN
  rw [map_le_iff_le_comap]
  apply primeToResidual_le
  rw [index_comap]
  exact hcop.of_dvd_right (N.relIndex_dvd_index_of_normal f.range)

omit [Finite G] in
/-- O^{2' }(L ∩ M) centralizes V; the residual is computed inside L ∩ M. -/
theorem component_intersection_residual (hU : U ∈ obstructionFamily M V)
    (hLH : L ≤ centralizer (U : Set G)) :
    (primeToResidual 2 ↥(L ⊓ M)).map (L ⊓ M).subtype ≤
      L ⊓ centralizer (V : Set G) := by
  let f : ↥(L ⊓ M) →* ↥(M ⊓ centralizer (U : Set G)) :=
    inclusion (le_inf inf_le_right (inf_le_left.trans hLH))
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y.property.1,
    (hU.2.2.2 (mem_map_of_mem _ ((residual_map_le f 2) (mem_map_of_mem f hy)))).2⟩

/-- Construction of the exact 1.1.5 hypotheses used in E.6.8. -/
theorem chapterOne_inputs (h : HypothesisE61 K T M V)
    (earlier : EarlierLocalFacts T) (hU : U ∈ obstructionFamily M V)
    {z : G} (hz : z ∈ sylowFixedSpace (T : Subgroup G) V) (hne : z ≠ 1) :
    ∃ S : Sylow 2 (centralizer (U : Set G)),
      (S : Subgroup (centralizer (U : Set G))).map
        (centralizer (U : Set G)).subtype = sylowCentralizer (T : Subgroup G) V ∧
      Chapter1.Lemma115Hypotheses (centralizer (U : Set G)) S
        (centralizer ({z} : Set G)) z := by
  let _ := h.elementary
  have ho : orderOf z = 2 := by
    have hz2 : z ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian z hz.1
    have hd := orderOf_dvd_of_pow_eq_one hz2
    exact (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd |>.resolve_left
      (fun he => hne (orderOf_eq_one_iff.mp he))
  obtain ⟨S, hS⟩ := h.sylow_obstruction hU
  refine ⟨S, hS, ?_⟩
  have hUH : U ≤ centralizer (U : Set G) :=
    hU.1.trans (V.le_centralizer.trans (Subgroup.centralizer_le hU.1))
  have hcore : U ≤ (centralizer (U : Set G)).pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((IsElementaryAbelian.isPGroup 2 V).to_le hU.1)
      hUH (centralizer_le_normalizer _)
  refine ⟨?_, ?_, ?_, ho, ?_, ?_, le_rfl⟩
  · exact fun he => hU.2.1 (le_bot_iff.mp (he ▸ hcore))
  · refine ⟨Chapter1.mem_He_iff.mpr
      (h.centralizer_fixedPoint_characteristicTwo earlier hz hne),
      Chapter1.mem_H_of_isTwoLocal (isTwoLocal_involution_centralizer ho), ?_⟩
    rw [hS]
    intro q hq
    exact mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp hz.2) q hq.1)
  · exact (h.centralizer_fixedPoint_core_bound hU.1 hz.1).trans
      ((pCoreIn_le 2 _).trans inf_le_left)
  · rw [hS]
    exact h.le_sylowCentralizer hz.1
  · intro q hq
    rw [hS] at hq
    exact (mem_centralizer_iff.mp hz.2) q hq.1

end CFSG.Quasithin.ChapterE.Section06.Components
