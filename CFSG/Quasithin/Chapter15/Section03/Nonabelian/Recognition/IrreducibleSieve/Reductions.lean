module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.Input

/-!
# Model-independent reductions in the irreducible sieve

The exact order of the original elementary actor supplies G.9.1 directly.
Irreducibility of the component join and the rank-two displacement prove
noncentrality, and hence select a component not centralized by that actor.
The three prime-to-three restrictions rule out actual elements of order three
in the relevant stabilizers. Degree arithmetic eliminates the small and odd
models and narrows the field parameters without identifying groups by labels.

These reductions do not assert the complete G.9.3 application or the terminal
contradiction. Source: Aschbacher–Smith, 15.3.58, printed p.1149.
-/

public section

namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve

open Subgroup Representation
open Representation.BinaryOffender
open CFSG.Quasithin.ChapterG.Section09
open scoped IsMulCommutative

variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
/-- A nonsolvable minimal normal subgroup is centerless. This uses genuine
minimal normality, independently of the classification of its components. -/
theorem ComponentData.center_eq_bot (hK : ComponentData ρ K) : center K = ⊥ := by
  let : K.Normal := hK.normal
  rcases hK.minimal ((center K).map K.subtype) inferInstance (map_subtype_le _) with hb | ht
  · exact (map_injective K.subtype_injective) (by simpa using hb)
  · have he : center K = ⊤ := (map_injective K.subtype_injective)
      (by simpa [← MonoidHom.range_eq_map] using ht)
    let : IsMulCommutative K := center_eq_top_iff.mp he
    exact (hK.nonsolvable inferInstance).elim

omit [Finite H] [FiniteDimensional (ZMod 2) W] in
/-- An actual component-action identification with a group having nontrivial
center contradicts minimal normality. In particular, a central cover must not
be silently replaced by its simple quotient in the model sieve. -/
theorem ComponentData.not_centerful_model (hK : ComponentData ρ K)
    {D M : Type*} [Group D] [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) D M) (hz : Nat.card (center D) ≠ 1) :
    ¬ Quasiequivalent (ρ.comp K.subtype) σ := by
  rintro ⟨e, _, _⟩
  apply hz
  rw [← Nat.card_congr (Subgroup.centerCongr e).toEquiv, hK.center_eq_bot, card_bot]

/-- G.9.1 uses the original actor `X`, whose rank is `s+1`. -/
theorem SourceData.setup (h : SourceData ρ X T v s) : Setup ρ X (s + 1) where
  faithful := h.faithful
  elementary := h.elementary
  card_actor := h.card_actor
  degree_le := by rw [h.dimension]

/-- Positive `s` gives the lower bound used before the final model sieve. -/
theorem SourceData.six_le_degree (h : SourceData ρ X T v s) :
    6 ≤ Module.finrank (ZMod 2) W := by
  have := h.dimension
  have := h.positive
  omega

/-- Both the small-degree alternatives, (3) and (11), are impossible. -/
theorem SourceData.degree_not_le_four (h : SourceData ρ X T v s) :
    ¬ Module.finrank (ZMod 2) W ≤ 4 := by
  have := h.six_le_degree
  omega

/-- Odd-degree alternatives are impossible, including the natural L₅ module,
the degree-eleven Mathieu modules, and the corrected component tensor. -/
theorem SourceData.degree_not_odd (h : SourceData ρ X T v s) :
    ¬ Odd (Module.finrank (ZMod 2) W) := by
  rintro ⟨n, hn⟩
  have := h.dimension
  omega

/-- The parity test applies to the action of any actual subgroup, so in
particular it does not identify the entire actor with the group in case (14). -/
theorem SourceData.not_odd_component_model (h : SourceData ρ X T v s)
    (J : Subgroup H) {D M : Type*} [Group D] [AddCommGroup M] [Module (ZMod 2) M]
    (σ : Representation (ZMod 2) D M) (hd : Odd (Module.finrank (ZMod 2) M)) :
    ¬ Quasiequivalent (ρ.comp J.subtype) σ := by
  rintro ⟨_, f, _⟩
  apply h.degree_not_odd
  rwa [f.finrank_eq]

/-- Rank two cannot be a nonzero invariant subspace of this irreducible
component action of degree at least six. -/
theorem SourceData.componentJoin_noncentral
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K) :
    ⁅K, zpowers v⁆ ≠ ⊥ := by
  let : Representation.IsIrreducible (ρ.comp K.subtype) := hK.irreducible
  apply Representation.commutator_zpowers_ne_bot_of_small_displacement ρ K v
  · intro J hJ
    have hn : J ≠ ⊥ := ((Subrepresentation.irreducible_iff_isAtom J).mp hJ).ne_bot
    have he : J = ⊤ := hK.irreducible.eq_bot_or_eq_top J |>.resolve_left hn
    rw [he]
    change Module.finrank (ZMod 2) (displacement ρ v) <
      Module.finrank (ZMod 2) (⊤ : Submodule (ZMod 2) W)
    rw [h.displacement_rank, finrank_top]
    have := h.six_le_degree
    omega
  · change 0 < Module.finrank (ZMod 2) (displacement ρ v)
    rw [h.displacement_rank]
    decide

/-- The whole component join fails to centralize the original elementary
actor, using the actual membership of its marked involution. -/
theorem SourceData.actor_noncentral
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K) : ⁅K, X⁆ ≠ ⊥ := by
  intro he
  apply h.componentJoin_noncentral hK
  exact le_bot_iff.mp (he ▸ commutator_mono le_rfl (zpowers_le.mpr h.marked_mem))

/-- At least one of the actual components satisfies the noncentrality
hypothesis in G.9.3. No assertion about component module equivalence is hidden
in this selection. -/
theorem SourceData.exists_noncentral_component
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K) :
    ∃ L : Subgroup H, Theory.GroupTheory.IsComponent H L ∧
      IsSimpleGroup L ∧ ¬ IsMulCommutative L ∧ L ≤ K ∧ ⁅L, X⁆ ≠ ⊥ := by
  obtain ⟨L, hL, hsL, hnL, he | ⟨L₂, hL₂, hsL₂, hnL₂, _, _, he⟩⟩ := hK.factors
  · exact ⟨L, hL, hsL, hnL, he.symm.le, he ▸ h.actor_noncentral hK⟩
  · by_cases hc : ⁅L, X⁆ = ⊥
    · refine ⟨L₂, hL₂, hsL₂, hnL₂, he ▸ le_sup_right, ?_⟩
      intro hc₂
      apply h.actor_noncentral hK
      apply commutator_eq_bot_iff_le_centralizer.mpr
      rw [he]
      exact sup_le (commutator_eq_bot_iff_le_centralizer.mp hc)
        (commutator_eq_bot_iff_le_centralizer.mp hc₂)
    · exact ⟨L, hL, hsL, hnL, he ▸ le_sup_left, hc⟩

omit [Finite H] in
private theorem no_three_element (J : Subgroup H) (hJ : Nat.Coprime 3 (Nat.card J))
    (a : H) (ha : orderOf a = 3) (hm : a ∈ J) : False := by
  exact (Nat.prime_three.coprime_iff_not_dvd.mp hJ)
    (ha ▸ J.orderOf_dvd_natCard hm)

/-- An actual cubic element stabilizing the displacement plane contradicts
the first of the source's three restrictions. -/
theorem SourceData.no_cubic_plane_stabilizer (h : SourceData ρ X T v s)
    (a : H) (ha : orderOf a = 3)
    (hD : ∀ w, ρ a w ∈ displacement ρ v ↔ w ∈ displacement ρ v) : False :=
  no_three_element _ h.plane_three_free a ha hD

/-- For a finite actor it suffices to show forward preservation of the plane. -/
theorem SourceData.no_cubic_plane_preserver (h : SourceData ρ X T v s)
    (a : H) (ha : orderOf a = 3)
    (hD : ∀ w ∈ displacement ρ v, ρ a w ∈ displacement ρ v) : False := by
  apply h.no_cubic_plane_stabilizer a ha
  intro w
  refine ⟨?_, hD w⟩
  intro hw
  have hw' := hD _ (hD _ hw)
  have hp : a ^ 3 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have he : ρ a (ρ a (ρ a w)) = w := by
    simpa [pow_succ, map_mul, Module.End.mul_apply] using
      congrArg (fun g => ρ g w) hp
  rwa [he] at hw'

/-- An actual cubic element fixing the Sylow fixed line pointwise contradicts
the source centralizer condition. -/
theorem SourceData.no_cubic_line_fixer (h : SourceData ρ X T v s)
    (a : H) (ha : orderOf a = 3)
    (hF : ∀ w ∈ sylowFixedSpace ρ T, ρ a w = w) : False :=
  no_three_element _ h.line_three_free a ha ⟨mem_top a, hF⟩

/-- A cubic element centralizing the actual `V*` is forbidden. -/
theorem SourceData.no_cubic_centralizer (h : SourceData ρ X T v s)
    (a : H) (ha : orderOf a = 3)
    (hC : a ∈ Subgroup.centralizer (zpowers v : Set H)) : False :=
  no_three_element _ h.centralizer_three_free a ha hC

/-- Once the involution calculation gives `n ≤ 2`, both rank-one families
have degree at most four and are excluded. -/
theorem SourceData.not_rank_one_small_field (h : SourceData ρ X T v s)
    {n : ℕ} (hn : n ≤ 2) (hd : Module.finrank (ZMod 2) W = 2 * n) : False := by
  have := h.six_le_degree
  omega

/-- The remaining natural SL₃ field would have order four. -/
theorem SourceData.linear_three_parameters (h : SourceData ρ X T v s)
    {n : ℕ} (hn : n ≤ 2) (hd : Module.finrank (ZMod 2) W = 3 * n) :
    n = 2 ∧ s = 1 := by
  have := h.six_le_degree
  have := h.dimension
  omega

/-- The remaining natural Sp₄ field would also have order four. -/
theorem SourceData.symplectic_four_parameters (h : SourceData ρ X T v s)
    {n : ℕ} (hn : n ≤ 2) (hd : Module.finrank (ZMod 2) W = 4 * n) :
    n = 2 ∧ s = 2 := by
  have := h.six_le_degree
  have := h.dimension
  omega

/-- Both small-field G₂ possibilities are retained, including G₂(2)′. -/
theorem SourceData.g2_parameters (h : SourceData ρ X T v s)
    {n : ℕ} (hn : n ≤ 2) (hd : Module.finrank (ZMod 2) W = 6 * n) :
    (n = 1 ∧ s = 1) ∨ (n = 2 ∧ s = 4) := by
  have := h.six_le_degree
  have := h.dimension
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
