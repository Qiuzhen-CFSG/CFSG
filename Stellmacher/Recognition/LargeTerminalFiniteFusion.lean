module

public import Stellmacher.Recognition.LargeTerminalTransferCharacter
public import Theory.GroupTheory.BinaryCharacterNormalizerFusion

/-!
# Central squares of the large terminal transfer candidates

At the Sylow endpoint 4096, a five-fixed local candidate has square in the
center of the first residual. The binary character kills every square,
so its exact restriction puts the candidate's square in the residual.
The square still centralizes the same order-five subgroup, whose fixed
subgroup in the residual is central.

This records a reduction for the ambient fusion problem following
Stellmacher (10.1)(b), `refs/latex/stellmacher-n-group.tex`. The center
has order two, but membership of the original square in that center does
not control its ambient conjugates or those of the candidate.

The character does respect conjugacy induced by the second local member:
that member normalizes both the core and the residual. The missing ambient
step is to treat conjugacies which have no such representative.

At order 4096 the known containments leave two possibilities for the full
centralizer core: the residual of order 512 or the local core of order
1024. The cardinal squeeze used at order 2048 does not identify it here.
-/

namespace Stellmacher.Recognition

open Later SectionsFiveToSeven CosetGraphContext SevenSix SectionNine Subgroup

universe u

/-- At the upper endpoint the full centralizer core can only be the
residual or the larger local core. The two containments do not choose
between these alternatives. -/
public theorem LargeTerminalContext.involution_centralizer_core_dichotomy
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ z : G, orderOf z = 2 ∧ zpowers z = omegaOneCenter (S : Subgroup G) ∧
      (twoCoreIn (centralizer ({z} : Set G)) = ctx.firstResidual ∨
        twoCoreIn (centralizer ({z} : Set G)) = twoCoreIn ctx.second) := by
  obtain ⟨z, hz, hgen, hlow, hhigh, _⟩ := ctx.involution_centralizer_core
  let J := twoCoreIn (centralizer ({z} : Set G))
  let Q := twoCoreIn ctx.second
  have hSP : (S : Subgroup G) ≤ ctx.second :=
    ctx.terminal.hypothesisTwo.fiveOne.P2_mem.1.2.1.1
  have hQS : Q ≤ (S : Subgroup G) := by
    rintro x ⟨q, hq, rfl⟩
    exact (pCore_isPGroup (p := 2) (G := ctx.second)).le_sylow_of_normal
      (S.subtype hSP) hq
  have hQcard : Nat.card Q = 1024 := by
    have h := ctx.local_character_core_card hS
    rw [Nat.card_congr (subgroupOfEquivOfLe hQS).toEquiv] at h
    exact h
  have hJlow : 512 ≤ Nat.card J := by
    have h := card_le_of_le hlow
    rwa [ctx.first_residual_structure.1] at h
  have hJdiv : Nat.card J ∣ 1024 := hQcard ▸ card_dvd_of_le hhigh
  obtain ⟨k, hk⟩ := hJdiv
  have hkpos : 0 < k := by nlinarith
  have hkle : k ≤ 2 := by nlinarith
  have hcard : Nat.card J = 512 ∨ Nat.card J = 1024 := by
    interval_cases k <;> omega
  refine ⟨z, hz, hgen, ?_⟩
  rcases hcard with hJ | hJ
  · exact Or.inl (eq_of_le_of_card_ge hlow
      (by rw [ctx.first_residual_structure.1]; exact hJ.le)).symm
  · exact Or.inr (eq_of_le_of_card_ge hhigh (by rw [hQcard]; exact hJ.ge))

private theorem second_normalizes_residual
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) :
    ctx.second ≤ normalizer (ctx.firstResidual : Set G) := by
  let K := (ctx.first ⊔ ctx.second : Subgroup G)
  let P := GAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
  let E := EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep
  have hE : E = twoResidualIn P := ctx.terminal.Γ.twoResidualAt_def _
  have hEP : E ≤ P := hE ▸ twoResidualIn_le P
  have hRP : twoCoreIn E ≤ P := (twoCoreIn_le E).trans hEP
  have hPN : P ≤ normalizer (twoCoreIn E : Set K) :=
    (normal_subgroupOf_iff_le_normalizer hRP).mp
      (twoCoreIn_normal_of_normal E P hEP (hE ▸ twoResidualIn_normal P))
  have hmap : P.map K.subtype = ctx.second :=
    (nine_two_ambient_setup
      (ctx.terminal.toSectionTenContext ctx.commuting ctx.length_three).toAmbientSectionNineContext).2.2.1
  rw [← hmap]
  exact (map_mono hPN).trans (le_normalizer_map K.subtype)

/-- The local character respects conjugacy inside the second local member
on elements of its core. This does not assert ambient fusion control. -/
public theorem LargeTerminalContext.local_character_eq_of_second_conjugation
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (χ : S →* Multiplicative (ZMod 2))
    (hχ : ∀ s : S, (s : G) ∈ twoCoreIn ctx.second →
      (χ s = 1 ↔ (s : G) ∈ ctx.firstResidual))
    (x y : S) (hx : (x : G) ∈ twoCoreIn ctx.second)
    (g : G) (hg : g ∈ ctx.second)
    (hxy : g * (x : G) * g⁻¹ = (y : G)) : χ y = χ x := by
  have hPQ : ctx.second ≤ normalizer (twoCoreIn ctx.second : Set G) := by
    have h := (pCore 2 ctx.second).le_normalizer_map ctx.second.subtype
    rwa [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] at h
  exact binary_character_eq_of_normalizer_conjugation (S : Subgroup G)
    (twoCoreIn ctx.second) ctx.firstResidual χ hχ x y hx g (hPQ hg)
    (second_normalizes_residual ctx hg) hxy

/-- A local transfer candidate can be chosen with its square in the
order-two residual center, retaining the actual five-subgroup and character. -/
public theorem LargeTerminalContext.exists_transfer_candidate_central_square
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ (χ : S →* Multiplicative (ZMod 2)) (x : S) (A : Subgroup G),
      Nat.card A = 5 ∧
      A ≤ (EAt ctx.terminal.Γ ctx.terminal.criticalPath.firstStep).map
        (ctx.first ⊔ ctx.second).subtype ∧
      (x : G) ∈ centralizer (A : Set G) ∧
      (x : G) ∈ twoCoreIn ctx.second ∧ χ x ≠ 1 ∧ x ^ 4 = 1 ∧
      (((x ^ 2) : S) : G) ∈ CenterAmbient ctx.firstResidual ∧
      ∀ s : S, (s : G) ∈ twoCoreIn ctx.second →
        (χ s = 1 ↔ (s : G) ∈ ctx.firstResidual) := by
  obtain ⟨χ, x, A, hA, hAE, _, hxA, hxQ, hx4, hxχ, hχ, hfixed⟩ :=
    ctx.exists_local_transfer_candidate_fixed_center hS
  have hχsquare : χ (x ^ 2) = 1 := by
    rw [map_pow]
    have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
    simpa only [hc] using (pow_card_eq_one' (x := χ x))
  have hsquareQ : (((x ^ 2) : S) : G) ∈ twoCoreIn ctx.second :=
    (twoCoreIn ctx.second).pow_mem hxQ 2
  have hsquareR : (((x ^ 2) : S) : G) ∈ ctx.firstResidual :=
    (hχ (x ^ 2) hsquareQ).mp hχsquare
  have hsquareA : (((x ^ 2) : S) : G) ∈ centralizer (A : Set G) :=
    (centralizer (A : Set G)).pow_mem hxA 2
  have hsquareZ : (((x ^ 2) : S) : G) ∈ CenterAmbient ctx.firstResidual :=
    mem_map.mpr ⟨⟨_, hsquareR⟩, hfixed hsquareA, rfl⟩
  exact ⟨χ, x, A, hA, hAE, hxA, hxQ, hxχ, hx4, hsquareZ, hχ⟩

/-- At order 4096 the candidate and its square satisfy the two required
character equations for conjugators in the second local member. -/
public theorem LargeTerminalContext.exists_transfer_candidate_second_fusion
    {G : Type u} [Group G] [Finite G] {S : Sylow 2 G}
    (ctx : LargeTerminalContext S) (hS : Nat.card S = 4096) :
    ∃ (χ : S →* Multiplicative (ZMod 2)) (x : S),
      χ x ≠ 1 ∧ x ^ 4 = 1 ∧
      (((x ^ 2) : S) : G) ∈ CenterAmbient ctx.firstResidual ∧
      (∀ (g : G), g ∈ ctx.second → ∀ y : S,
        g * (x : G) * g⁻¹ = (y : G) → χ y = χ x) ∧
      (∀ (g : G), g ∈ ctx.second → ∀ y : S,
        g * (((x ^ 2) : S) : G) * g⁻¹ = (y : G) → χ y = 1) := by
  obtain ⟨χ, x, _, _, _, _, hxQ, hxχ, hx4, hsquareZ, hχ⟩ :=
    ctx.exists_transfer_candidate_central_square hS
  refine ⟨χ, x, hxχ, hx4, hsquareZ, ?_, ?_⟩
  · intro g hg y hxy
    exact ctx.local_character_eq_of_second_conjugation χ hχ x y hxQ g hg hxy
  · intro g hg y hxy
    have hsquareQ : (((x ^ 2) : S) : G) ∈ twoCoreIn ctx.second :=
      (twoCoreIn ctx.second).pow_mem hxQ 2
    rw [ctx.local_character_eq_of_second_conjugation χ hχ (x ^ 2) y
      hsquareQ g hg hxy, map_pow]
    have hc : Nat.card (Multiplicative (ZMod 2)) = 2 := by simp
    simpa only [hc] using (pow_card_eq_one' (x := χ x))

end Stellmacher.Recognition
