module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ComponentRecognitionSource
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ComponentRecognitionFinite
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Double.ComponentRecognitionLie
/-!
# Odd rank on the original double-linear component

The actual local block restricts to a full Sylow subgroup of the generated
component. The refined source catalogue, finite two-rank exclusions, and
marked Lie parabolics supply an odd prime dividing its field torus order
with rank at least two in that component. The final theorem applies this
result to K = L₂ ∨ L₂^(x⁻¹) inside X = K ∨ S₁, using only the original
source geometry. This supplies the rank input of
`LinearDouble.false_of_conjugate_generated_rank`; exact PSL₃ recognition
is unnecessary for that contradiction.

Source: Aschbacher–Smith 2.4.7, double-linear conclusion, printed p.541,
using the refined alternatives in 2.3.9(7).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.LinearShadows.Double
variable {G : Type*} [Group G] [Finite G]

/-- Restriction and transport retain the literal natural local block in the
actual containing component. -/
theorem local_natural_full_sylow_in_component
    {X K B L : Subgroup G} (hKX : K ≤ X) (hLK : L ≤ K)
    (P : Sylow 2 X) (hBP : B ≤ (P : Subgroup X).map X.subtype)
    (hlocal : L.subgroupOf X ∈ Chapter1.L X (B.subgroupOf X))
    (hK : IsComponent X (K.subgroupOf X))
    (hinter : K ⊓ (P : Subgroup X).map X.subtype ≤ B)
    {n : ℕ} (hn : ChapterC.IsL2EvenBlock L n) :
    ∃ Q : Sylow 2 K, L.subgroupOf K ∈ ChapterA.Section03.localCComponents Q ∧
      ChapterC.IsL2EvenBlock (L.subgroupOf K) n := by
  have hBPin : B.subgroupOf X ≤ P := by
    intro u hu
    obtain ⟨v,hv,he⟩ := hBP hu
    exact (Subtype.ext he : v=u) ▸ hv
  have hLKX : L.subgroupOf X ≤ K.subgroupOf X := subgroupOf_mono X hLK
  have hint : K.subgroupOf X ⊓ (P : Subgroup X) ≤ B.subgroupOf X := by
    intro u hu
    exact hinter ⟨hu.1,mem_map_of_mem _ hu.2⟩
  obtain ⟨Q,hQ,hLQ⟩ := local_full_sylow_of_intersection_le P
    (B.subgroupOf X) (L.subgroupOf X) (K.subgroupOf X) hBPin hlocal hLKX hK.1 hint
  let e := subgroupOfEquivOfLe hKX
  let Q' := Q.mapSurjective (f:=e.toMonoidHom) e.surjective
  have he : ((L.subgroupOf X).subgroupOf (K.subgroupOf X)).map e.toMonoidHom =
      L.subgroupOf K := by
    ext u
    constructor
    · rintro ⟨v,hv,rfl⟩
      exact hv
    · intro hu
      exact ⟨⟨⟨u,hKX u.property⟩,u.property⟩,hu,rfl⟩
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]
    infer_instance
  have hmap := Chapter1.Section02.localCComponents_map_of_solvable_ker hLQ e.toMonoidHom
  rw [he] at hmap
  exact ⟨Q',hmap,hn.of_mulEquiv (subgroupOfEquivOfLe hLK).symm⟩

/-- Every surviving refined row supplies an odd torus prime of rank two;
rows with insufficient two-rank are excluded by the actual natural module. -/
theorem odd_rank_of_refined_intersection
    {K M S : Subgroup G} {z : G} [IsQuasisimple K]
    (P : Sylow 2 K) (L : Subgroup K) {n : ℕ}
    (hlocal : L ∈ ChapterA.Section03.localCComponents P)
    (hn : ChapterC.IsL2EvenBlock L n)
    (hmodel : ComponentRefinement.RefinedIntersection K M S z) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p K := by
  cases hmodel with
  | bender hm => exact (not_bender_of_local_natural_block P L hlocal hn hm).elim
  | case_b hm =>
    rcases hm with hs | ⟨m,hm,hpsl⟩ | h4 | h6
    · exact odd_rank_of_derived_symplectic_four hs P L hlocal hn
    · exact odd_rank_of_psl_three hm hpsl P L hlocal hn
    · exact odd_rank_of_psl_three_four_quotient L hn h4
    · obtain ⟨e⟩ := h6.2.2
      exact (not_small_alternating_quotient L hn (Or.inl rfl) e).elim
  | alternating hm =>
    obtain ⟨e,_⟩ := hm.2
    exact (not_small_alternating_quotient L hn (Or.inr rfl) e).elim
  | linear_three hm _ =>
    obtain ⟨e⟩ := hm
    exact (not_psl_three_three L hn e).elim
  | linear_two p hp hm _ => exact (not_psl_two_fermatMersenne L hn hp hm).elim
  | sporadic hm =>
    apply odd_rank_of_mathieu L hn
    rcases hm with ⟨h,_⟩ | ⟨e,_⟩ | ⟨e,_⟩
    · exact .inl h
    · exact .inr (.inl ⟨e⟩)
    · exact .inr (.inr ⟨e⟩)
  | case_g hm =>
    obtain ⟨e,_⟩ := hm
    exact odd_rank_of_psl_four_two L hn e

/-- The original Γ₀ source hypotheses discharge the whole component catalogue. -/
theorem odd_rank_of_source_component
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M X K B L J : Subgroup G}
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (hgamma : X ∈ gammaZero (Chapter1.He G) M)
    (hpair : (B,J) ∈ localPairsIn (Chapter1.He G) M X)
    (P : Sylow 2 X) (hBP : B ≤ (P : Subgroup X).map X.subtype)
    (hKX : K ≤ X) (hK : IsComponent X (K.subgroupOf X)) (hLK : L ≤ K)
    (hlocal : L.subgroupOf X ∈ Chapter1.L X (B.subgroupOf X))
    (hinter : K ⊓ (P : Subgroup X).map X.subtype ≤ B)
    {n : ℕ} (hn : ChapterC.IsL2EvenBlock L n) :
    ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p K := by
  let : IsQuasisimple (K.subgroupOf X) := hK.2
  let : IsQuasisimple K := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hKX)
  obtain ⟨Q,hQ,hnQ⟩ := local_natural_full_sylow_in_component hKX hLK P hBP hlocal hK hinter hn
  obtain ⟨z,hm⟩ := source_component_catalogue hG T hM hTM hunique hgamma hpair P hBP hKX hK
  rcases hm with hm | hm
  · exact odd_rank_of_refined_intersection Q (L.subgroupOf K) hQ hnQ hm
  · obtain ⟨e⟩ := hm
    exact odd_rank_of_mathieu_quotient (L.subgroupOf K) hnQ e

/-- The required odd-rank witness on the literal double-linear source carrier.
The input geometric statements have independent source producers; no abstract
component, known model, or field-identification hypothesis remains. -/
theorem source_pair_odd_rank
    {M M₀ : Subgroup G} (d : MinimalBlockSetup M) {n : ℕ}
    (c : DoubleLinearSourceSetup d M₀ n)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → (T : Subgroup G) ≤ N → N = M)
    (x : G) (B S₁ : Subgroup G) (hx : x ∈ S₁) (hBS : B ≤ S₁)
    (hindex : B.relIndex S₁ = 2) :
    let K := c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom
    let X := K ⊔ S₁
    twoCore X ≠ ⊥ → c.second ≤ centralizer (twoCore X : Set G) →
      (∃ P : Sylow 2 X, (P : Subgroup X).map X.subtype = S₁) →
      c.second.subgroupOf X ∈ Chapter1.L X (B.subgroupOf X) →
      (K.subgroupOf X).Normal → K ⊓ S₁ ≤ B →
      X ∈ gammaZero (Chapter1.He G) M →
      (B,c.second ⊔ B) ∈ localPairsIn (Chapter1.He G) M X →
      ∃ p, p.Prime ∧ Odd p ∧ p ∣ 2^n-1 ∧ 2≤primeRank p K := by
  dsimp only
  let K := c.second ⊔ c.second.map (MulAut.conj x⁻¹).toMonoidHom
  let X := K ⊔ S₁
  intro hcore hc hSylow hlocal hnormal hinter hgamma hpair
  have hK := source_pair_component_of_core_centralized d c hG x B S₁ hx hBS hindex
    hcore hc hSylow hlocal hnormal
  obtain ⟨P,hP⟩ := hSylow
  exact odd_rank_of_source_component hG T hM hTM hunique hgamma hpair P
    (hP.symm ▸ hBS) (show K≤X from le_sup_left) hK (show c.second≤K from le_sup_left)
    hlocal (hP.symm ▸ hinter) c.second_type
end CFSG.Quasithin.Chapter2.LinearShadows.Double
