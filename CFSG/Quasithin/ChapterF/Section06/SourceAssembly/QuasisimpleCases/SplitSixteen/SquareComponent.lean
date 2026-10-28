module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.ComponentModels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleCases.SplitSixteen.PrimeExclusion

/-!
# The actual square-field component in the split-sixteen branch

The complete source sieve supplies the odd PSL2 component with field degree
at most two. The genuine prime-extension theorem excludes degree one, so
the component is PSL2(p²). Its projected Sylow profile has order eight;
the order formula gives p congruent to three or five modulo eight.
The alternating triple covers and A7 retain their concrete carriers.

Source: Aschbacher--Smith F.6.18(8)--(9), printed p.310. This component
reduction precedes the separate ambient outer-action classification.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.SourceAssembly

private theorem psl_model_on_central_quotient
    {L : Type*} [Group L] {q : ℕ} (hm : ClassicalGroup.IsPSL L 2 q) :
    ClassicalGroup.IsPSL (L ⧸ center L) 2 q := by
  obtain ⟨F, _, _, hF, ⟨j⟩⟩ := hm
  have hz : center L = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hj := (Subgroup.centerCongr j ⟨x, hx⟩).property
    change j x ∈ center PSL(2,F) at hj
    rw [GorensteinWalter.psl2_center_eq_bot F, mem_bot] at hj
    exact j.injective (hj.trans (map_one j).symm)
  exact ⟨F, inferInstance, inferInstance, hF,
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).trans j⟩⟩

/-- The field-square congruence comes from the original Sylow section. -/
theorem square_psl_component_congruence_of_split_sixteen
    {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4))
    (K : Subgroup G) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 (p ^ 2)) : p % 8 = 3 ∨ p % 8 = 5 := by
  let P : Sylow 2 (K ⧸ center K) := default
  have hq : GorensteinWalter.IsOddPrimePower (p ^ 2) :=
    ⟨p, 2, hp, ho, by decide, rfl⟩
  rcases ComponentSieve.odd_pslTwo_central_quotient_profile T eT K hq
    (psl_model_on_central_quotient hm) P with ⟨_, hm8⟩ | ⟨_, hm16⟩
  · have he := degree_one_of_small_degree_nonsquare_mod_eight (by decide : 2 ≤ 2) hm8
    omega
  · have hbound : p % 16 < 16 := Nat.mod_lt _ (by decide)
    interval_cases hmod : p % 16 <;> norm_num [Nat.pow_mod, hmod] at hm16 <;> omega

universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]
    {κ : GroupClass.{u}} {K : Subgroup G} [K.Normal]

/-- The final component list for the literal split-sixteen source extension. -/
theorem component_models_of_split_sixteen_refined
    (hA : ChapterA.Section02.TheoremA κ H)
    (hC : ChapterA.Section02.TheoremC κ (K ⧸ center K))
    (hH : IsSQTK κ H) (e : G ≃* (H ⧸ pPrimeCore 3 H))
    (hK : IsComponent G K) (hFstar : generalizedFitting G = K)
    (hquot : IsPGroup 2 (G ⧸ K)) (T : Sylow 2 G)
    (eT : T ≃* (Multiplicative (ZMod 2) × DihedralGroup 4)) :
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      ClassicalGroup.IsPSL K 2 (p ^ 2)) ∨
    Nonempty (K ≃* Atlas.Codes.HexEvenAutomorphisms) ∨
    Nonempty (K ≃* alternatingGroup (Fin 7)) ∨
    Nonempty (K ≃* GLS3.Chapter5.OddCentralCovers.TripleSeven) := by
  rcases component_models_of_split_sixteen hA hC hH e hK hFstar hquot T eT with
    hm | hm | hm | hm
  · obtain ⟨p, f, hp, ho, hf, hf2, hm⟩ := hm
    have he : f = 1 ∨ f = 2 := by omega
    rcases he with rfl | rfl
    · let : Fact p.Prime := ⟨hp⟩
      exact (not_prime_psl_component_of_split_sixteen T eT K hFstar hK ho
        (by simpa using hm)).elim
    · exact .inl ⟨p, hp, ho, square_psl_component_congruence_of_split_sixteen T eT K hp ho hm, hm⟩
  · exact .inr (.inl hm)
  · exact .inr (.inr (.inl hm))
  · exact .inr (.inr (.inr hm))

end CFSG.Quasithin.ChapterF.SourceAssembly
