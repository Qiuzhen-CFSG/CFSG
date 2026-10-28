module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.SplitBranch.G64Natural
public import Theory.SpecificGroups.BinaryLinear.ThreePointQuotient
public import Theory.Representation.BinaryOffender.EquivariantStabilizer

/-!
# Excluding the larger central-transvection models

A prime-to-three line stabilizer rules out every central alternative of
G.6.4 except the natural binary two-space. The existing cubic-centralizer
obstructions exclude the symmetric models and dimensions four and five.
In dimension three the actual point stabilizer has an S₃ quotient, which
also contradicts the prime-to-three condition.

Source: Aschbacher–Smith, Lemma 15.3.52, printed p.1145.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
open Chapter13.Section08.TransvectionRecognition
open Chapter13.Section08.TransvectionRecognition.Component
open Chapter13.Section08.TransvectionRecognition.Component.RecognitionStep
open Recognition.SplitBranch.G64Natural
universe u
variable {A E : Type u} [Group A] [Finite A]
  [AddCommGroup E] [Module (ZMod 2) E] [Finite E]

omit [Finite A] [Finite E] in
theorem not_linear_three_of_line_three_prime
    (ρ : Representation (ZMod 2) A E) (P : Submodule (ZMod 2) E)
    (hP : Module.finrank (ZMod 2) P = 1)
    (hthree : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ P))) :
    ¬ HasActionModel ρ (linearRepresentation 3) := by
  rintro ⟨eA, eE, he⟩
  let P' := P.map eE.toLinearMap
  have hP' : Module.finrank (ZMod 2) P' = 1 := (eE.finrank_map_eq P).trans hP
  have hn : P' ≠ ⊥ := by
    intro hz
    have hh : Module.finrank (ZMod 2) P' = 0 := by rw [hz]; simp
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hn
  have hs : P' = Submodule.span (ZMod 2) {v} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hP' hv hv0
  have hmap := map_subspaceStabilizer_equivariant ρ (linearRepresentation 3) eA eE he P
  have hst : subspaceStabilizer (linearRepresentation 3) P' =
      MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) v := by
    rw [BinaryLinear.PointStabilizerRank.stabilizer_eq_parabolic, ← hs]
    rfl
  have hcard : Nat.card (subspaceStabilizer ρ P) =
      Nat.card (MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) v) := by
    rw [← hst, ← hmap]
    exact (card_map_of_injective eA.injective).symm
  obtain ⟨e⟩ := BinaryLinear.PointStabilizerRank.three_point_quotient (by simp) v hv0
  have hquot : Nat.card (MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) v ⧸
      pCore 2 (MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) v)) = 6 := by
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hd : 3 ∣ Nat.card (MulAction.stabilizer (BinaryLinear.GL (Fin 3 → ZMod 2)) v) := by
    apply dvd_trans (by decide : 3 ∣ 6)
    rw [← hquot]
    exact card_quotient_dvd_card _
  exact Nat.prime_three.coprime_iff_not_dvd.mp hthree (hcard.symm ▸ hd)

theorem finrank_eq_two_of_central_alternative
    (ρ : Representation (ZMod 2) A E) (hρ : Function.Injective ρ)
    (t : A) (ht : IsTransvection ρ t)
    (hthree : Nat.Coprime 3 (Nat.card (subspaceStabilizer ρ
      (LinearMap.range (ρ t - LinearMap.id)))))
    (hmodels : G64CentralAlternative ρ) : Module.finrank (ZMod 2) E = 2 := by
  have hno : ∀ c ∈ commutator A, orderOf c = 3 → ¬ Commute c t :=
    fun c _ hc => no_cubic_centralizer_of_plane ρ t hthree c hc
  obtain ⟨n, hn, hn', hm⟩ :=
    PermutationSieve.linear_of_central_alternative ρ hρ t ht hno hmodels
  have hd : Module.finrank (ZMod 2) E = n := by
    obtain ⟨_, e, _⟩ := hm
    simpa using e.finrank_eq
  by_cases h2 : n = 2
  · exact hd.trans h2
  have hn3 : 3 ≤ Module.finrank (ZMod 2) E := by omega
  have hm3 := (LinearSieve.linear_model_eq_three ρ t
    (transvection_displacement_rank ht) hn3 hno hn hn' hm).2
  exact (not_linear_three_of_line_three_prime ρ _
    (transvection_displacement_rank ht) hthree hm3).elim

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.AbelianExclusion
