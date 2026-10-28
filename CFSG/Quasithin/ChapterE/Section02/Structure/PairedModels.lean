module
public import CFSG.Quasithin.ChapterE.Section02.Structure.ComponentModels
public import CFSG.Quasithin.ChapterE.Section02.Structure.PairedComponents
public import Theory.SpecificGroups.Classical.PairedOddRank
public import Theory.SpecificGroups.PSL2.RootPrimeRank
public import Theory.SpecificGroups.PSL3.DefiningRank
public import Theory.SpecificGroups.SU3.OddDefiningRank
public import Theory.AtlasPort.ExceptionalIsomorphisms.SmallParameters
/-!
# The genuine paired-component model sieve in E.2.2

The original core-free minimal parabolic supplies a simple component and
an exchanged, commuting conjugate. Their direct product forces odd-prime
rank at most one in each factor. Apply the genuine reduced Theorem C list
to that same component through its faithful automizer. Explicit odd-rank
witnesses exclude binary PSU₃, higher-field PSL₃, symplectic groups and odd
PSL₃/PSU₃. The PSL₂ defining root forces prime field degree; PSL₃(2) is
transported through the actual exceptional PSL₂(7) equivalence.

Only binary PSL₂, Suzuki, odd-prime PSL₂ and the independent sporadic row
remain. The source endpoint constructs the rank and simple-component inputs;
it retains only the earlier universal Theorem C required by the catalogue.
Source: Aschbacher–Smith E.2.2, printed pp.215–216, and E.2.7, p.218.
-/

public section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterE.Structure.PairedModels
universe u
variable {G : Type u} [Group G] [Finite G]
open Theory.SpecificGroups.Classical.PairedOddRank

/-- Odd rank at most one forces the actual PSL₂ field to have prime order. -/
theorem odd_linear_two {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL G 2 (p^e))
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 1) :
    ClassicalGroup.IsPSL G 2 p := by
  obtain ⟨F,hF,hfin,hcard,⟨eF⟩⟩ := hm
  let : Fact p.Prime := ⟨hp⟩
  have hr := Theory.PSL2.root_prime_rank_ge F hcard
  change e ≤ primeRank p PSL(2,F) at hr
  have hle := hrank p hp ho
  rw [primeRank_equiv p eF] at hle
  have he0 : e ≠ 0 := by
    intro he
    have hc : Nat.card F = 1 := by simpa [he] using hcard
    exact zero_ne_one ((Nat.card_eq_one_iff_unique.mp hc).1.elim (0 : F) 1)
  have he : e = 1 := by omega
  exact ⟨F,hF,hfin,by simpa [he] using hcard,⟨eF⟩⟩

/-- The ordinary odd defining-prime root plane excludes PSL₃(p). -/
theorem not_odd_linear_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 1) :
    ¬ ClassicalGroup.IsPSL G 3 p := by
  rintro ⟨F,hF,hfin,hcard,⟨eF⟩⟩
  let : Fact p.Prime := ⟨hp⟩
  let : Fintype F := Fintype.ofFinite F
  let : CharP F p := charP_of_card_eq_prime_pow (p:=p) (f:=1)
    (by simpa only [pow_one,Nat.card_eq_fintype_card] using hcard)
  have hr := PSL3.DefiningRank.two_mul_fieldExponent_le_primeRank F
    (p:=p) (e:=1) (by simpa using hcard)
  have hle := hrank p hp ho
  rw [primeRank_equiv p eF] at hle
  omega

/-- The ordinary odd defining-prime elementary subgroup excludes PSU₃(p). -/
theorem not_odd_unitary_three {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 1) :
    ¬ ClassicalGroup.IsPSU G 3 p := by
  rintro ⟨F,hF,hfin,J,hcard,hconj,⟨eF⟩⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective eF eF.surjective
  let : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by intro h; subst p; norm_num at ho
  have hr := HermitianForm.OddDefiningRank.two_mul_fieldExponent_le_primeRank J
    (p:=p) (e:=1) hp2 (by decide) (by simpa using hcard) (by simpa using hconj)
  have hle := hrank p hp ho
  rw [primeRank_equiv p eF] at hle
  omega

/-- The two norm-one torus directions exclude every binary PSU₃ parameter. -/
theorem not_binary_unitary_three {n : ℕ} (hn : 0<n)
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 1) :
    ¬ ClassicalGroup.IsPSU G 3 (2^n) := by
  rintro ⟨F,hF,hfin,J,hcard,hconj,⟨eF⟩⟩
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_surjective eF eF.surjective
  obtain ⟨p,hp,ho,hr⟩ := unitary_binary_exists J hn hcard hconj
  have hle := hrank p hp ho
  rw [primeRank_equiv p eF] at hle
  omega

omit [Finite G] in
/-- The concrete exceptional equivalence identifies the degree-one binary row. -/
theorem psl_three_two_as_seven (hm : ClassicalGroup.IsPSL G 3 2) :
    ClassicalGroup.IsPSL G 2 7 := by
  obtain ⟨F,hF,hfin,hcard,⟨eF⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  let eField : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F (by decide)
    (by simpa only [Nat.card_eq_fintype_card] using hcard)).symm
  exact ⟨ZMod 7,inferInstance,inferInstance,by simp,
    ⟨(eF.trans (Atlas.fieldEquivPSL 3 eField)).trans
      Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.symm⟩⟩

/-- Prune the actual reduced Theorem C source list using the paired odd-rank bound. -/
theorem sieve
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 1)
    (hm : ChapterA.Section02.IsTheoremCOddModel G ∨
      ClassificationModels.IsBenderModel G ∨
      (∃ f : ℕ, 1 ≤ f ∧ ClassicalGroup.IsPSL G 3 (2^f)) ∨
      (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSp G 2 (2^f)) ∨
      Nonempty (G ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) ∨
      ChapterA.Section02.IsTheoremCSporadicModel G) :
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL G 2 (2^f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (G ≃* SuzukiMatrixGroup m)) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL G 2 p) ∨
    ChapterA.Section02.IsTheoremCSporadicModel G := by
  rcases hm with h | h | h | h | h | h
  · cases h with
    | linear_two p e hp ho he hm =>
      exact Or.inr (Or.inr (Or.inl ⟨p,hp,ho,odd_linear_two hp ho hm hrank⟩))
    | linear_three p hp ho hm => exact (not_odd_linear_three hp ho hrank hm).elim
    | unitary_three p hp ho hm => exact (not_odd_unitary_three hp ho hrank hm).elim
  · cases h with
    | linear f hf hm => exact Or.inl ⟨f,hf,hm⟩
    | unitary f hf hm => exact (not_binary_unitary_three (by omega) hrank hm).elim
    | suzuki m hm he => exact Or.inr (Or.inl ⟨m,hm,he⟩)
  · obtain ⟨f,hf,hm⟩ := h
    by_cases hf1 : f = 1
    · subst f
      exact Or.inr (Or.inr (Or.inl ⟨7,by decide,by decide,
        psl_three_two_as_seven (by simpa using hm)⟩))
    · obtain ⟨F,hF,hfin,hcard,⟨eF⟩⟩ := hm
      obtain ⟨p,hp,ho,hr⟩ := linear_binary_exists (by omega) hcard
      have hle := hrank p hp ho
      rw [primeRank_equiv p eF] at hle
      omega
  · obtain ⟨f,hf,F,hF,hfin,hcard,⟨eF⟩⟩ := h
    have hr := psp_binary_three_rank hcard
    rw [←primeRank_equiv 3 eF] at hr
    have hle := hrank 3 (by decide) (by decide)
    omega
  · obtain ⟨eF⟩ := h
    have hr := derived_psp_binary_three_rank
    rw [←primeRank_equiv 3 eF] at hr
    have hle := hrank 3 (by decide) (by decide)
    omega
  · exact Or.inr (Or.inr (Or.inr h))

variable {H : Type u} [Group H] [Finite H] {κ : GroupClass.{u}}

/-- The full paired source sieve on the original component, with rank and simplicity derived. -/
theorem source
    (hC : ∀ (G : Type u) [Group G] [Finite G], ChapterA.Section02.TheoremC κ G)
    (hH : IsSQTK κ H) (T : Sylow 2 H) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (hs : ¬ Group.IsSolvable H) (hJ : ChapterB.minimalParabolicCore T hP = ⊥)
    (K : Subgroup H) (hK : IsComponent H K)
    (hgen : K ⊔ (T : Subgroup H) = ⊤) (hn : ¬ K.Normal) :
    (∃ f : ℕ, 2 ≤ f ∧ ClassicalGroup.IsPSL K 2 (2^f)) ∨
    (∃ m : ℕ, 1 ≤ m ∧ Nonempty (K ≃* SuzukiMatrixGroup m)) ∨
    (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL K 2 p) ∨
    ChapterA.Section02.IsTheoremCSporadicModel K := by
  have hrad : solvableRadical H = ⊥ :=
    (ChapterB.minimalParabolic_nonsolvable_core_eq_radical T hP hs).symm.trans hJ
  let : IsSimpleGroup K := hK.isCComponent.isSimpleGroup_of_solvableRadical_eq_bot hrad
  rcases component_normal_or_pair hH.stronglyQuasithin T hK hgen with h | ⟨t,hne,_⟩
  · exact (hn h.1).elim
  · exact sieve (paired_component_odd_rank_le_one hH.stronglyQuasithin hrad hK hK.isCComponent t hne)
      (source_simple_component_models hC hH T hP K hK hgen)

end CFSG.Quasithin.ChapterE.Structure.PairedModels
