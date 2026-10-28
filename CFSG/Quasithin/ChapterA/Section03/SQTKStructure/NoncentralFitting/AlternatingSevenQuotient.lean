module
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.EvenNormalQuotient
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.NoncentralFitting.TwoRank
public import Theory.SpecificGroups.SL2.OddOrderDivisibility
public import Theory.Alternating.PrimeRank
/-!
# A₇ quotients of SQTK C-components

The noncentral-Fitting alternative has two-rank one. If a surjective map
onto A₇ has an odd kernel, coprime rank transport excludes that alternative.
An even kernel instead makes the quotient PSL₂ over a prime field; its
order excludes A₇. Applying this to the original two-core quotient proves
that the head is quasisimple while retaining a possible central cubic cover.

Source: Aschbacher--Smith A.3.6 and 10.2.9, printed pp.43--45 and751.
-/
public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
private theorem not_prime_linear_two_seven {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ Nonempty (PSL(2, ZMod p) ≃* alternatingGroup (Fin 7)) := by
  let : Fact p.Prime := ⟨hp⟩
  rintro ⟨e⟩
  have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
    (F := ZMod p) (by simpa using hp.odd_of_ne_two (by omega))
  rw [Nat.card_congr e.toEquiv, Nat.card_zmod, nat_card_alternatingGroup] at hc
  norm_num at hc
  have hsub : p ^ 2 - 1 + 1 = p ^ 2 := Nat.sub_add_cancel (by nlinarith)
  by_cases hb : p ≤ 17
  · have hq : p ^ 2 - 1 ≤ 288 := by nlinarith
    have hh := Nat.mul_le_mul hb hq
    omega
  · have hq : 323 ≤ p ^ 2 - 1 := by nlinarith
    have hh := Nat.mul_le_mul (show 18 ≤ p by omega) hq
    omega

theorem quasisimple_of_alternating_seven_quotient
    {H : Type*} [Group H] [Finite H] {κ : GroupClass}
    (hH : IsSQTK κ H) (hO : pCore 2 H = ⊥)
    (hC : (⊤ : Subgroup H).IsCComponent)
    (f : H →* alternatingGroup (Fin 7)) (hf : Function.Surjective f) :
    IsQuasisimple H := by
  by_contra hnot
  have hrank : 2 ≤ primeRank 2 (alternatingGroup (Fin 7)) := by
    have hr := (GLS3.Chapter5.PRank.alternating_hasPRank_two 7).primeRank_eq Nat.prime_two
    simpa using hr.ge
  have hproper : f.ker ≠ ⊤ := by
    intro he
    obtain ⟨a,ha⟩ := exists_ne (1 : alternatingGroup (Fin 7))
    obtain ⟨x,rfl⟩ := hf a
    exact ha (MonoidHom.mem_ker.mp (he ▸ mem_top x))
  have heven : Even (Nat.card f.ker) := by
    by_contra he
    have hodd := Nat.not_even_iff_odd.mp he
    have heq := primeRank_eq_of_surjective_of_coprime 2 f hf hodd.coprime_two_left
    have hh : 2 ≤ primeRank 2 (⊤ : Subgroup H) := by
      rw [primeRank_equiv 2 (topEquiv : (⊤ : Subgroup H) ≃* H),heq]
      exact hrank
    let := quasisimple_of_two_le_two_rank hH hO hC hh
    exact hnot (IsQuasisimple.of_mulEquiv topEquiv)
  obtain ⟨_,p,hp,hp3,⟨ep⟩⟩ := intrinsic_even_normal_quotient hH hO hC hnot f.ker hproper heven
  exact not_prime_linear_two_seven hp hp3
    ⟨ep.symm.trans (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- A marked A7 quotient makes the original two-core head quasisimple.
The conclusion deliberately retains the possible central cubic cover. -/
theorem quasisimple_twoCore_of_alternating_seven_quotient
    {H : Type*} [Group H] [Finite H] {κ : GroupClass}
    (hH : IsSQTK κ H) (hC : (⊤ : Subgroup H).IsCComponent)
    (f : H →* alternatingGroup (Fin 7)) (hf : Function.Surjective f)
    (hker : pCore 2 H ≤ f.ker) : IsQuasisimple (H ⧸ pCore 2 H) := by
  let Q := H ⧸ pCore 2 H
  have hQ : IsSQTK κ Q := by
    refine ⟨?_,hH.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 H) pCore_isPGroup).trans
      (hH.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  have hbar : (⊤ : Subgroup Q).IsCComponent := by
    simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
      hC.map_quotient (pCore 2 H)
  let g := QuotientGroup.lift (pCore 2 H) f hker
  exact quasisimple_of_alternating_seven_quotient hQ (pCore_quotient_pCore_eq_bot 2)
    hbar g (QuotientGroup.lift_surjective_of_surjective _ f hf _)
end CFSG.Quasithin.ChapterA.Section03.NoncentralFitting
