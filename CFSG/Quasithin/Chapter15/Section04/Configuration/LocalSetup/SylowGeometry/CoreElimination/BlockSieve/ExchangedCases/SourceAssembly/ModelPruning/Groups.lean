module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.Models
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.Actions
public import Theory.Representation.QuadraticFourGroup.Recognition.FactorSpectrum
public import Theory.SpecificGroups.PSL2.OddAutomorphismRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.G2Even.TwoRank.Elementary
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.LinearThreeModels
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.BlockSieve.ExchangedCases.ExceptionalG2
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.IrreducibleCohomology.SymplecticTwo.PolarComparison
/-!
# Intrinsic model obstructions for exchanged B.5 components

Even-field PSL₂ has no element of order four; odd-prime PSL₂ has two-rank
at most two. Concrete unipotent elements of Sp₄ and G₂ have order four,
while their elementary root subgroups have rank at least three. This excludes
these rows without dimension arguments or additional module hypotheses.
The remaining finite order comparisons reuse the source swapped-model sieve.

Source: Aschbacher--Smith C.2.7(3), pp.145--147, and 15.4.20, p.1164.
-/

public section
open Subgroup Theory.GroupTheory Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ModelPruning
open ChapterB.QuasisimpleSource
variable {Q : Type*} [Group Q] [Finite Q]

theorem swapped_rank_le_two_of_four
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q)
    (x : Q) (hx : x ^ 4 = 1) (hne : x ^ 2 ≠ 1) : primeRank 2 Q ≤ 2 := by
  rcases hs with ⟨n,_,_,F,_,_,hF,⟨e⟩⟩ | ⟨p,hp,ho,F,_,_,hF,⟨e⟩⟩
  · exfalso
    have hn : n ≠ 0 := by
      intro hn; rw [hn,pow_zero] at hF
      have := Finite.one_lt_card (α := F)
      omega
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    let f : Q ≃* SL(2,F) := e.trans (Representation.SL2NaturalH1.projectiveEquiv (K := F))
    have h4 : (f x)^4=1 := by rw [← map_pow,hx,map_one]
    have h2 : (f x)^2=1 := by
      rcases Representation.QuadraticFourGroup.specialLinear_involutionOddSpectrum (f x) with he | he
      · simpa only [he] using pow_orderOf_eq_one (f x)
      · have hd := orderOf_dvd_of_pow_eq_one h4
        have hc : Nat.Coprime (orderOf (f x)) 4 := (Nat.coprime_two_right.mpr he).pow_right 2
        have h1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc dvd_rfl hd)
        rw [h1,one_pow]
    exact hne (f.injective (by simpa only [map_pow,map_one] using h2))
  · let hodd : GorensteinWalter.IsOddPrimePower (Nat.card F) :=
      ⟨p,1,hp,ho,by decide,by simpa using hF⟩
    let : Finite PGL(2,F) := Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
    rw [primeRank_equiv 2 e]
    exact (primeRank_le_of_injective 2 ProjectiveSpecialLinearGroup.toPGL
      ProjectiveSpecialLinearGroup.toPGL_injective).trans (Theory.PSL2.odd_pgl_two_rank F hodd)

private theorem symplectic_four (F : BinaryField) :
    ∃ x : Theory.SpecificGroups.SymplecticFour.Sp F.Carrier, x^4=1 ∧ x^2≠1 := by
  let a := Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element (1:F.Carrier) 0 0 1
  have h4 : a^4=1 := by
    rw [show 4=2*2 by decide,pow_mul]
    rw [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_square]
    simp only [one_pow,one_mul]
    change (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element (0:F.Carrier) 1 1 0)^2=1
    rw [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_square]
    simp [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.theta,
      Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_zero]
  have h2 : a^2≠1 := by
    rw [Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_square]
    simp only [one_pow,one_mul]
    rw [←Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_zero (F:=F.Carrier)]
    change Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element (0:F.Carrier) 1 1 0 ≠
      Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element 0 0 0 0
    intro h
    have hh := (Theory.SpecificGroups.SymplecticFour.CentralRootGeometry.element_eq_iff _ _ _ _ _ _ _ _).mp h
    simp at hh
  exact ⟨a.val,by exact congrArg Subtype.val h4,
    fun h => h2 (Subtype.ext h)⟩

theorem not_symplectic (F : BinaryField) (e : Q ≃* Matrix.symplecticGroup (Fin 2) F.Carrier)
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) : False := by
  obtain ⟨x,h4,h2⟩ := symplectic_four F
  have hb := swapped_rank_le_two_of_four hs (e.symm x)
    (by rw [←map_pow,h4,map_one]) (by intro h; exact h2 (e.symm.injective (by simpa only [map_pow,map_one] using h)))
  rw [primeRank_equiv 2 e] at hb
  have hlo := Theory.SpecificGroups.SymplecticFour.EvenTwoRank.three_mul_le_rank F.card_eq
  change 3*F.degree ≤ primeRank 2 (Matrix.symplecticGroup (Fin 2) F.Carrier) at hlo
  have := F.degree_pos
  omega

private theorem g2_four (F : BinaryField) :
    ∃ x : Atlas.G2.Model F.Carrier, x^4=1 ∧ x^2≠1 := by
  let t : Fin 6 → F.Carrier := ![0,1,0,0,1,0]
  let u : Fin 6 → F.Carrier := ![1,0,0,0,0,0]
  have ht : Atlas.G2.unipotentProductParameters t t = u := by
    funext i; fin_cases i <;>
      simp [t,u,Atlas.G2.unipotentProductParameters,CharTwo.neg_eq,CharTwo.two_eq_zero,CharTwo.add_self_eq_zero]
  have hu : Atlas.G2.unipotentProductParameters u u = 0 := by
    funext i; fin_cases i <;>
      simp [u,Atlas.G2.unipotentProductParameters,CharTwo.two_eq_zero,CharTwo.add_self_eq_zero]
  have hs : (Atlas.G2.unipotentProduct t)^2 = Atlas.G2.unipotentProduct u := by
    rw [pow_two,Atlas.G2.unipotentProduct_mul,ht]
  refine ⟨Atlas.G2.unipotentProduct t,?_,?_⟩
  · rw [show 4=2*2 by decide,pow_mul,hs,pow_two,Atlas.G2.unipotentProduct_mul,hu,
      Atlas.G2.unipotentProduct_zero]
  · rw [hs,←Atlas.G2.unipotentProduct_zero]
    intro he
    have hh := congrFun (Atlas.G2.unipotentProduct_injective he) 0
    simp [u] at hh

theorem not_g2 (F : BinaryField) (e : Q ≃* Atlas.G2.Model F.Carrier)
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) : False := by
  obtain ⟨x,h4,h2⟩ := g2_four F
  have hb := swapped_rank_le_two_of_four hs (e.symm x)
    (by rw [←map_pow,h4,map_one]) (by intro h; exact h2 (e.symm.injective (by simpa only [map_pow,map_one] using h)))
  rw [primeRank_equiv 2 e] at hb
  have hlo := Atlas.G2.EvenTwoRank.rank_ge F.Carrier F.card_eq
  have := F.degree_pos
  omega
omit [Finite Q] in
/-- Full binary special linear groups in dimensions four and five have the
excluded exceptional orders, before passage to any module. -/
theorem not_binaryLinear {d : ℕ} (hd : d = 4 ∨ d = 5)
    (e : Q ≃* SL(d,ZMod 2)) (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) : False := by
  have hdpos : 0 < d := by omega
  let : NeZero d := ⟨by omega⟩
  have hz : Nat.card (center SL(d,ZMod 2)) = 1 := by
    rw [Atlas.ExceptionalSupport.card_sl_center, Fintype.card_fin]
    norm_num
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center SL(d,ZMod 2))
  rw [hz,mul_one] at hc
  have ho := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 2) d
  rw [←hc,←Nat.card_congr e.toEquiv] at ho
  rcases hd with rfl | rfl
  · norm_num [Fin.prod_univ_succ] at ho
    exact not_swapped_of_exceptional_order (Or.inr (Or.inr (Or.inr (Or.inl ho)))) hs
  · norm_num [Fin.prod_univ_succ] at ho
    exact not_swapped_of_exceptional_order (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ho))))) hs

omit [Finite Q] in
/-- The triple-six row has the full central cover of order 1080. -/
theorem not_tripleSix (z : center Q ≃* Multiplicative (ZMod 3))
    (e : (Q ⧸ center Q) ≃* alternatingGroup (Fin 6))
    (hs : Chapter1.XiEmbedding.SwappedModel 3 Q) : False := by
  have hc := Subgroup.card_eq_card_quotient_mul_card_subgroup (center Q)
  rw [Nat.card_congr z.toEquiv, Nat.card_congr e.toEquiv,
    nat_card_alternatingGroup,Nat.card_fin] at hc
  have ho : Nat.card Q = 1080 := by norm_num at hc ⊢; exact hc
  exact not_swapped_of_exceptional_order (Or.inl ho) hs

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve.ExchangedCases.SourceAssembly.ModelPruning
