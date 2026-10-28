module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components.Statements
public import Theory.GroupTheory.PPrimeCoreSurjection
public import Theory.SpecificGroups.SL2.OddCoreAndRank
public import Theory.SpecificGroups.ProjectiveLinearInvolutions

/-!
# The odd-extension rows in the first-normalizer refinement

An odd kernel with odd-characteristic SL₂ quotient is the entire intrinsic
odd core: SL₂ has trivial odd core, and the core pulls back through the
original quotient map. Applied after the literal O₂(K) quotient, this
identifies K/O₂,₂′(K) without assuming that the extension splits.

Both nonsimple extension rows of 11.1.1 therefore give alternative (1)
of 11.1.2 at the first normalizer. The exceptional prime congruences also
supply the required lower bound p ≥ 11. The final theorem uses the original
chosen flag and preserves its quotient and Cartan conventions.

The relative-components owner retains the exhaustive embedding classification,
the remaining first-normalizer sieve, the second-normalizer exclusions, and
final assembly. These proved rows do not establish the entire refinement.

Source: Aschbacher--Smith, combined manuscript, 1 March 2004,
11.1.1(3) and 11.1.2(1), printed pp.761--762; extension notation from A.3.14.
-/

public noncomputable section
open Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
open Chapter1.Section02.LocalModels

private theorem oddCore_quotient_of_odd_sl2_extension
    {A : Type*} [Group A] [Finite A] {q : ℕ} (hq : Odd q)
    (h : HasExtension A (fun N _ => Odd (Nat.card N)) (fun Q _ => Source.IsSL Q 2 q)) :
    Source.IsSL (A ⧸ pPrimeCore 2 A) 2 q := by
  obtain ⟨N,hN,hodd,F,_,_,hF,⟨e⟩⟩ := h
  let := hN
  let π := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have hk : π.ker = N := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hcore : pPrimeCore 2 A = N := by
    have h := pPrimeCore_comap_eq_of_surjective_coprime 2 π hπ
      (by rw [hk]; exact Nat.coprime_two_left.mpr hodd)
    rw [Matrix.SpecialLinearGroup.pPrimeCore_two_eq_bot
      (Field.two_ne_zero_of_odd_card F (hF.symm ▸ hq)), MonoidHom.comap_bot, hk] at h
    exact h.symm
  exact ⟨F,inferInstance,inferInstance,hF,
    ⟨(QuotientGroup.quotientMulEquivOfEq hcore).trans e⟩⟩

variable {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L L₁ L₂ K X : Subgroup G} {n : ℕ}

/-- The nilpotent odd-kernel row already gives the exact two-odd quotient
in alternative (1) of 11.1.2 at the first normalizer. -/
theorem first_refinement_of_nilpotent_extension (hfour : n = 2)
    (h : HasExtension (K ⧸ pCore 2 K)
      (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
      (fun Q _ => Source.IsSL Q 2 5)) :
    RefinementAlternative T L L₁ L₂ K X 0 n := by
  apply RefinementAlternative.sl2 rfl hfour 5 (Or.inl rfl)
  apply oddCore_quotient_of_odd_sl2_extension (by decide : Odd 5)
  obtain ⟨N,hN,hNil,hModel⟩ := h
  exact ⟨N,hN,hNil.2,hModel⟩

/-- The elementary odd-kernel row gives the prime SL₂ row with the source's
lower bound, using both congruences on the same prime. -/
theorem first_refinement_of_elementary_extension (hfour : n = 2)
    {p : ℕ} (hp : Source.ExceptionalPrime p)
    (h : HasExtension (K ⧸ pCore 2 K) (ElementaryModel p 2)
      (fun Q _ => Source.IsSL Q 2 p)) :
    RefinementAlternative T L L₁ L₂ K X 0 n := by
  obtain ⟨hprime,hfive,height⟩ := hp
  have hlarge : 11 ≤ p := by omega
  have hodd : Odd p := hprime.odd_of_ne_two (by omega)
  apply RefinementAlternative.sl2 rfl hfour p (Or.inr ⟨hprime,hlarge⟩)
  apply oddCore_quotient_of_odd_sl2_extension hodd
  obtain ⟨N,hN,⟨e⟩,hModel⟩ := h
  refine ⟨N,hN,?_,hModel⟩
  have hc : Nat.card N = p ^ 2 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 2 → ZMod p) = p ^ 2
    rw [Nat.card_fun]
    simp only [Nat.card_fin, Nat.card_zmod]
  change Odd (Nat.card N)
  rw [hc]
  exact hodd.pow

open CFSG.Quasithin.Chapter12.Section02
/-- Both nonsimple extension rows of the actual first-normalizer list feed
the full refinement directly; no triangle or further kernel assumption remains. -/
theorem first_refinement_of_odd_extension_rows
    {V : Subgroup G} {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    {c : Coordinates D S.field} (f : InvariantFlag c) (K X : Subgroup G)
    (hfour : S.field.degree = 2)
    (h : HasExtension (K ⧸ pCore 2 K)
        (fun P _ => Group.IsNilpotent P ∧ Odd (Nat.card P))
        (fun Q _ => Source.IsSL Q 2 5) ∨
      ∃ p, Source.ExceptionalPrime p ∧
        HasExtension (K ⧸ pCore 2 K) (ElementaryModel p 2)
          (fun Q _ => Source.IsSL Q 2 p)) :
    RefinementAlternative T L (f.Li 0) (f.Li 1) K X 0 S.field.degree := by
  rcases h with hn | ⟨p,hp,he⟩
  · exact first_refinement_of_nilpotent_extension hfour hn
  · exact first_refinement_of_elementary_extension hfour hp he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Components
