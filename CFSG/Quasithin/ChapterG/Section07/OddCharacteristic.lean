module

public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.OrderSieve
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.UnitarySieve
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.SmallParameters
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.FrobeniusExclusions
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.PSL2AutomorphismRank
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.ThreeAutomorphismRank
public import CFSG.Quasithin.ChapterG.Section07.OddCharacteristic.UnitarySmallDegree
public import CFSG.Quasithin.ChapterG.Section07.Setup
public import Theory.Representation.BinaryIrreducibleRank
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizing

/-!
# Odd-characteristic degree bounds and comparisons for G.7

Aschbacher--Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, G.7.2(2),(3) and the model branches of G.7.3(1),
printed pp.347--348 (PDF pp.358--359).

The faithful binary action and genuine Borel Frobenius subgroups reduce odd
PSL₂ parameters in degree at most eight to at most nine or seventeen.
Seventeen forces degree at least eight. The full automorphism two-rank is
at most three, and at most two at seventeen, so the source degree/rank
inequality leaves only the small parameters. Their actual isomorphisms give
PSL₂(4), PSL₃(2), and the commutator of Sp₄(2). The last step uses the
proved trivial binary symplectic center to remove the projective quotient.

For the four special/projective linear/unitary ternary alternatives, the
order sieve leaves PSU₃(3). Its genuine comparison with G₂(2)' and the
checked permutation-module filtration give degree six for every faithful
irreducible binary module of degree at most eight. The unitary parameter
is always the fixed-field order, with coefficient field of its square order.

The source wrappers retain the faithful ambient action, irreducibility of
F*(G), quasisimplicity and SQTK. Faithful conjugation on elementary two-groups
proves the ambient rank bound needed by G.7.3. Its two model branches below
have no extra rank, Frobenius, comparison or module-classification premises.
The earlier classification into these models or the exceptional A₆ cover
remains with the parent G.7.3 assembly.
-/

public section

namespace CFSG.Quasithin.ChapterG.Section07

open Theory.GroupTheory

namespace OddCharacteristic

variable {L V : Type*} [Group L] [Finite L] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

/-- G.7.2(2) for the actual odd PSL₂ models. Faithfulness alone suffices. -/
theorem psl2_degree_bounds (ρ : Representation (ZMod 2) L V)
    (hρ : Function.Injective ρ) {p e : ℕ} (hp : p.Prime) (ho : Odd p)
    (he : 0 < e) (hlarge : 9 < p ^ e) (hmodel : ClassicalGroup.IsPSL L 2 (p ^ e)) :
    6 < Module.finrank (ZMod 2) V ∧
      (p ^ e ≠ 17 → 8 < Module.finrank (ZMod 2) V) := by
  have hsmall (hd : Module.finrank (ZMod 2) V ≤ 8) : p ^ e = 17 :=
    (psl2_parameter_sieve_after_frobenius ρ hρ hp ho he hmodel hd).resolve_left
      (by omega)
  constructor
  · by_contra hd
    have h17 := hsmall (by omega)
    have := psl2_seventeen_degree_ge_eight ρ hρ (h17 ▸ hmodel)
    omega
  · intro hne
    by_contra hd
    exact hne (hsmall (by omega))

/-- G.7.2(3) for all four special/projective, linear/unitary models.
The unitary parameter is the fixed-field order. -/
theorem linear_unitary_three_small_degree (ρ : Representation (ZMod 2) L V)
    [Representation.IsIrreducible ρ] (hρ : Function.Injective ρ)
    {p : ℕ} (hp : p.Prime) (ho : Odd p) (hmodel : IsLinearUnitaryThree L p)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    p = 3 ∧ ClassicalGroup.IsPSU L 3 3 ∧ Module.finrank (ZMod 2) V = 6 := by
  obtain ⟨hp3, hpsu⟩ := linear_unitary_three_identification ρ hρ hp ho hmodel hd
  exact ⟨hp3, hpsu, psu33_finrank_eq_six ρ hρ hpsu hd⟩

/-- The degree/rank comparison eliminates every PSL₂ parameter above nine.
This intrinsic version takes the degree bound with the full automorphism rank. -/
theorem psl2_parameter_le_nine_of_degree_le_automorphism_rank
    (ρ : Representation (ZMod 2) L V) (hρ : Function.Injective ρ)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSL L 2 (p ^ e))
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (primeRank 2 (MulAut L) + 1)) :
    p ^ e ≤ 9 := by
  by_contra hlarge
  have hlarge : 9 < p ^ e := by omega
  have hr := psl2_automorphism_two_rank_le_three hp ho he (by omega) hmodel
  have hd8 : Module.finrank (ZMod 2) V ≤ 8 := by omega
  have h17 := (psl2_parameter_sieve_after_frobenius ρ hρ hp ho he hmodel hd8).resolve_left
    (by omega)
  have hr17 := psl2_seventeen_automorphism_two_rank_le_two (h17 ▸ hmodel)
  have hlower := psl2_seventeen_degree_ge_eight ρ hρ (h17 ▸ hmodel)
  omega

/-- The actual small-model isomorphisms in the PSL₂ branch of G.7.3(1). -/
theorem psl2_identification_of_degree_le_automorphism_rank [Group.IsPerfect L]
    (ρ : Representation (ZMod 2) L V) (hρ : Function.Injective ρ)
    {p e : ℕ} (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSL L 2 (p ^ e))
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (primeRank 2 (MulAut L) + 1)) :
    ClassicalGroup.IsPSL L 2 4 ∨ ClassicalGroup.IsPSL L 3 2 ∨
      Nonempty (L ≃* commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) := by
  rcases psl2_small_odd_identification ho.pow
    (psl2_parameter_le_nine_of_degree_le_automorphism_rank ρ hρ hp ho he hmodel hd) hmodel
      with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · obtain ⟨fL⟩ := h
    let f : ClassicalGroup.PSp 2 (ZMod 2) ≃*
        Matrix.symplecticGroup (Fin 2) (ZMod 2) :=
      (QuotientGroup.quotientMulEquivOfEq
        Theory.SpecificGroups.SymplecticFour.Binary.center_sp_two).trans QuotientGroup.quotientBot
    refine Or.inr (Or.inr ⟨fL.trans ((f.subgroupMap _).trans (MulEquiv.subgroupCongr ?_))⟩)
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr f.surjective]
    rfl

/-- The actual G₂(2)′ isomorphism and degree in the ternary branch of G.7.3(1). -/
theorem linear_unitary_three_of_degree_le_automorphism_rank [IsQuasisimple L]
    (ρ : Representation (ZMod 2) L V) [Representation.IsIrreducible ρ]
    (hρ : Function.Injective ρ) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : IsLinearUnitaryThree L p)
    (hd : Module.finrank (ZMod 2) V ≤ 2 * (primeRank 2 (MulAut L) + 1)) :
    Nonempty (L ≃* commutator (Atlas.G2.Model (ZMod 2))) ∧
      Module.finrank (ZMod 2) V = 6 := by
  have hr := linearUnitaryThree_automorphism_two_rank_le_three hp ho hmodel
  obtain ⟨_, hpsu, hdim⟩ := linear_unitary_three_small_degree ρ hρ hp ho hmodel (by omega)
  exact ⟨psu33_nonempty_equiv_g2_derived hpsu, hdim⟩

end OddCharacteristic

universe u v

variable {G : Type u} [Group G] [Finite G]
    {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V}

/-- G.7.2(2), retaining the source setup on the actual generalized Fitting subgroup. -/
theorem lemma_G_7_2_2 (h : QuasisimpleSetup K ρ) {p e : ℕ}
    (hp : p.Prime) (ho : Odd p) (he : 0 < e) (hlarge : 9 < p ^ e)
    (hmodel : ClassicalGroup.IsPSL (generalizedFitting G) 2 (p ^ e)) :
    6 < Module.finrank (ZMod 2) V ∧
      (p ^ e ≠ 17 → 8 < Module.finrank (ZMod 2) V) :=
  OddCharacteristic.psl2_degree_bounds (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) hp ho he hlarge hmodel

/-- G.7.2(3), including both the genuine PSU₃(3) identification and the degree. -/
theorem lemma_G_7_2_3 (h : QuasisimpleSetup K ρ) {p : ℕ}
    (hp : p.Prime) (ho : Odd p)
    (hmodel : OddCharacteristic.IsLinearUnitaryThree (generalizedFitting G) p)
    (hd : Module.finrank (ZMod 2) V ≤ 8) :
    ClassicalGroup.IsPSU (generalizedFitting G) 3 3 ∧ Module.finrank (ZMod 2) V = 6 := by
  let : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  exact (OddCharacteristic.linear_unitary_three_small_degree
    (ρ.comp (generalizedFitting G).subtype) (h.faithful.comp Subtype.val_injective)
    hp ho hmodel hd).2

/-- The ambient two-rank is bounded by the full automorphism two-rank of F*(G).
Irreducibility and faithfulness make conjugation faithful on each elementary
two-subgroup; injectivity on all of G is unnecessary. -/
theorem QuasisimpleSetup.rank_le_automorphisms (h : QuasisimpleSetup K ρ) :
    primeRank 2 G ≤ primeRank 2 (MulAut (generalizedFitting G)) := by
  let : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  exact Representation.BinaryIrreducibleCentralizer.primeRank_le_automorphisms
    ρ (generalizedFitting G) h.faithful

/-- The source inequality (*) passes to the intrinsic automorphism rank. -/
theorem QuasisimpleSetup.degree_le_automorphisms (h : QuasisimpleSetup K ρ)
    (hd : SmallDegree (G := G) (V := V)) :
    Module.finrank (ZMod 2) V ≤ 2 * (primeRank 2 (MulAut (generalizedFitting G)) + 1) :=
  hd.trans (Nat.mul_le_mul_left 2 (Nat.add_le_add_right h.rank_le_automorphisms 1))

/-- The PSL₂ branch of G.7.3(1), under the original ambient degree inequality.
The earlier SQTK classification supplying the model remains in the parent theorem. -/
theorem lemma_G_7_3_1_psl2 (h : QuasisimpleSetup K ρ)
    (hd : SmallDegree (G := G) (V := V)) {p e : ℕ}
    (hp : p.Prime) (ho : Odd p) (he : 0 < e)
    (hmodel : ClassicalGroup.IsPSL (generalizedFitting G) 2 (p ^ e)) :
    ClassicalGroup.IsPSL (generalizedFitting G) 2 4 ∨
      ClassicalGroup.IsPSL (generalizedFitting G) 3 2 ∨
      Nonempty ((generalizedFitting G) ≃*
        commutator (Matrix.symplecticGroup (Fin 2) (ZMod 2))) := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  exact OddCharacteristic.psl2_identification_of_degree_le_automorphism_rank
    (ρ.comp (generalizedFitting G).subtype) (h.faithful.comp Subtype.val_injective)
    hp ho he hmodel (h.degree_le_automorphisms hd)

/-- The ternary linear/unitary branch of G.7.3(1), with both source conclusions.
No group-comparison, module-classification or automorphism-rank premise remains. -/
theorem lemma_G_7_3_1_linearUnitaryThree (h : QuasisimpleSetup K ρ)
    (hd : SmallDegree (G := G) (V := V)) {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hmodel : OddCharacteristic.IsLinearUnitaryThree (generalizedFitting G) p) :
    Nonempty ((generalizedFitting G) ≃* commutator (Atlas.G2.Model (ZMod 2))) ∧
      Module.finrank (ZMod 2) V = 6 := by
  let : IsQuasisimple (generalizedFitting G) := h.quasisimple
  let : Representation.IsIrreducible (ρ.comp (generalizedFitting G).subtype) := h.irreducible
  exact OddCharacteristic.linear_unitary_three_of_degree_le_automorphism_rank
    (ρ.comp (generalizedFitting G).subtype) (h.faithful.comp Subtype.val_injective)
    hp ho hmodel (h.degree_le_automorphisms hd)

end CFSG.Quasithin.ChapterG.Section07
