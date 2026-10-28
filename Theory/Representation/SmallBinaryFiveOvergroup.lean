module
public import Theory.Representation.SmallBinaryPrimeNormalizer
public import Theory.GroupAction.OddFiveSixteen
public import Theory.GroupTheory.Fitting.PrimeComplementCentralizer
public import Theory.GroupTheory.PResidual.NormalComplement

/-!
# Whole overgroups of a normal five on a binary four-space

The centralizer of the normal five has odd order dividing fifteen. Conjugation
embeds every two-subgroup in the cyclic automorphism group of the five. The
two-core vanishes, so the Fitting subgroup has odd order. Restriction of the
original faithful action makes it the marked five or cyclic of order fifteen.

Source: Aschbacher--Smith 15.1.7(5) and 15.2.1(4), printed pp.1087--1088
and 1104. No classification of the whole actor is assumed.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Representation.SmallBinaryFiveOvergroup
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
  (h4 : Module.finrank (ZMod 2) V = 4)
  (P : Subgroup G) [P.Normal] (hP : Nat.card P = 5)

include h4 in
private theorem module_card : Nat.card (Multiplicative V) = 16 := by
  change Nat.card V = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, h4]
  rfl

include ρ hf h4 hP

omit [P.Normal] in
/-- The full centralizer is odd, with order dividing fifteen. -/
theorem centralizer_card_dvd : Nat.card (centralizer (P : Set G)) ∣ 15 := by
  let := BinaryGroupAction.action ρ
  let := BinaryGroupAction.faithful ρ hf
  let : Finite V := Module.finite_of_finite (ZMod 2)
  exact card_centralizer_five_dvd_fifteen (V := Multiplicative V) P hP (module_card h4)

/-- Every two-subgroup embeds by its actual conjugation action on the five. -/
theorem two_subgroup (S : Subgroup G) (hS : IsPGroup 2 S) :
    IsCyclic S ∧ Nat.card S ∣ 4 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  let f : S →* MulAut P := MulAut.conjNormal.comp S.subtype
  have hd : Disjoint S (centralizer (P : Set G)) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n,hn⟩ := hS.exists_card_eq
    rw [hn]
    exact ((by decide : Nat.Coprime 2 15).of_dvd_right
      (centralizer_card_dvd ρ hf h4 P hP)).pow_left n
  have hi : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply bot_unique
    intro s hs
    apply Subtype.ext
    apply disjoint_def.mp hd s.property
    rw [← MulAut.conjNormal_ker_eq_centralizer P]
    exact hs
  let e : MulAut P ≃* (ZMod 5)ˣ := by
    have he := IsCyclic.mulAutMulEquiv P
    rw [hP] at he
    exact he
  let : IsCyclic (MulAut P) := isCyclic_of_injective e.toMonoidHom e.injective
  refine ⟨isCyclic_of_injective f hi, ?_⟩
  have hh := card_dvd_of_injective f hi
  rw [IsCyclic.card_mulAut,hP] at hh
  exact hh

/-- A normal five in this faithful degree forces the ambient two-core to vanish. -/
theorem twoCore_eq_bot : pCore 2 G = ⊥ := by
  have hc : Nat.Coprime (Nat.card (pCore 2 G)) (Nat.card P) := by
    obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn,hP]
    exact (by decide : Nat.Coprime 2 5).pow_left n
  have hle : pCore 2 G ≤ centralizer (P : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (commutator_eq_bot_of_disjoint (disjoint_of_coprime_natCard hc))
  have hodd : Odd (Nat.card (pCore 2 G)) :=
    (by decide : Odd 15).of_dvd_nat
      ((card_dvd_of_le hle).trans (centralizer_card_dvd ρ hf h4 P hP))
  obtain ⟨n,hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
  apply (eq_bot_iff_card _).mpr
  have hn0 : n = 0 := by
    by_contra hn0
    exact hodd.not_two_dvd_nat (hn ▸ dvd_pow_self 2 hn0)
  rw [hn,hn0]
  rfl

/-- The Fitting alternative identifies the literal subgroup. -/
theorem fitting_alternatives : fittingSubgroup G = P ∨
    Nonempty (fittingSubgroup G ≃* Multiplicative (ZMod 15)) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : IsCyclic P := isCyclic_of_prime_card hP
  have hPF : P ≤ fittingSubgroup G := le_sSup ⟨inferInstance,inferInstance⟩
  let F := fittingSubgroup G
  let A := P.subgroupOf F
  have hA : Nat.card A = 5 :=
    (Nat.card_congr (subgroupOfEquivOfLe hPF).toEquiv).trans hP
  have hodd : Odd (Nat.card F) := by
    apply Nat.coprime_two_left.mp
    exact pPrimeCore_coprime_card.of_dvd_right (card_dvd_of_le
      (fitting_le_pPrimeCore_of_pCore_eq_bot 2 (twoCore_eq_bot ρ hf h4 P hP)))
  by_cases he : F = P
  · exact Or.inl he
  · right
    let := BinaryGroupAction.action ρ
    let := BinaryGroupAction.faithful ρ hf
    let : Finite V := Module.finite_of_finite (ZMod 2)
    let a := MulDistribMulAction.toMulAut G (Multiplicative V)
    have ha : Function.Injective a := by
      intro x y heq
      exact FaithfulSMul.eq_of_smul_eq_smul (α := Multiplicative V)
        (fun v => congrArg (fun f : MulAut (Multiplicative V) => f v) heq)
    have hlt : A < ⊤ := lt_of_le_of_ne le_top (by
      intro heq
      have hh := congrArg (fun H : Subgroup F => H.map F.subtype) heq
      rw [map_subgroupOf_eq_of_le hPF,← MonoidHom.range_eq_map,range_subtype] at hh
      exact he hh.symm)
    obtain ⟨hc,hcy⟩ := Theory.GroupAction.cyclic_fifteen_of_normal_five_lt_top
      (a.comp F.subtype) (ha.comp F.subtype_injective) A hA hodd (module_card h4) hlt
    let := hcy
    exact ⟨mulEquivOfCyclicCardEq (by simpa using hc)⟩
end Representation.SmallBinaryFiveOvergroup
