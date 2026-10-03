module
public import Stellmacher.SectionOne.OneSevenFactorAction
public import Theory.GroupAction.NormalizingActor
public import Mathlib.Tactic.FinCases

/-!
# Opposite involution subgroups in a one-seven factor

For a one-seven factor `D ≅ SL₂(2)` and an order-two subgroup `Q ≤ D`,
one conjugating element `x ∈ D` gives both `D = Q ∨ Q^x` and a spanning
of the four-point action support by its `Q`-fixed and `Q^x`-fixed parts.
The summands remain inside the support, as required for coordinatewise
assembly in a product of factors.

A six-element matrix calculation, checked by kernel reduction, supplies
a conjugate involution and expresses every factor element as a word in the
two involutions. Orbit parity supplies a nonidentity fixed point on the
four-point support for each order-two subgroup. These points differ:
a common fixed point would be fixed by `D`, contradicting the coprime
fixed/commutator decomposition for its derived C3. The subgroup containing
the two distinct nonidentity points has order at least three dividing
four, hence is the whole support. No faithfulness transfer or change of
ambient module action is needed.

This is the single-factor step in the two-conjugate argument of
Stellmacher (2.3), Journal of Algebra 190 (1997), p.20, following
`refs/latex/stellmacher-n-group.tex`.
-/

namespace Stellmacher.SectionOne
universe u

private theorem sl2_exists_opposite
    {G : Type*} [Group G] [Finite G] (D Q : Subgroup G)
    (hD : IsSL2Two D) (hQD : Q ≤ D) (hQcard : Nat.card Q = 2) :
    ∃ x ∈ D, D = Q ⊔ Q.conjBy x := by
  classical
  let _ : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQcard]; decide)
  obtain ⟨q, hq⟩ := exists_ne (1 : Q)
  let a : D := ⟨q, hQD q.property⟩
  have ha : a ≠ 1 := by
    intro hh
    have hhG : (q : G) = 1 := congrArg (fun d : D => (d : G)) hh
    exact hq (Subtype.ext hhG)
  have ha2 : a ^ 2 = 1 := by
    apply Subtype.ext
    have hq2 : q ^ 2 = 1 := by
      rw [← hQcard]
      exact pow_card_eq_one' (x := q)
    exact congrArg (fun q : Q => (q : G)) hq2
  obtain ⟨e⟩ := hD
  have htable : ∀ a : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      a ≠ 1 → a ^ 2 = 1 → ∃ x,
      ∀ d, d = 1 ∨ d = a ∨ d = x * a * x⁻¹ ∨
        d = a * (x * a * x⁻¹) ∨ d = (x * a * x⁻¹) * a ∨
        d = a * (x * a * x⁻¹) * a := by
    decide +kernel
  obtain ⟨x, hx⟩ := htable (e a) (by simpa using ha) (by simpa using congrArg e ha2)
  let y : D := e.symm x
  let b : D := y * a * y⁻¹
  have hcover (d : D) : d = 1 ∨ d = a ∨ d = b ∨ d = a * b ∨
      d = b * a ∨ d = a * b * a := by
    rcases hx (e d) with hh | hh | hh | hh | hh | hh
    · exact Or.inl (e.injective (by simpa using hh))
    · exact Or.inr (Or.inl (e.injective hh))
    · exact Or.inr (Or.inr (Or.inl (e.injective (by simpa [b, y] using hh))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (e.injective (by simpa [b, y] using hh)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e.injective (by simpa [b, y] using hh))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e.injective (by simpa [b, y] using hh))))))
  refine ⟨y, y.property, le_antisymm ?_ ?_⟩
  · let K := Q ⊔ Q.conjBy (y : G)
    have haK : (a : G) ∈ K := (le_sup_left : Q ≤ K) q.property
    have hbK : (b : G) ∈ K := (le_sup_right : Q.conjBy (y : G) ≤ K)
      ⟨q, q.property, rfl⟩
    intro d hd
    rcases hcover ⟨d, hd⟩ with hh | hh | hh | hh | hh | hh
    · rw [show d = 1 from congrArg Subtype.val hh]; exact K.one_mem
    · rw [show d = (a : G) from congrArg Subtype.val hh]; exact haK
    · rw [show d = (b : G) from congrArg Subtype.val hh]; exact hbK
    · rw [show d = (a : G) * b from congrArg Subtype.val hh]; exact K.mul_mem haK hbK
    · rw [show d = (b : G) * a from congrArg Subtype.val hh]; exact K.mul_mem hbK haK
    · rw [show d = (a : G) * b * a from congrArg Subtype.val hh]
      exact K.mul_mem (K.mul_mem haK hbK) haK
  · apply sup_le hQD
    rintro d ⟨q, hq, rfl⟩
    exact D.mul_mem (D.mul_mem y.property (hQD hq)) (D.inv_mem y.property)

private theorem support_fixed_ne_one
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [MulDistribMulAction G V] (D Q : Subgroup G)
    (hU : Nat.card (commutatorAction D V) = 4)
    (hQD : Q ≤ D) (hQ : Nat.card Q = 2) :
    ∃ v : V, v ∈ commutatorAction D V ∧ v ∈ FixedPoints.subgroup Q V ∧ v ≠ 1 := by
  let U := commutatorAction D V
  let _ : IsInvariant Q V U :=
    _root_.commutatorAction_isInvariant_of_normalizing_actor Q D
      (hQD.trans D.le_normalizer)
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 1) (by simpa using hQ)
  have hone : (1 : U) ∈ MulAction.fixedPoints Q U := by
    rw [MulAction.mem_fixedPoints]
    intro q
    exact smul_one q
  obtain ⟨v, hv, hne⟩ := hQp.exists_fixed_point_of_prime_dvd_card_of_fixed_point
    U (by rw [show Nat.card U = 4 from hU]; decide) hone
  refine ⟨v, v.property, ?_, ?_⟩
  · rw [FixedPoints.mem_subgroup]
    intro q
    exact congrArg Subtype.val (hv q)
  · intro hh
    exact hne (Subtype.ext hh.symm)

open scoped IsMulCommutative

public theorem oneSevenFactor_exists_opposite
    {G V : Type u} [Group G] [Group V] [Finite G] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction G V]
    (_h : Hypotheses G V) (D Q : Subgroup G)
    (hD : IsOneSevenFactor (V := V) D) (hQD : Q ≤ D) (hQ : Nat.card Q = 2) :
    ∃ x ∈ D, D = Q ⊔ Q.conjBy x ∧
      commutatorAction D V ≤
        (commutatorAction D V ⊓ FixedPoints.subgroup Q V) ⊔
        (commutatorAction D V ⊓ FixedPoints.subgroup (Q.conjBy x) V) := by
  classical
  obtain ⟨x, hx, hgen⟩ := sl2_exists_opposite D Q hD.1 hQD hQ
  let R := Q.conjBy x
  let U := commutatorAction D V
  have hRD : R ≤ D := by rw [hgen]; exact le_sup_right
  have hR : Nat.card R = 2 := by
    change Nat.card (Q.map (MulAut.conj x).toMonoidHom) = 2
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective, hQ]
  obtain ⟨v, hvU, hvQ, hvne⟩ := support_fixed_ne_one D Q hD.2.2.1 hQD hQ
  obtain ⟨w, hwU, hwR, hwne⟩ := support_fixed_ne_one D R hD.2.2.1 hRD hR
  have hvw : v ≠ w := by
    intro heq
    have hfix : D ≤ MulAction.stabilizer G v := by
      rw [hgen]
      apply sup_le
      · intro q hq
        exact (FixedPoints.mem_subgroup (M := Q) (a := v)).mp hvQ ⟨q, hq⟩
      · intro r hr
        change r • v = v
        rw [heq]
        exact (FixedPoints.mem_subgroup (M := R) (a := w)).mp hwR ⟨r, hr⟩
    let F := (commutator D).map D.subtype
    have hvF : v ∈ FixedPoints.subgroup F V := by
      rw [FixedPoints.mem_subgroup]
      intro f
      exact hfix ((Subgroup.map_subtype_le _) f.property)
    have hcop : Nat.Coprime (Nat.card F) (Nat.card V) := by
      obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 V).exists_card_eq
      rw [show Nat.card F = 3 from hD.2.1.2.1, hn]
      exact (show Nat.Coprime 3 2 by decide).pow_right n
    have hcompl := isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := V) (A := F)
      (Group.isSolvable_of_comm fun a b => (IsMulCommutative.is_comm (M := V)).comm a b)
      hcop (inferInstance : IsMulCommutative V)
    apply hvne
    apply hcompl.disjoint.le_bot
    refine ⟨hvF, ?_⟩
    rwa [← oneSevenFactor_full_commutator_eq_derived D hD]
  let K := (U ⊓ FixedPoints.subgroup Q V) ⊔ (U ⊓ FixedPoints.subgroup R V)
  have hKU : K ≤ U := sup_le inf_le_left inf_le_left
  have hvK : v ∈ K := (le_sup_left : U ⊓ FixedPoints.subgroup Q V ≤ K) ⟨hvU, hvQ⟩
  have hwK : w ∈ K := (le_sup_right : U ⊓ FixedPoints.subgroup R V ≤ K) ⟨hwU, hwR⟩
  let f : Fin 3 → K := ![1, ⟨v, hvK⟩, ⟨w, hwK⟩]
  have hf : Function.Injective f := by
    intro i j hij
    have hijG := congrArg Subtype.val hij
    clear hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hKge : 3 ≤ Nat.card K := by
    simpa using Nat.card_le_card_of_injective f hf
  have hKdiv : Nat.card K ∣ 4 := by
    rw [← hD.2.2.1]
    exact Subgroup.card_dvd_of_le hKU
  have hKcard : Nat.card K = 4 := by
    have hh := Nat.le_of_dvd (by decide : 0 < 4) hKdiv
    have hc : Nat.card K = 3 ∨ Nat.card K = 4 := by omega
    rcases hc with hc | hc
    · rw [hc] at hKdiv
      norm_num at hKdiv
    · exact hc
  refine ⟨x, hx, hgen, ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hKU (by rw [hKcard, hD.2.2.1])).ge

end Stellmacher.SectionOne

