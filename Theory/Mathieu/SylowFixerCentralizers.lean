module
public import Theory.Mathieu.M11.Properties.AutomorphismCentralizers
public import Theory.Mathieu.M12.Properties.SylowCentralizing
public import Theory.Mathieu.M12.TwoCentralInvolutions.CentralizerOrder
public import Theory.Mathieu.M12.A5Fixer.Automorphisms.OuterIndex
public import Theory.Mathieu.M22.Properties.FourNormalizers.Hexads
public import Theory.Mathieu.M22.Properties.SylowPointwise.Innerness
public import Theory.Mathieu.M22.TripleCover.ScalarAutomorphisms
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.Automorphisms
public import Theory.Mathieu.M24.Properties.InvolutionCentralizers.TwoCentral
public import Theory.GroupAction.InnerCentralizerCardinality

/-!
# Cubic obstructions in Mathieu automorphism centralizers

The native involution and automorphism calculations bound the full
centralizers of involutory Sylow fixers in all five Mathieu groups.
Their orders are indivisible by nine. For M₁₂ and M₂₄ the literal
Sylow marking selects the two-central involution class; the other three
rows use their full involution fusion. Actual outer quotients retain the
same divisibility after passage from elements to automorphisms.

Source: Aschbacher–Smith, proof of 12.6.26, printed p.832, Theorem C
inspection; GLS3 Table 5.3b–e. The imported native certificates retain
their source attribution. No representation or classification input is used.
-/

public section
open Subgroup
namespace Sporadic.Mathieu

/-- No automorphism involution of M11 has a centralizer divisible by nine. -/
theorem m11_not_nine_dvd_involution_aut_centralizer
    (a : MulAut M11) (ha : orderOf a = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut M11))) := by
  obtain ⟨t, rfl⟩ := m11_automorphism_inner a
  have ht : orderOf t = 2 := (MulAut.conj_orderOf_of_center_eq_bot m11_center_eq_bot t).symm.trans ha
  have hC : Nat.card (centralizer ({t} : Set M11)) = 48 := by
    rw [card_centralizer_eq_of_isConj _ _ (m11_involution_isConj_generatorA t ht)]
    exact m11_involutionCentralizer_card
  let := m11_outer_subsingleton
  have hd := MulAut.centralizer_conj_card_dvd m11_center_eq_bot t
  rw [hC, Nat.card_unique (α := MulAut.Outer M11), mul_one] at hd
  exact fun h => (by decide : ¬ 9 ∣ 48) (h.trans hd)

/-- The pointwise Sylow fixer in M12 has full automorphism centralizer prime to nine. -/
theorem m12_not_nine_dvd_sylow_fixer_centralizer
    (P : Sylow 2 M12) (a : MulAut M12) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut M12))) := by
  obtain ⟨x,hx,ho,he⟩ := MulAut.inner_involution_fixing_sylow_center m12_center_eq_bot P a ha
    (m12_automorphism_inner_of_fixes_sylow a P hP) hP
  have hc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral (x : M12) := ⟨P,x.property,hx⟩
  have hC := M12Involutions.card_centralizer_of_twoCentral x ho hc
  have houter : Nat.card (MulAut.Outer M12) ∣ 2 := by
    have hpos := Nat.card_pos (α := MulAut.Outer M12)
    have hle : Nat.card (MulAut.Outer M12) ≤ 2 := M12A5Fixer.Automorphisms.outerIndexBound
    have hcases : Nat.card (MulAut.Outer M12) = 1 ∨ Nat.card (MulAut.Outer M12) = 2 := by omega
    rcases hcases with h|h <;> simp only [h, one_dvd, dvd_refl]
  rw [he]
  have hd := (MulAut.centralizer_conj_card_dvd m12_center_eq_bot (x : M12)).trans
    (Nat.mul_dvd_mul_left _ houter)
  rw [hC] at hd
  exact fun h => (by decide : ¬ 9 ∣ 192 * 2) (h.trans hd)

/-- The same intrinsic obstruction holds for M22. -/
theorem m22_not_nine_dvd_sylow_fixer_centralizer
    (P : Sylow 2 M22) (a : MulAut M22) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut M22))) := by
  obtain ⟨x,rfl⟩ := M22SylowPointwise.automorphism_inner_of_fixes_sylow a P hP
  have hx : orderOf x = 2 := (MulAut.conj_orderOf_of_center_eq_bot m22_center_eq_bot x).symm.trans ha
  have hd := (MulAut.centralizer_conj_card_dvd m22_center_eq_bot x).trans
    (Nat.mul_dvd_mul_left _ M22TripleCover.ScalarAutomorphisms.m22_outer_card_dvd_two)
  rw [M22FourNormalizers.involution_centralizer_card x hx] at hd
  exact fun h => (by decide : ¬ 9 ∣ 384 * 2) (h.trans hd)

/-- The full automorphism centralizer of an M23 involution has no factor nine. -/
theorem m23_not_nine_dvd_involution_aut_centralizer
    (a : MulAut M23) (ha : orderOf a = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut M23))) := by
  obtain ⟨t,rfl⟩ := m23_conj_surjective a
  have ht : orderOf t = 2 :=
    (MulAut.conj_orderOf_of_center_eq_bot M23Geometry.m23_center_eq_bot t).symm.trans ha
  have hi : MulAut.innerSubgroup M23 = ⊤ := MonoidHom.range_eq_top.mpr m23_conj_surjective
  have ho : Nat.card (MulAut.Outer M23) = 1 := by
    let : Subsingleton (MulAut.Outer M23) := QuotientGroup.subsingleton_iff.mpr hi
    exact Nat.card_unique
  obtain ⟨e⟩ := M23Geometry.InvolutionCentralizer.centralizer_equiv_representative ht
  have hd := MulAut.centralizer_conj_card_dvd M23Geometry.m23_center_eq_bot t
  rw [Nat.card_congr e.toEquiv,M23Geometry.involutionRepresentative_centralizer_card,ho,mul_one] at hd
  exact fun h => (by decide : ¬ 9 ∣ 2688) (h.trans hd)

/-- In M24 the actual Sylow marking selects the centralizer of order 21504. -/
theorem m24_not_nine_dvd_sylow_fixer_centralizer
    (P : Sylow 2 M24) (a : MulAut M24) (ha : orderOf a = 2)
    (hP : ∀ x ∈ P, a x = x) :
    ¬ 9 ∣ Nat.card (centralizer ({a} : Set (MulAut M24))) := by
  obtain ⟨t,ht⟩ := M24OuterRestriction.conj_surjective a
  obtain ⟨x,hx,ho,he⟩ := MulAut.inner_involution_fixing_sylow_center
    M24InvolutionCentralizers.center_eq_bot P a ha ⟨t,ht.symm⟩ hP
  have hc : Theory.GroupTheory.DoubleCoverCentralizer.TwoCentral (x : M24) := ⟨P,x.property,hx⟩
  have hC := M24InvolutionCentralizers.card_centralizer_of_twoCentral x ho hc
  have hi : MulAut.innerSubgroup M24 = ⊤ :=
    MonoidHom.range_eq_top.mpr M24OuterRestriction.conj_surjective
  have houter : Nat.card (MulAut.Outer M24) = 1 := by
    let : Subsingleton (MulAut.Outer M24) := QuotientGroup.subsingleton_iff.mpr hi
    exact Nat.card_unique
  rw [he]
  have hd := MulAut.centralizer_conj_card_dvd M24InvolutionCentralizers.center_eq_bot (x : M24)
  rw [hC,houter,mul_one] at hd
  exact fun h => (by decide : ¬ 9 ∣ 21504) (h.trans hd)

end Sporadic.Mathieu

