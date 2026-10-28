module

public import GorensteinWalter.DihedralOuterInvolutionConjugacy
public import GorensteinWalter.KleinFourExceptionTransport
public import GorensteinWalter.KleinFourCentralizerTransport
public import Mathlib.GroupTheory.Sylow

/-!
# Mixed four-group fusion for dihedral Sylow groups of order eight

A Klein four-subgroup has index two in a dihedral group of order eight,
hence is normal. Fusion of involutions outside a noncyclic index-two
subgroup forces uniqueness of the other Klein four. Sylow conjugacy
then gives the corresponding ambient fusion theorem.

The consumer is the four-actor catalogue for PSL₂(11), used for the
finite-generation alternative to Guralnick–Malle, Classification of
2F-modules I, Proposition 4.1 (Aschbacher–Smith K.2, printed p.453).
-/

public section
open Subgroup GorensteinWalter
namespace Theory.PSL2.ElevenConjugateBudget.Coverage

private theorem klein_isPGroup {G : Type*} [Group G] (hG : IsKleinFour G) :
    IsPGroup 2 G := by
  intro x
  refine ⟨1, ?_⟩
  simpa only [pow_one, ← hG.exponent_two] using Monoid.pow_exponent_eq_one x

/-- In a dihedral group of order eight there is a unique Klein four which
is not contained in a specified noncyclic index-two subgroup. -/
private theorem mixed_four_unique {P : Type*} [Group P] [Finite P]
    (e : P ≃* DihedralGroup 4) (H : Subgroup P)
    (hHindex : H.index = 2) (hHnoncyclic : ¬ IsCyclic H)
    (V W : Subgroup P) (hV : IsKleinFour V) (hW : IsKleinFour W)
    (hVH : ¬ V ≤ H) (hWH : ¬ W ≤ H) : V = W := by
  classical
  have hPcard : Nat.card P = 8 := (Nat.card_congr e.toEquiv).trans (by rw [DihedralGroup.nat_card])
  have hVindex : V.index = 2 := by
    have hc := V.card_mul_index
    rw [hV.card_four, hPcard] at hc
    omega
  let : V.Normal := V.normal_of_index_eq_two hVindex
  obtain ⟨v, hvV, hvH⟩ := Set.not_subset.mp hVH
  have hvI : IsInvolution v := ⟨fun h => hvH (h ▸ H.one_mem), by
    exact congrArg Subtype.val (show (⟨v, hvV⟩ : V) ^ 2 = 1 from
      hV.exponent_two ▸ Monoid.pow_exponent_eq_one _)⟩
  have outside_mem {x : P} (hxH : x ∉ H) (hx2 : x ^ 2 = 1) : x ∈ V := by
    have hxI : IsInvolution x := ⟨fun h => hxH (h ▸ H.one_mem), hx2⟩
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (dihedral_involutions_not_mem_noncyclic_index_two_isConj
        (m := 2) (by decide) e H hHindex hHnoncyclic hvI hxI hvH hxH)
    exact hg ▸ (inferInstance : V.Normal).conj_mem v hvV g
  obtain ⟨w, hwW, hwH⟩ := Set.not_subset.mp hWH
  have square {x : P} (hxW : x ∈ W) : x ^ 2 = 1 :=
    congrArg Subtype.val (show (⟨x, hxW⟩ : W) ^ 2 = 1 from
      hW.exponent_two ▸ Monoid.pow_exponent_eq_one _)
  have hwV : w ∈ V := outside_mem hwH (square hwW)
  apply (Subgroup.eq_of_le_of_card_ge (H := W) (K := V) ?_ ?_).symm
  · intro x hxW
    by_cases hxH : x ∈ H
    · have hwxH : w * x ∉ H := by
        intro h
        exact hwH ((H.mul_mem_cancel_right hxH).mp h)
      have hwxV := outside_mem hwxH (square (W.mul_mem hwW hxW))
      exact (V.mul_mem_cancel_left hwV).mp hwxV
    · exact outside_mem hxH (square hxW)
  · rw [hV.card_four, hW.card_four]

/-- The mixed Klein four-groups form one conjugacy class when every Sylow
is dihedral of order eight and meets the index-two subgroup noncyclically. -/
theorem mixed_four_conjugate {G : Type*} [Group G] [Finite G]
    (J : Subgroup G) (hJindex : J.index = 2)
    (hSylow : ∀ P : Sylow 2 G, Nonempty (P ≃* DihedralGroup 4))
    (hJnoncyclic : ∀ P : Sylow 2 G, ¬ IsCyclic (J.subgroupOf (P : Subgroup G)))
    (A B : Subgroup G) (hA : IsKleinFour A) (hB : IsKleinFour B)
    (hAJ : ¬ A ≤ J) (hBJ : ¬ B ≤ J) :
    ∃ g : G, B = A.map (MulAut.conj g).toMonoidHom := by
  classical
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : J.Normal := J.normal_of_index_eq_two hJindex
  obtain ⟨P, hBP⟩ := (klein_isPGroup hB).exists_le_sylow
  obtain ⟨Q, hAQ⟩ := (klein_isPGroup hA).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  let A' := A.map (MulAut.conj g).toMonoidHom
  have hA'P : A' ≤ (P : Subgroup G) := by
    rw [← hg]
    change A.map (MulAut.conj g).toMonoidHom ≤
      (Q : Subgroup G).map (MulAut.conj g).toMonoidHom
    exact Subgroup.map_mono hAQ
  have hA' : IsKleinFour A' := isKleinFour_map_mulEquiv A hA (MulAut.conj g)
  have hA'J : ¬ A' ≤ J := by
    intro h
    apply hAJ
    intro a ha
    have hh := (inferInstance : J.Normal).conj_mem
      ((MulAut.conj g) a) (h (Subgroup.mem_map_of_mem _ ha)) g⁻¹
    simpa [MulAut.conj_apply, mul_assoc] using hh
  let H := J.subgroupOf (P : Subgroup G)
  have hHindex : H.index = 2 := by
    have hd : H.index ∣ 2 := by
      change J.relIndex (P : Subgroup G) ∣ 2
      simpa only [hJindex] using J.relIndex_dvd_index_of_normal (P : Subgroup G)
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · exfalso
      apply hBJ
      have ht := Subgroup.index_eq_one.mp he
      intro b hb
      exact show (⟨b, hBP hb⟩ : P) ∈ H from ht ▸ Subgroup.mem_top _
    · exact he
  have hnA : ¬ A'.subgroupOf (P : Subgroup G) ≤ H := by
    intro h
    apply hA'J
    intro a ha
    exact h (show (⟨a, hA'P ha⟩ : P) ∈ A'.subgroupOf (P : Subgroup G) from ha)
  have hnB : ¬ B.subgroupOf (P : Subgroup G) ≤ H := by
    intro h
    apply hBJ
    intro b hb
    exact h (show (⟨b, hBP hb⟩ : P) ∈ B.subgroupOf (P : Subgroup G) from hb)
  obtain ⟨eP⟩ := hSylow P
  have he := mixed_four_unique eP H hHindex (hJnoncyclic P)
    (A'.subgroupOf (P : Subgroup G)) (B.subgroupOf (P : Subgroup G))
    (isKleinFour_subgroupOf hA'P hA') (isKleinFour_subgroupOf hBP hB) hnA hnB
  refine ⟨g, ?_⟩
  apply le_antisymm
  · intro b hb
    have hh : (⟨b, hBP hb⟩ : P) ∈ A'.subgroupOf (P : Subgroup G) := by
      rw [he]
      exact hb
    exact hh
  · intro a ha
    have hh : (⟨a, hA'P ha⟩ : P) ∈ B.subgroupOf (P : Subgroup G) := by
      rw [← he]
      exact ha
    exact hh

end Theory.PSL2.ElevenConjugateBudget.Coverage
