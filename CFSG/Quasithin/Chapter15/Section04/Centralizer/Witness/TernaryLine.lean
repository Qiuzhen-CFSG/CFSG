module

public import Theory.GroupAction.ElementaryNineSylowLine
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.Family.SourceConstruction.Lifting

/-!
# The normal cubic witness in the centralizer reduction

In H = C_G(Z), a normal elementary three-subgroup of H/O_2(H) of order
three or nine and a Sylow-invariant cubic subgroup produce an actual normal
cubic subgroup of that quotient. The four-point action proves this even when
the given cubic subgroup is not normal. Its literal residual preimage gives
X = O^2(X), normal in H, with X/O_2(X) of order three.

The nontrivial two-group Z lies centrally in XT, proving XT belongs to H(T).
Thus X belongs to the source NormalCentralizerXi family. Neither Thompson
action nor the desired equality C_G(Z)=T is assumed.

The actual construction of the elementary subgroup and its Sylow-invariant
cubic subgroup remains with qt-15-04-prime-reduction and
qt-15-04-centralizer-witness, using the reducibility consequence of 15.4.2(3).
This is the corresponding implication in 15.4.9, not the full 15.4.8 or
15.4.10. Source: Aschbacher--Smith, printed p.1159.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.CentralizerWitness
open FamilySource
variable {G : Type*} [Group G] [Finite G]

/-- A normal cubic subgroup of the actual centralizer quotient gives a
member of the original lowercase xi family normal in C_G(Z). -/
theorem normalCentralizerXi_of_normal_cubic (T Z : Subgroup G)
    (hZT : Z ≤ T) (hTC : T ≤ centralizer (Z : Set G))
    (hZne : Z ≠ ⊥) (hZtwo : IsPGroup 2 Z)
    (A : Subgroup (CoreQuotient (centralizer (Z : Set G))))
    (hA : Nat.card A = 3) (hAn : A.Normal) :
    lift (centralizer (Z : Set G)) A ∈ NormalCentralizerXi T Z := by
  let H := centralizer (Z : Set G)
  let X := lift H A
  have hXH : X ≤ H := lift_le H A
  have hHN : H ≤ normalizer (X : Set G) :=
    lift_normalized H H le_rfl A (by rw [normalizer_eq_top_iff.mpr hAn]; exact le_top)
  have hZcore : Z ≤ (X ⊔ T).pCoreIn 2 :=
    le_pCoreIn_of_normalizes hZtwo (hZT.trans le_sup_right)
      ((sup_le hXH hTC).trans (Subgroup.centralizer_le_normalizer _))
  have hH : X ⊔ T ∈ Chapter1.HOver G (T : Set G) := by
    refine ⟨?_, show T ≤ X ⊔ T from le_sup_right⟩
    intro hbot
    exact hZne (le_bot_iff.mp (hbot ▸ hZcore))
  obtain ⟨e, _⟩ := prime_lift_quotient H A hA
  have hi : (pCore 2 X).index = 3 := (Nat.card_congr e.toEquiv).trans hA
  exact ⟨⟨hTC.trans hHN, lift_perfect H A, hH,
    hi ▸ Nat.prime_three, hi ▸ (by decide : Odd 3)⟩, hXH, hHN⟩

/-- The actual 15.4.9 application: the Sylow image need only preserve a
cubic subgroup of the specified elementary quotient subgroup. The normal
cubic line and all lowercase-xi lift conditions are constructed internally. -/
theorem normalCentralizerXi_nonempty_of_ternary_section
    (T : Sylow 2 G) (Z : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G))
    (hTC : (T : Subgroup G) ≤ centralizer (Z : Set G)) (hZne : Z ≠ ⊥)
    (P : Subgroup (CoreQuotient (centralizer (Z : Set G))))
    [P.Normal] [IsElementaryAbelian 3 P]
    (hP : Nat.card P = 3 ∨ Nat.card P = 9)
    (B : Subgroup (CoreQuotient (centralizer (Z : Set G))))
    (hBP : B ≤ P) (hB : Nat.card B = 3)
    (hTB : image (centralizer (Z : Set G)) (T : Subgroup G) ≤
      normalizer (B : Set (CoreQuotient (centralizer (Z : Set G))))) :
    (NormalCentralizerXi (T : Subgroup G) Z).Nonempty := by
  let H := centralizer (Z : Set G)
  let S : Sylow 2 (CoreQuotient H) :=
    (T.subtype hTC).mapSurjective (QuotientGroup.mk'_surjective (pCore 2 H))
  have hSB : (S : Subgroup (CoreQuotient H)) ≤ normalizer (B : Set (CoreQuotient H)) :=
    hTB
  obtain ⟨A, _, hn, hc⟩ := exists_normal_cubic_le_of_sylow_invariant P hP S B hBP hB hSB
  have hZtwo : IsPGroup 2 Z := T.isPGroup'.of_injective
    (Subgroup.inclusion hZT) (Subgroup.inclusion_injective hZT)
  exact ⟨lift H A, normalCentralizerXi_of_normal_cubic T Z hZT hTC hZne hZtwo A hc hn⟩

end CFSG.Quasithin.Chapter15.Section04.CentralizerWitness
