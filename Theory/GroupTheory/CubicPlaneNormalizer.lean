module

public import Theory.GroupTheory.CommutatorOrbitCard
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Sylow

/-!
# The normalizer of a fixed plane in a cubic extension

Suppose that A has order 27, X has order three, X normalizes A, the
intersection is trivial, and C_A(X) has order three. Then Y=C_A(X)X
has order nine, and its normalizer inside AX is nonabelian of order 27.

The normalizer congruence makes 27 divide the order of N_AX(Y). For the
upper bound, put D=A intersect N_G(Y). Its commutators with X lie in
A intersect Y=C_A(X). A generator of X and the orbit--commutator bound
therefore give |D| at most nine. The product formula for A and N_AX(Y)
gives the upper bound 27. If the normalizer were abelian, D would lie
in C_A(X), contradicting that same product formula.

No coordinate representation or assumed normalizer calculation is used.
This argument supplies the local calculation in Bender, *Finite groups
with large subgroups* (1974), proof of (4.1), printed p.225. In particular,
the calculation does not need A to be elementary abelian.
-/

open Subgroup
open scoped Pointwise IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_plane_data
    (A X : Subgroup G) (hA : Nat.card A = 27) (hX : Nat.card X = 3)
    (hXA : X ≤ normalizer (A : Set G)) (hd : Disjoint A X)
    (hC : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3) :
    Nat.card (A ⊔ X : Subgroup G) = 81 ∧
    Nat.card ((A ⊓ centralizer (X : Set G)) ⊔ X : Subgroup G) = 9 ∧
    A ⊓ ((A ⊓ centralizer (X : Set G)) ⊔ X) = A ⊓ centralizer (X : Set G) := by
  let C := A ⊓ centralizer (X : Set G)
  let Y := C ⊔ X
  have hXC : X ≤ centralizer (C : Set G) := le_centralizer_iff.mpr inf_le_right
  have hYc : Nat.card Y = 9 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint C X
      (hXC.trans (centralizer_le_normalizer _)) (hd.mono_left inf_le_left), hC, hX]
  have hSc : Nat.card (A ⊔ X : Subgroup G) = 81 := by
    rw [card_sup_eq_mul_of_normalizes_of_disjoint A X hXA hd, hA, hX]
  have hAY : A ⊔ Y = A ⊔ X := by
    dsimp [Y, C]
    rw [← sup_assoc, sup_of_le_left (show A ⊓ centralizer (X : Set G) ≤ A from inf_le_left)]
  have hYC : Y ≤ normalizer (A : Set G) :=
    sup_le (inf_le_left.trans A.le_normalizer) hXA
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A Y hYC
  rw [hA, hYc, hAY, hSc] at hprod
  refine ⟨hSc, hYc, ?_⟩
  apply le_antisymm
  · exact (eq_of_le_of_card_ge (show C ≤ A ⊓ Y from le_inf inf_le_left le_sup_left)
      (by rw [hC]; omega)).symm.le
  · exact le_inf inf_le_left le_sup_left

private theorem cubic_plane_intersection_normalizer_bound
    (A X : Subgroup G) (hX : Nat.card X = 3)
    (hXA : X ≤ normalizer (A : Set G))
    (hC : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3)
    (hAY : A ⊓ ((A ⊓ centralizer (X : Set G)) ⊔ X) = A ⊓ centralizer (X : Set G)) :
    Nat.card (A ⊓ normalizer (((A ⊓ centralizer (X : Set G)) ⊔ X : Subgroup G) : Set G) : Subgroup G) ≤ 9 := by
  let C := A ⊓ centralizer (X : Set G)
  let Y := C ⊔ X
  let D := A ⊓ normalizer (Y : Set G)
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : IsCyclic X := isCyclic_of_prime_card hX
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := X)
  have hgen : zpowers (x : G) = X := by
    apply le_antisymm (zpowers_le.mpr x.property)
    intro y hy
    obtain ⟨n, hn⟩ := (mem_zpowers_iff.mp (hx ⟨y, hy⟩))
    exact mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
  have hcomm : ⁅D, zpowers (x : G)⁆ ≤ C := by
    rw [hgen]
    apply (le_inf ?_ ?_).trans hAY.le
    · exact (commutator_mono (show D ≤ A from inf_le_left) le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hXA)
    · exact (commutator_mono le_rfl (show X ≤ Y from le_sup_right)).trans
        (le_normalizer_iff_commutator_le_right.mp (show D ≤ normalizer (Y : Set G) from inf_le_right))
  have hcent : D ⊓ centralizer ({(x : G)} : Set G) ≤ C := by
    intro a ha
    refine ⟨ha.1.1, ?_⟩
    have hc : zpowers (x : G) ≤ centralizer ({a} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
        (mem_centralizer_singleton_iff.mp ha.2).symm)
    rw [hgen] at hc
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hc hy)
  have hc := card_le_commutator_card_mul_centralizer D (x : G)
  have hrelative : Nat.card ((centralizer ({(x : G)} : Set G)).subgroupOf D) =
      Nat.card (D ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) := by
    rw [← inf_subgroupOf_left (centralizer ({(x : G)} : Set G)) D]
    exact Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hrelative] at hc
  calc
    Nat.card D ≤ Nat.card (⁅D, zpowers (x : G)⁆ : Subgroup G) *
      Nat.card (D ⊓ centralizer ({(x : G)} : Set G) : Subgroup G) := hc
    _ ≤ Nat.card C * Nat.card C := Nat.mul_le_mul (card_le_of_le hcomm) (card_le_of_le hcent)
    _ = 9 := by rw [hC]

/-- The fixed line of a cubic extension has a nonabelian normalizer of order 27
inside the extension. -/
public theorem cubic_plane_normalizer_card_nonabelian
    (A X : Subgroup G) (hA : Nat.card A = 27) (hX : Nat.card X = 3)
    (hXA : X ≤ normalizer (A : Set G)) (hd : Disjoint A X)
    (hC : Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3) :
    let Y := (A ⊓ centralizer (X : Set G)) ⊔ X
    let Z := (A ⊔ X) ⊓ normalizer (Y : Set G)
    Nat.card Z = 27 ∧ ¬ IsMulCommutative Z := by
  let C := A ⊓ centralizer (X : Set G)
  let Y := C ⊔ X
  let S := A ⊔ X
  let Z := S ⊓ normalizer (Y : Set G)
  obtain ⟨hSc, hYc, hAY⟩ := cubic_plane_data A X hA hX hXA hd hC
  have hYS : Y ≤ S := sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hXZ : X ≤ Z := le_inf le_sup_right (le_sup_right.trans Y.le_normalizer)
  have hAZ : A ⊔ Z = S := le_antisymm (sup_le le_sup_left inf_le_left)
    (sup_le le_sup_left (hXZ.trans le_sup_right))
  have hZn : Z ≤ normalizer (A : Set G) :=
    inf_le_left.trans (sup_le A.le_normalizer hXA)
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes A Z hZn
  rw [hA, hAZ, hSc] at hprod
  have hD : Nat.card (A ⊓ Z : Subgroup G) ≤ 9 := by
    have he : A ⊓ Z = A ⊓ normalizer (Y : Set G) := by
      dsimp [Z]; rw [← inf_assoc, inf_of_le_left (show A ≤ S from le_sup_left)]
    rw [he]
    exact cubic_plane_intersection_normalizer_bound A X hX hXA hC hAY
  have hZsmall : Nat.card Z ≤ 27 := by omega
  have hZeq : Nat.card Z = 27 := by
    let : Fact (Nat.Prime 3) := ⟨by decide⟩
    have hcY : Nat.card (Y.subgroupOf S) = 3 ^ 2 := by
      rw [Nat.card_congr (subgroupOfEquivOfLe hYS).toEquiv, hYc]
      norm_num
    have hdiv := Sylow.prime_pow_dvd_card_normalizer (p := 3) (n := 2)
      (show 3 ^ (2 + 1) ∣ Nat.card S by rw [hSc]; decide) hcY
    have he : (normalizer (Y.subgroupOf S : Set S)).map S.subtype = Z := by
      rw [← subgroupOf_normalizer_eq hYS, subgroupOf_map_subtype, inf_comm]
    have hZdiv : 27 ∣ Nat.card Z := by
      rw [← he, card_map_of_injective S.subtype_injective]
      exact hdiv
    exact le_antisymm hZsmall (Nat.le_of_dvd Nat.card_pos hZdiv)
  refine ⟨hZeq, ?_⟩
  intro hab
  let : IsMulCommutative Z := hab
  have hsmall : A ⊓ Z ≤ C :=
    le_inf inf_le_left (inf_le_right.trans (Z.le_centralizer.trans (centralizer_le hXZ)))
  have hc := card_le_of_le hsmall
  rw [hC] at hc
  rw [hZeq] at hprod
  omega
end Subgroup
