module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.Local
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.LocalData
public import Theory.Frattini.PGroup

/-!
# Central action in the small-extension argument

Write Q = [O₂(L),L], D = C_I(Y₊), and I⁺ = I/C_I(L). If D centralizes Q
and C_L(Q) ≤ O₂(L), the three-subgroup lemma and perfectness give [D,L] ≤ Q.
The existing central-commutator reduction then puts [D,L] in Z(Q). When
Z(Q) is elementary abelian, every square in D centralizes L. Consequently
D⁺ is elementary abelian and has trivial Frattini subgroup.

The centralizer bound and elementary center must come from the actual MS
alternatives. The remaining covering-module calculation must still show
D⁺ = 1. In particular this module does not assert the centralizer equality
or the exclusion of alternative 15.3.28(2).

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
printed p.1132 (PDF p.1149), proof of 15.3.31, centralizing branch;
compare the square argument in C.1.13 on printed p.125.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

variable {G : Type*} [Group G]

/-- The subgroup D = C_I(Y₊) used in 15.3.31, embedded in G. -/
def yplusCentralizer (d : LocalData G) (I : Subgroup G) : Subgroup G :=
  I ⊓ centralizer (d.Yplus : Set G)

/-- The centralizing branch gives [D,L] ≤ Q once the model calculation
establishes C_L(Q) ≤ O₂(L). First [D,L] lies in that centralizer; then
perfectness of L and the three-subgroup lemma lower it from O₂(L) to Q. -/
theorem commutator_le_core_of_centralizes (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) (hYL : d.Yplus ≤ c.L)
    (hnormal : (c.L.subgroupOf I).Normal)
    (hCQ : c.L ⊓ centralizer (extensionCore c.L : Set G) ≤ c.L.pCoreIn 2)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G)) :
    ⁅yplusCentralizer d I, c.L⁆ ≤ extensionCore c.L := by
  have hIL : I ≤ normalizer (c.L : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (component_le c)).mp hnormal
  have hLQ := normalizes_extensionCore c.L.le_normalizer
  have hfirst : ⁅yplusCentralizer d I, c.L⁆ ≤ c.L.pCoreIn 2 := by
    apply le_trans (le_inf ?_ ?_) hCQ
    · exact le_normalizer_iff_commutator_le_right.mp (inf_le_left.trans hIL)
    · exact (commutator_mono hDQ le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp
          (hLQ.trans (normalizer_le_normalizer_centralizer _)))
  have hrot : ⁅⁅yplusCentralizer d I, c.L⁆, c.L⁆ ≤ extensionCore c.L :=
    commutator_mono hfirst le_rfl
  have hrot' : ⁅⁅c.L, yplusCentralizer d I⁆, c.L⁆ ≤ extensionCore c.L := by
    rwa [commutator_comm c.L (yplusCentralizer d I)]
  have hthree := commutator_commutator_le_of_rotate_of_le_normalizer
    hLQ hLQ (hDQ.trans (Subgroup.centralizer_le_normalizer _)) hrot' hrot
  rw [Subgroup.isPerfect_iff.mp (component_isPerfect_of_containment d c hYL),
    commutator_comm] at hthree
  exact hthree

/-- The centralizer C_I(L), formed inside I rather than as an ambient quotient denominator. -/
def actionKernel (I L : Subgroup G) : Subgroup I :=
  (centralizer (L : Set G)).subgroupOf I

/-- Normalizers of L normalize its centralizer, so the quotient denominator is normal in I. -/
theorem actionKernel_normal {I L : Subgroup G} (hIL : I ≤ normalizer (L : Set G)) :
    (actionKernel I L).Normal :=
  normal_subgroupOf_of_le_normalizer (hIL.trans (normalizer_le_normalizer_centralizer _))

/-- The source quotient I⁺ = I/C_I(L), with relative normality supplied explicitly. -/
abbrev Plus (I L : Subgroup G) [(actionKernel I L).Normal] := I ⧸ actionKernel I L

/-- The natural map to the quotient by C_I(L). -/
def plusMap (I L : Subgroup G) [(actionKernel I L).Normal] : I →* Plus I L :=
  QuotientGroup.mk' (actionKernel I L)

/-- The image of X ∩ I in I⁺. -/
def plusImage (I L X : Subgroup G) [(actionKernel I L).Normal] : Subgroup (Plus I L) :=
  (X.subgroupOf I).map (plusMap I L)

private theorem square_centralizes_of_central_commutator {D L Z : Subgroup G}
    (hcomm : ⁅D, L⁆ ≤ Z) (hDZ : D ≤ centralizer (Z : Set G))
    (hsq : ∀ z ∈ Z, z ^ 2 = 1) {d : G} (hd : d ∈ D) :
    d ^ 2 ∈ centralizer (L : Set G) := by
  intro l hl
  apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  have hc : ⁅d, l⁆ ∈ Z := hcomm (commutator_mem_commutator hd hl)
  have hdc : Commute d ⁅d, l⁆ := (mem_centralizer_iff.mp (hDZ hd) _ hc).symm
  calc
    ⁅d ^ 2, l⁆ = ⁅d, l⁆ ^ 2 := by
      rw [pow_two, commutatorElement_mul_left_eq_conj_mul, hdc.eq]
      simp [pow_two]
    _ = 1 := hsq _ hc

private theorem elementary_of_square_eq_one {H : Type*} [Group H]
    (hsq : ∀ x : H, x ^ 2 = 1) : IsElementaryAbelian 2 H := by
  have hinv (x : H) : x⁻¹ = x := (inv_eq_iff_mul_eq_one.mpr (by simpa [pow_two] using hsq x))
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩
           exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hsq }
  calc
    x * y = (x * y)⁻¹ := (hinv _).symm
    _ = y * x := by rw [mul_inv_rev, hinv, hinv]

/-- In the centralizing branch, central elementary commutators force
every element of D⁺ to square to one. This establishes the elementary
abelian structure needed by the covering calculation; it does not prove D⁺ = 1. -/
theorem centralizerImage_elementary (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [(actionKernel I c.L).Normal]
    (hDL : ⁅yplusCentralizer d I, c.L⁆ ≤ extensionCore c.L)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G))
    (hZ : IsElementaryAbelian 2
      (extensionCore c.L ⊓ centralizer (extensionCore c.L : Set G) : Subgroup G)) :
    IsElementaryAbelian 2 (plusImage I c.L (yplusCentralizer d I)) := by
  let := hZ
  have hcomm := extension_commutator_le_center d c hDL hDQ
  have hDZ : yplusCentralizer d I ≤ centralizer
      ((extensionCore c.L ⊓ centralizer (extensionCore c.L : Set G) : Subgroup G) : Set G) :=
    hDQ.trans (centralizer_le inf_le_left)
  apply elementary_of_square_eq_one
  rintro ⟨x, a, ha, rfl⟩
  apply Subtype.ext
  change (plusMap I c.L a) ^ 2 = 1
  rw [← map_pow]
  apply (QuotientGroup.eq_one_iff _).mpr
  exact square_centralizes_of_central_commutator hcomm hDZ
    (fun z hz => elemPow_eq_one_of_isElementaryAbelian z hz) ha

/-- The actual image D⁺ has trivial Frattini subgroup in the centralizing branch. -/
theorem centralizerImage_frattini [Finite G] (d : LocalData G) {I : Subgroup G}
    (c : ComponentWitness d I) [(actionKernel I c.L).Normal]
    (hDL : ⁅yplusCentralizer d I, c.L⁆ ≤ extensionCore c.L)
    (hDQ : yplusCentralizer d I ≤ centralizer (extensionCore c.L : Set G))
    (hZ : IsElementaryAbelian 2
      (extensionCore c.L ⊓ centralizer (extensionCore c.L : Set G) : Subgroup G)) :
    frattini (plusImage I c.L (yplusCentralizer d I)) = ⊥ := by
  let := centralizerImage_elementary d c hDL hDQ hZ
  let : Fact (IsPGroup 2 (plusImage I c.L (yplusCentralizer d I))) :=
    ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- Triviality in I⁺ is exactly centralization of L for a subgroup contained in I. -/
theorem plusImage_eq_bot_iff {I L X : Subgroup G} [(actionKernel I L).Normal]
    (hXI : X ≤ I) : plusImage I L X = ⊥ ↔ X ≤ centralizer (L : Set G) := by
  rw [plusImage, Subgroup.map_eq_bot_iff,
    show (plusMap I L).ker = actionKernel I L from QuotientGroup.ker_mk' _]
  constructor
  · intro h x hx
    exact h (show (⟨x, hXI hx⟩ : I) ∈ X.subgroupOf I from hx)
  · intro h x hx
    exact h hx

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension

end
