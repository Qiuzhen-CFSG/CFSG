module

public import CFSG.Quasithin.Chapter12.Section08.Parabolic.BinaryGeneration.Core
public import Theory.GroupTheory.SylowNormalizerOvergroup
public import Theory.GroupTheory.AbelianConjugateSpan

/-!
# The nontrivial binary action of U

The source square clause puts U in the fixed Sylow two-subgroup: its
exponent divides four and T normalizes its defining span. If U centralized
the plane, it would centralize the entire H-span, contradicting its
nonabelianness. Its plane image is thus a nontrivial two-subgroup of S₃,
which has order two. This proves the literal relative index |U:W|=2.

Source: Aschbacher–Smith, 12.8.8(2,6) and 12.8.9(1), pp.852–853.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}

theorem binary_U_isPGroup (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1) : IsPGroup 2 F.U := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  intro u
  refine ⟨2, Subtype.ext ?_⟩
  have hh := congrArg Subtype.val (pow_card_eq_one' (x := (⟨(u : G)^2, hsquare u u.property⟩ : F.Vi 1)))
  change ((u : G) ^ 2) ^ Nat.card (F.Vi 1) = 1 at hh
  rw [hc, ← pow_mul] at hh
  exact hh

theorem binary_U_le_sylow (F : InvariantFlag T V n) (hn : 1 ≤ n)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1) : F.U ≤ T :=
  (F.binary_U_isPGroup hn hsquare).le_sylow_of_normalized T
    ((F.invariant 1).trans (le_normalizer_conjugateSpanBy V F.H))

theorem binary_sylow_le_P (F : InvariantFlag T V n) (L : Subgroup G) :
    (T : Subgroup G) ≤ F.P L :=
  le_inf le_sup_right (le_iInf fun i => le_iInf fun _ => F.invariant i)

theorem binary_U_le_P (F : InvariantFlag T V n) (hn : 1 ≤ n) (L : Subgroup G)
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1) : F.U ≤ F.P L :=
  (F.binary_U_le_sylow hn hsquare).trans (F.binary_sylow_le_P L)

theorem binary_U_not_centralizes_plane (F : InvariantFlag T V n)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U) :
    ¬ F.U ≤ centralizer (F.Vi 2 : Set G) := by
  intro hc
  have hh := le_centralizer_conjugateSpanBy_of_normalizes F.U (F.Vi 2) F.H
    (le_normalizer_conjugateSpanBy V F.H) hc
  rw [← hspan] at hh
  exact hne (IsMulCommutative.of_setLike_mul_comm fun x hx y hy => (hh hy) x hx)


theorem binary_U_action_index (F : InvariantFlag T V n) [Finite G]
    [IsElementaryAbelian 2 V] (hn : 2 ≤ n) (L : Subgroup G)
    (hL : L ≤ normalizer (V : Set G))
    (hsquare : ∀ u ∈ F.U, u ^ 2 ∈ F.Vi 1)
    (hspan : F.U = conjugateSpanBy (F.Vi 2) F.H) (hne : ¬ IsMulCommutative F.U) :
    F.W.relIndex F.U = 2 := by
  let := F.binaryPlane_kleinFour hn
  let j := inclusion (F.binary_U_le_P (by omega) L hsquare)
  let f := (F.binaryPlaneAction hn L hL).comp j
  have hk : f.ker = F.W.subgroupOf F.U := by
    ext u
    change F.binaryPlaneAction hn L hL (j u) = 1 ↔ (u : G) ∈ F.W
    rw [← MonoidHom.mem_ker, F.binaryPlaneAction_ker hn L hL]
    exact (and_iff_right u.property).symm
  have hp : IsPGroup 2 f.range := (F.binary_U_isPGroup (by omega) hsquare).of_surjective
    f.rangeRestrict f.rangeRestrict_surjective
  have hc : Nat.card f.range ∣ 6 := by
    simpa only [IsKleinFour.card_mulAut] using f.range.card_subgroup_dvd_card
  have hcop : Nat.Coprime (Nat.card f.range) 3 := by
    obtain ⟨i, hi⟩ := hp.exists_card_eq
    rw [hi]
    exact (by decide : Nat.Coprime 2 3).pow_left i
  have hd : Nat.card f.range ∣ 2 := hcop.dvd_mul_right.mp hc
  have hcard : Nat.card f.range = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with he | he
    · have hr : f.range = ⊥ := Subgroup.card_eq_one.mp he
      have hh : F.U ≤ F.W := by
        intro u hu
        have hf : f ⟨u,hu⟩ = 1 := by
          have hm : f ⟨u,hu⟩ ∈ f.range := ⟨⟨u,hu⟩,rfl⟩
          rwa [hr, mem_bot] at hm
        have hm : (⟨u,hu⟩ : F.U) ∈ f.ker := hf
        rw [hk] at hm
        exact hm
      exact (F.binary_U_not_centralizes_plane hspan hne (hh.trans inf_le_right)).elim
    · exact he
  change (F.W.subgroupOf F.U).index = 2
  rw [← hk, index_ker]
  exact hcard

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
