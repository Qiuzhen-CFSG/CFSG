module
public import Theory.Representation.BinaryCoprimeDegree.TransitivePlane
public import Theory.GroupTheory.Commutator.PerfectSmallIndex
/-!
# Binary degree from an irreducible plane in a perfect group

Every normalizer orbit of a hyperplane has at least five members. Otherwise
the perfect group acts on at most four cosets and fixes the hyperplane,
contradicting irreducibility. The actual hyperplane-orbit degree theorem then
gives degree at least 5 ordₚ(2), hence at least 15 for p>3.

This is the elementary-plane branch needed for the noncentral-Fitting
C-component in Aschbacher–Smith C.5.12, printed p.163. All subgroups and
normalizer actions are the original ones; no automorphism-group replacement
or semiregular character-orbit assumption is used.
-/
public section
open Subgroup
open scoped Pointwise
namespace Representation.BinaryCoprimeDegree
variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

theorem perfect_plane_hyperplane_orbit_card
    {p : ℕ} [Fact p.Prime] (P : Subgroup G) [P.Normal]
    (hP : Nat.card P = p^2)
    (hi : ∀ A : Subgroup P, (∀ g x, x ∈ A → MulAut.conjNormal g x ∈ A) → A=⊥ ∨ A=⊤)
    (A : Subgroup P) (hA : A.index=p) :
    5 ≤ Nat.card (normalizerHyperplaneOrbit P A) := by
  let N := normalizer (P : Set G)
  let : Group.IsPerfect N := by
    change Group.IsPerfect (normalizer (P : Set G))
    rw [normalizer_eq_top]
    infer_instance
  let : MulAction N (Subgroup P) := MulAction.compHom _ P.normalizerMonoidHom
  have horbit : normalizerHyperplaneOrbit P A = MulAction.orbit N A := rfl
  by_contra! hsmall
  have hidx : (MulAction.stabilizer N A).index ≤ 4 := by
    change Nat.card (N ⧸ MulAction.stabilizer N A) ≤ 4
    rw [← Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N A)]
    rw [← horbit]
    omega
  have htop : (⊤ : Subgroup N) ≤ MulAction.stabilizer N A :=
    le_of_isPerfect_of_index_le_four _ _ hidx
  have hinv : ∀ g x, x ∈ A → MulAut.conjNormal g x ∈ A := by
    intro g x hx
    let n : N := ⟨g,by change g ∈ normalizer (P : Set G); rw [normalizer_eq_top]; trivial⟩
    have hn := htop (mem_top n)
    change A.map (P.normalizerMonoidHom n).toMonoidHom = A at hn
    have hh := mem_map_of_mem (P.normalizerMonoidHom n).toMonoidHom hx
    rw [hn] at hh
    exact hh
  rcases hi A hinv with hb | ht
  · have hp := (Fact.out : p.Prime).two_le
    rw [hb, index_bot, hP] at hA
    nlinarith
  · rw [ht, index_top] at hA
    exact (Fact.out : p.Prime).ne_one hA.symm

private theorem three_le_order_two {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    3 ≤ orderOf (2 : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hpos : 0 < orderOf (2 : ZMod p) :=
    (isUnit_iff_ne_zero.mpr htwo).isOfFinOrder.orderOf_pos
  by_contra! hsmall
  have hcases : orderOf (2 : ZMod p)=1 ∨ orderOf (2 : ZMod p)=2 := by omega
  have hpow := pow_orderOf_eq_one (2 : ZMod p)
  rcases hcases with he | he
  · rw [he,pow_one] at hpow
    have hz : (1 : ZMod p)=0 := by linear_combination hpow
    exact one_ne_zero hz
  · rw [he] at hpow
    have hz : (3 : ZMod p)=0 := by linear_combination hpow
    have hd := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have := Nat.le_of_dvd (by decide : 0<3) hd
    omega

theorem perfect_irreducible_plane_degree
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    {p : ℕ} [Fact p.Prime] (hp : 3<p)
    (P : Subgroup G) [P.Normal] [IsElementaryAbelian p P] (hP : Nat.card P=p^2)
    (hi : ∀ A : Subgroup P, (∀ g x, x∈A → MulAut.conjNormal g x∈A) → A=⊥ ∨ A=⊤) :
    15 ≤ Module.finrank (ZMod 2) V := by
  have hne : P ≠ ⊥ := by intro hb; rw [hb,card_bot] at hP; nlinarith
  have hb := (hyperplane_orbit_degree ρ hf (by omega : p≠2) P hne 5
    (perfect_plane_hyperplane_orbit_card P hP hi)).1
  have ho := three_le_order_two (Fact.out : p.Prime) hp
  omega
end Representation.BinaryCoprimeDegree
