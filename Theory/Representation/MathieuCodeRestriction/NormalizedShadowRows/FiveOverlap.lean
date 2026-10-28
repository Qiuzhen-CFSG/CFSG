module
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.SpecificGroups.SymmetricFive.SylowOvergroup
public import Theory.SpecificGroups.SymmetricFiveInvolutions

/-!
# The symmetric-five overlap under odd-normalizer control

Odd-normalizer control passes through a two-group kernel: lift an odd
prime subgroup by a Sylow subgroup of its full preimage, then use the
coprime normalizer theorem. In S₅, a normal subgroup of a point stabilizer
containing a transposition contains a three-cycle. The transposition on
the two unused letters centralizes that cycle and escapes the stabilizer.
These observations exclude the single-five chief quotient in the original
M22-code inside-core argument, with the full quotient map retained.

Source: Aschbacher--Smith, 3.1.9(6), final paragraph on p.578, used in
8.2.2(1), p.715, together with odd-normalizer control 4.4.3.
The source consumer is Chapter8/Section02/MathieuShadowRows/FiveChiefExclusion.
-/

public section
open Subgroup
namespace MathieuCode.NormalizedShadowRows

/-- Odd-normalizer control descends through a two-group kernel, for odd prime subgroups. -/
theorem odd_normalizer_control_image
    {G D : Type*} [Group G] [Finite G] [Group D]
    (q : G →* D) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (B C : Subgroup G)
    (hc : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ C → Odd (Nat.card X) →
      normalizer (X : Set G) ≤ B)
    (Y : Subgroup D) (hY : IsPGroup 3 Y) (hne : Y ≠ ⊥) (hYC : Y ≤ C.map q) :
    normalizer (Y : Set D) ≤ B.map q := by
  let U := C ⊓ Y.comap q
  let f : U →* Y := {
    toFun := fun x => ⟨q x,x.property.2⟩
    map_one' := Subtype.ext (map_one q)
    map_mul' := fun x y => Subtype.ext (map_mul q (x : G) (y : G)) }
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x,hx,hxy⟩ := hYC y.property
    exact ⟨⟨x,hx,show q x ∈ Y from hxy.symm ▸ y.property⟩,Subtype.ext hxy⟩
  let P : Sylow 3 U := Sylow.nonempty.some
  let X : Subgroup G := (P : Subgroup U).map U.subtype
  have hPX : IsPGroup 3 X := P.isPGroup'.map U.subtype
  have hX : X.map q = Y := by
    have ht : ((P.mapSurjective hf : Sylow 3 Y) : Subgroup Y) = ⊤ :=
      ((P.mapSurjective hf).is_maximal' (hY.to_subgroup ⊤) le_top).symm
    have hm := congrArg (map Y.subtype) ht
    change ((P : Subgroup U).map f).map Y.subtype = (⊤ : Subgroup Y).map Y.subtype at hm
    rw [map_map,←MonoidHom.range_eq_map,range_subtype] at hm
    change ((P : Subgroup U).map U.subtype).map q = Y
    rw [map_map]
    exact hm
  have hodd : Odd (Nat.card X) := by
    obtain ⟨n,hn⟩ := hPX.exists_card_eq
    rw [hn]
    exact (by decide : Odd 3).pow
  have hXne : X ≠ ⊥ := by
    intro he
    exact hne (by rw [←hX,he,Subgroup.map_bot])
  have hXC : X ≤ C := (map_subtype_le _).trans inf_le_left
  let : Fact (IsPGroup 3 X) := ⟨hPX⟩
  have hcop : Nat.Coprime 3 (Nat.card q.ker) := by
    obtain ⟨n,hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  rw [←hX,normalizer_map_eq_of_coprime_kernel 3 X q hq hcop]
  exact map_mono (hc X hXne hXC hodd)

namespace FiveOverlap
abbrev D := Equiv.Perm (Fin 5)

private theorem witnesses (i j k : Fin 5) (hjk : j ≠ k)
    (hfix : Equiv.swap j k i = i) :
    ∃ l m : Fin 5, l ≠ i ∧ l ≠ j ∧ l ≠ k ∧
      m ≠ i ∧ m ≠ j ∧ m ≠ k ∧ m ≠ l := by
  revert i j k
  decide +kernel

/-- A normal subgroup of a point stabilizer containing a transposition
contains a cubic with a normalizer outside that point stabilizer. -/
theorem cubic_of_swap (i : Fin 5) (C : Subgroup D)
    (hC : C ≤ MulAction.stabilizer D i)
    (hn : MulAction.stabilizer D i ≤ normalizer (C : Set D))
    (a : D) (ha : a ∈ C) (hs : a.IsSwap) :
    ∃ x : D, x ∈ C ∧ orderOf x = 3 ∧
      ¬ normalizer (zpowers x : Set D) ≤ MulAction.stabilizer D i := by
  obtain ⟨j,k,hjk,rfl⟩ := hs
  have hfix : Equiv.swap j k i = i := hC ha
  obtain ⟨l,m,hli,hlj,hlk,hmi,hmj,hmk,hml⟩ := witnesses i j k hjk hfix
  let b : D := Equiv.swap j l
  let x : D := Equiv.swap j k * (b * Equiv.swap j k * b⁻¹)
  let z : D := Equiv.swap i m
  have hbi : b i = i := by
    have hh : ∀ i j k l : Fin 5, j ≠ k → Equiv.swap j k i = i →
      l ≠ i → Equiv.swap j l i = i := by decide +kernel
    exact hh i j k l hjk hfix hli
  have hx : x ∈ C := C.mul_mem ha (le_normalizer_iff.mp hn b hbi _ ha)
  have ho : orderOf x = 3 := by
    have hh : ∀ j k l : Fin 5, j ≠ k → l ≠ j → l ≠ k →
        (Equiv.swap j k * (Equiv.swap j l * Equiv.swap j k * (Equiv.swap j l)⁻¹))^3 = 1 ∧
        Equiv.swap j k * (Equiv.swap j l * Equiv.swap j k * (Equiv.swap j l)⁻¹) ≠ 1 := by
      decide +kernel
    exact orderOf_eq_prime (hh j k l hjk hlj hlk).1 (hh j k l hjk hlj hlk).2
  have hc : Commute x z := by
    have hji : j ≠ i := by
      intro he
      subst j
      simp only [Equiv.swap_apply_left] at hfix
      exact hjk hfix.symm
    have hki : k ≠ i := by
      intro he
      subst k
      simp only [Equiv.swap_apply_right] at hfix
      exact hjk hfix
    have h₁ : Commute (Equiv.swap j k : D) z :=
      (Equiv.Perm.disjoint_swap_swap (by simp [List.nodup_cons, hji, hki, hjk,
        hmi.symm, hmj.symm, hmk.symm])).commute
    have h₂ : Commute b z :=
      (Equiv.Perm.disjoint_swap_swap (by simp [List.nodup_cons, hji, hli, hlj.symm,
        hmi.symm, hmj.symm, hml.symm])).commute
    exact h₁.mul_left ((h₂.mul_left h₁).mul_left h₂.inv_left)
  refine ⟨x,hx,ho,?_⟩
  intro hN
  have hz : z ∈ centralizer (zpowers x : Set D) := by
    apply mem_centralizer_iff.mpr
    intro y hy
    obtain ⟨n,rfl⟩ := hy
    exact (hc.zpow_left n).eq
  have hzi : z i = i := hN (centralizer_le_normalizer _ hz)
  exact hmi (by simpa only [z,Equiv.swap_apply_left] using hzi)
/-- A two-group cover of S₅ cannot have the source odd-normalizer control
and a centralizing odd involution in its maximal Sylow overlap. -/
theorem quotient_impossible
    {H : Type*} [Group H] [Finite H]
    (q : H →* D) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (S : Sylow 2 H) (B C : Subgroup H)
    (hSB : (S : Subgroup H) ≤ B) (hB : IsCoatom B) (hker : q.ker ≤ B)
    (hCB : C ≤ B) (hn : B ≤ normalizer (C : Set H))
    (hc : ∀ X : Subgroup H, X ≠ ⊥ → X ≤ C → Odd (Nat.card X) →
      normalizer (X : Set H) ≤ B)
    (a : D) (ha : a ∈ C.map q) (hs : a.IsSwap) : False := by
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.SymmetricFive.SylowOvergroup.quotient_image_eq_point_stabilizer
    q hq S B hSB hB hker
  have hCi : C.map q ≤ MulAction.stabilizer D i := hi ▸ map_mono hCB
  have hni : MulAction.stabilizer D i ≤ normalizer (C.map q : Set D) := by
    rw [←hi]
    exact (map_mono hn).trans (C.le_normalizer_map q)
  obtain ⟨x,hx,ho,hescape⟩ := cubic_of_swap i (C.map q) hCi hni a ha hs
  have hY : IsPGroup 3 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,ho,pow_one])
  have hne : zpowers x ≠ ⊥ := by
    rw [ne_eq,zpowers_eq_bot]
    intro he
    simp only [he,orderOf_one] at ho
    contradiction
  exact hescape ((odd_normalizer_control_image q hq hk B C hc (zpowers x) hY hne
    (zpowers_le.mpr hx)).trans_eq hi)

end FiveOverlap
end MathieuCode.NormalizedShadowRows
