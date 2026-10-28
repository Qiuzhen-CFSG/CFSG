module

public import Theory.Representation.BinaryOffender.OddOrderSmallCodimension
public import Theory.Representation.BinaryOffender.ComponentPermutationObstruction
public import Theory.Representation.BinaryOffender.TimmesfeldCentralizer
public import Theory.GroupTheory.TwoThreeSolvable.OddCubes

/-!
# Order-two offenders normalize components

An element moving a genuine quasisimple component has fixed codimension at
least two in every faithful finite-dimensional binary representation. Indeed,
if its codimension were at most one, each odd-order `x` in the component would
have `x^a * x⁻¹` moving at most two dimensions. Distinct components commute,
so this element has odd order and hence cube one. Thus `x³` is central in the
component. Burnside's two-prime theorem makes the central quotient solvable,
contrary to its nontrivial perfectness.

The codimension argument works for any moving element. Order two then gives
rank one for an offender, ruling out movement. For a best offender, the proved
Timmesfeld replacement theorem supplies all premises needed to exclude the
literal cyclic alternative `C_A([V,A]) = ⟨a⟩`. The final application removes
that alternative from the existing quadratic four-group construction.

Source: GLS, *The Classification of the Finite Simple Groups*, vol. 2,
Theorem 26.24 Step 2 and the following replacement argument;
`refs/KGroup/GLS2/ChapterG.tex`, lines 1225–1232.
-/

public section

open Subgroup
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

private theorem odd_cube_central_of_moving_component_codim_le_one
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    {L : Subgroup G} (hL : Theory.GroupTheory.IsComponent G L)
    (a : G) (ha : a ∉ normalizer (L : Set G))
    (hd : fixedCodim ρ (zpowers a) ≤ 1)
    (x : L) (hx : Odd (orderOf x)) : x ^ 3 ∈ center L := by
  let K := L.map (MulAut.conj a).toMonoidHom
  have hLK : L ≠ K := fun h => ha (mem_normalizer_iff_map_conj_eq.mpr h.symm)
  have hc : ⁅L, K⁆ = ⊥ := hL.commutator_eq_bot_of_ne (hL.map_conj a) hLK
  have hKC : K ≤ centralizer (L : Set G) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  let y := (MulAut.conj a) (x : G)
  have hy : y ∈ K := mem_map_of_mem _ x.property
  have hxy : Commute y (x : G)⁻¹ :=
    ((mem_centralizer_iff.mp (hKC hy)) _ (L.inv_mem x.property)).symm
  have hxodd : Odd (orderOf (x : G)) := by simpa only [Subgroup.orderOf_coe] using hx
  have hyodd : Odd (orderOf y) := by
    change Odd (orderOf ((MulAut.conj a).toMonoidHom (x : G)))
    rw [orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective]
    exact hxodd
  have hdodd : Odd (orderOf (y * (x : G)⁻¹)) :=
    (hyodd.mul (by simpa only [orderOf_inv] using hxodd)).of_dvd_nat
      hxy.orderOf_mul_dvd_mul_orderOf
  have hdim : fixedCodim ρ (zpowers (y * (x : G)⁻¹)) ≤ 2 := by
    have h := fixedCodim_commutator_le_twice ρ a (x : G)
    change fixedCodim ρ (zpowers (y * (x : G)⁻¹)) ≤ _ at h
    omega
  have hcube := orderOf_dvd_iff_pow_eq_one.mp
    (orderOf_dvd_three_of_odd_fixedCodim_le_two ρ hf _ hdodd hdim)
  rw [hxy.mul_pow, inv_pow] at hcube
  have he : y ^ 3 = (x : G) ^ 3 := mul_inv_eq_one.mp hcube
  have hxC : (x : G) ^ 3 ∈ centralizer (L : Set G) := he ▸ (centralizer _).pow_mem (hKC hy) 3
  rw [mem_center_iff]
  intro z
  apply Subtype.ext
  exact (mem_centralizer_iff.mp hxC) z z.property

/-- Moving a genuine component requires at least two binary dimensions. -/
theorem two_le_fixedCodim_of_moving_component [Finite G]
    (ρ : Representation (ZMod 2) G V) (hf : Function.Injective ρ)
    {L : Subgroup G} (hL : Theory.GroupTheory.IsComponent G L)
    (a : G) (ha : a ∉ normalizer (L : Set G)) :
    2 ≤ fixedCodim ρ (zpowers a) := by
  by_contra hn
  have hd : fixedCodim ρ (zpowers a) ≤ 1 := by omega
  let : Theory.GroupTheory.IsQuasisimple L := hL.2
  let : IsSimpleGroup (L ⧸ center L) := Theory.GroupTheory.IsQuasisimple.simple
  let : Group.IsPerfect (L ⧸ center L) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center L))
  exact Group.IsPerfect.not_isSolvable (L ⧸ center L)
    (Theory.GroupTheory.isSolvable_center_quotient_of_odd_cube_central
      (odd_cube_central_of_moving_component_codim_le_one ρ hf hL a ha hd))

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V] (ρ : Representation (ZMod 2) G V)

/-- An offender of order two normalizes every genuine component. -/
theorem IsOffender.le_normalizer_component_of_card_two
    (hf : Function.Injective ρ) {A L : Subgroup G} (hA : IsOffender ρ A)
    (hcard : Nat.card A = 2) (hL : Theory.GroupTheory.IsComponent G L) :
    A ≤ normalizer (L : Set G) := by
  intro a ha
  by_contra haN
  have hdim := two_le_fixedCodim_of_moving_component ρ hf hL a haN
  have hfix : fixedSpace ρ A ≤ fixedSpace ρ (zpowers a) :=
    fixedSpace_antitone ρ (zpowers_le.mpr ha)
  have hm := Submodule.finrank_mono hfix
  have h1 := fixedCodim_add_finrank ρ A
  have h2 := fixedCodim_add_finrank ρ (zpowers a)
  have hoff := hA.2
  have hr : rank A = 1 := by norm_num [rank, hcard]
  omega

/-- The cyclic subgroup of an offending involution normalizes each component. -/
theorem mem_normalizer_component_of_order_two_offender
    (hf : Function.Injective ρ) {a : G} (ha : orderOf a = 2)
    (hoff : IsOffender ρ (zpowers a)) {L : Subgroup G}
    (hL : Theory.GroupTheory.IsComponent G L) : a ∈ normalizer (L : Set G) :=
  hoff.le_normalizer_component_of_card_two ρ hf (by rwa [Nat.card_zpowers]) hL
    (mem_zpowers a)

/-- The cyclic replacement branch in GLS 26.24 Step 2 is impossible.
All replacement premises follow from the original best offender. -/
theorem IsBestOffender.displacementCentralizer_ne_zpowers_of_moving_component
    (hf : Function.Injective ρ) {A L : Subgroup G} (hA : IsBestOffender ρ A)
    (hL : Theory.GroupTheory.IsComponent G L) {a : G} (ha : a ∈ A)
    (haN : a ∉ normalizer (L : Set G)) :
    displacementCentralizer ρ A ≠ zpowers a := by
  intro he
  let : IsElementaryAbelian 2 A := hA.1.2
  have ha1 : a ≠ 1 := fun h => haN (h ▸ (normalizer (L : Set G)).one_mem)
  have ha2 : orderOf a = 2 :=
    orderOf_eq_prime (elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha) ha1
  have hoff := (hA.displacementCentralizer_isBestOffender ρ).isOffender ρ
  rw [he] at hoff
  exact haN (mem_normalizer_component_of_order_two_offender ρ hf ha2 hoff hL)

/-- The actual replacement subgroup yields the quadratic four-group used in
GLS 26.24, without a remaining cyclic alternative. Local centralizer and
normalizer premises belong to the other steps of that theorem. -/
theorem IsBestOffender.exists_fourGroup_of_moving_component
    (hf : Function.Injective ρ) {A L : Subgroup G} (hA : IsBestOffender ρ A)
    (hL : Theory.GroupTheory.IsComponent G L) {a : G} (ha : a ∈ A)
    (haN : a ∉ normalizer (L : Set G))
    (hcent : displacementCentralizer ρ A ⊓ centralizer (L : Set G) = ⊥)
    (halt : displacementCentralizer ρ A = A ∨
      displacementCentralizer ρ A ≤ normalizer (L : Set G)) :
    ∃ c ∈ displacementCentralizer ρ A, c ≠ 1 ∧ c ≠ a ∧
      ∃ B : Subgroup G, B = closure ({a, c} : Set G) ∧
        B ≤ A ∧ IsElementaryTwo B ∧ Nat.card B = 4 ∧ a ∈ B ∧ c ∈ B ∧
        (∀ b ∈ B, ∀ v : V, ρ b (ρ a v - v) = ρ a v - v) ∧
        B ⊓ centralizer (L : Set G) = ⊥ := by
  exact (displacement_cyclic_or_exists_fourGroup ρ hA.1 ha haN
    (hA.displacementCentralizer_ne_bot ρ) hcent halt).resolve_left
      (hA.displacementCentralizer_ne_zpowers_of_moving_component ρ hf hL ha haN)

end Representation.BinaryOffender
