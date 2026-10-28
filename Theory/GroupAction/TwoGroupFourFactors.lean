module
public import Theory.GroupTheory.IrreducibleFourResidual
public import Mathlib.GroupTheory.Index

/-!
# Two-group actions on joins of subgroups of order four

A two-group acting on a group of order four fixes a nonidentity element.
The point-stabilizer bound therefore makes its image have order at most
two. Restriction to two invariant four-subgroups embeds the action on
their join into the product of those two images. The resulting image has
order at most four and every actor's square centralizes the join. Neither
commutativity nor disjointness of the factors is needed. Sylow conjugacy
then rules out an element of order four in the action of any overgroup
containing this Sylow and preserving the same join. The ambient version
retains the literal centralizer and subgroup embeddings.

Source application: the original Sylow action on V₂C_I(Z(U)^g) in the
proof of Aschbacher--Smith 12.9.4, printed p.860 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

private theorem two_group_four_action_card
    (Q A : Subgroup G) (hQ : IsPGroup 2 Q) (hA : Nat.card A = 4)
    (hn : Q ≤ normalizer (A : Set G)) :
    Nat.card (A.normalizerMonoidHom.comp (inclusion hn)).range ≤ 2 := by
  let f : Q →* MulAut A := A.normalizerMonoidHom.comp (inclusion hn)
  let : MulAction Q A := MulAction.compHom A f
  have hfix : (1:A) ∈ MulAction.fixedPoints Q A := fun q => map_one (f q)
  obtain ⟨z,hz,hzne⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point A
    (by rw [hA]; decide) hfix
  exact card_mulAut_subgroup_le_two_of_fixed_point hA z hzne.symm f.range
    (by rintro _ ⟨q,rfl⟩; exact hz q)

omit [Finite G] in
private theorem centralizer_join (A B : Subgroup G) :
    centralizer ((A ⊔ B : Subgroup G) : Set G) =
      centralizer (A : Set G) ⊓ centralizer (B : Set G) := by
  apply le_antisymm (le_inf (centralizer_le (show A ≤ A ⊔ B from le_sup_left))
    (centralizer_le (show B ≤ A ⊔ B from le_sup_right)))
  apply le_centralizer_iff.mpr
  exact sup_le (le_centralizer_iff.mp inf_le_left) (le_centralizer_iff.mp inf_le_right)

private theorem pow_two_of_card_le_two {D : Type*} [Group D] [Finite D]
    (hc : Nat.card D ≤ 2) (d : D) : d ^ 2 = 1 := by
  have hp : 0 < Nat.card D := Nat.card_pos
  have hh := pow_card_eq_one' (x := d)
  have hcases : Nat.card D = 1 ∨ Nat.card D = 2 := by omega
  rcases hcases with he | he
  · rw [he,pow_one] at hh
    rw [hh,one_pow]
  · simpa only [he] using hh

/-- A two-group preserving two subgroups of order four has an action of
order at most four on their join, and the square of every actor acts trivially. -/
theorem two_group_four_factors_action
    (Q A B : Subgroup G) (hQ : IsPGroup 2 Q)
    (hA : Nat.card A = 4) (hB : Nat.card B = 4)
    (hQA : Q ≤ normalizer (A : Set G)) (hQB : Q ≤ normalizer (B : Set G)) :
    (centralizer ((A ⊔ B : Subgroup G) : Set G)).relIndex Q ≤ 4 ∧
      ∀ q ∈ Q, q ^ 2 ∈ centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  let f : Q →* MulAut A := A.normalizerMonoidHom.comp (inclusion hQA)
  let k : Q →* MulAut B := B.normalizerMonoidHom.comp (inclusion hQB)
  let j := f.prod k
  have hf : Nat.card f.range ≤ 2 := two_group_four_action_card Q A hQ hA hQA
  have hk : Nat.card k.range ≤ 2 := two_group_four_action_card Q B hQ hB hQB
  have hker (D : Subgroup G) (hn : Q ≤ normalizer (D : Set G)) :
      (D.normalizerMonoidHom.comp (inclusion hn)).ker = (centralizer (D : Set G)).subgroupOf Q := by
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  have hjker : j.ker = (centralizer ((A ⊔ B : Subgroup G) : Set G)).subgroupOf Q := by
    rw [MonoidHom.ker_prod,hker A hQA,hker B hQB,centralizer_join]
    rfl
  have hjrange : j.range ≤ f.range.prod k.range := by
    rintro _ ⟨q,rfl⟩
    exact ⟨⟨q,rfl⟩,⟨q,rfl⟩⟩
  have hjcard : Nat.card j.range ≤ 4 := by
    have hh := card_le_of_le hjrange
    rw [Nat.card_congr (prodEquiv f.range k.range).toEquiv,Nat.card_prod] at hh
    nlinarith
  refine ⟨?_,?_⟩
  · change ((centralizer ((A ⊔ B : Subgroup G) : Set G)).subgroupOf Q).index ≤ 4
    rw [←hjker,index_ker]
    exact hjcard
  · intro q hq
    have hqj : (⟨q,hq⟩ : Q)^2 ∈ j.ker := by
      change j ((⟨q,hq⟩ : Q)^2) = 1
      rw [map_pow]
      exact Prod.ext (congrArg Subtype.val (pow_two_of_card_le_two hf (f.rangeRestrict ⟨q,hq⟩)))
        (congrArg Subtype.val (pow_two_of_card_le_two hk (k.rangeRestrict ⟨q,hq⟩)))
    rw [hjker] at hqj
    exact hqj
end Subgroup

namespace Sylow
variable {G H : Type*} [Group G] [Finite G] [Group H]

/-- Squares on the original Sylow image detect whether an image element
of order dividing four already has square one. -/
theorem image_square_eq_one_of_fourth_power
    (S : Sylow 2 G) (f : G →* H)
    (hS : ∀ s ∈ S, f s ^ 2 = 1) (x : G) (hx : f x ^ 4 = 1) : f x ^ 2 = 1 := by
  let : Finite f.range := Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  let q := f.rangeRestrict
  let P : Sylow 2 f.range := S.mapSurjective (f := q) f.rangeRestrict_surjective
  have hx' : q x ^ 4 = 1 := Subtype.ext hx
  have hp : IsPGroup 2 (zpowers (q x)) := IsPGroup.of_card_dvd_pow (n := 2) (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hx')
  obtain ⟨Q,hQ⟩ := hp.exists_le_sylow
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq f.range Q P
  have hmem : MulAut.conj a (q x) ∈ P := by
    rw [←ha]
    exact mem_map_of_mem (MulAut.conj a).toMonoidHom (hQ (mem_zpowers (q x)))
  have hP (y : f.range) (hy : y ∈ P) : y ^ 2 = 1 := by
    obtain ⟨s,hs,rfl⟩ := hy
    exact Subtype.ext (hS s hs)
  have hh : q x ^ 2 = 1 := (MulAut.conj a).injective (by
    simpa only [map_pow,map_one] using hP _ hmem)
  exact congrArg Subtype.val hh
end Sylow

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- The same test expressed on the literal ambient centralizer of an
invariant subgroup. It keeps the original overgroup and Sylow embeddings. -/
theorem fourth_power_centralizes_implies_square
    (T : Sylow 2 G) (Y E : Subgroup G) (hTY : (T : Subgroup G) ≤ Y)
    (hYE : Y ≤ normalizer (E : Set G))
    (hT : ∀ t ∈ (T : Subgroup G), t ^ 2 ∈ centralizer (E : Set G)) :
    ∀ y ∈ Y, y ^ 4 ∈ centralizer (E : Set G) → y ^ 2 ∈ centralizer (E : Set G) := by
  let f : Y →* MulAut E := E.normalizerMonoidHom.comp (inclusion hYE)
  have hk : f.ker = (centralizer (E : Set G)).subgroupOf Y := by
    rw [←MonoidHom.comap_ker,normalizerMonoidHom_ker]
    rfl
  intro y hy h4
  have hpow : f ⟨y,hy⟩ ^ 4 = 1 := by
    rw [←map_pow]
    change (⟨y,hy⟩ : Y)^4 ∈ f.ker
    rw [hk]
    exact h4
  have htwo := (T.subtype hTY).image_square_eq_one_of_fourth_power f
    (fun t ht => by
      rw [←map_pow]
      change t ^ 2 ∈ f.ker
      rw [hk]
      exact hT t ht) ⟨y,hy⟩ hpow
  rw [←map_pow] at htwo
  have hh : (⟨y,hy⟩ : Y)^2 ∈ f.ker := htwo
  rw [hk] at hh
  exact hh
end Subgroup
