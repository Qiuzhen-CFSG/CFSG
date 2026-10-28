module

public import Theory.SpecificGroups.Suzuki.NonsplitTori
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups
public import Theory.GroupTheory.ConjugacyClassSize
import Mathlib.Data.Fintype.BigOperators

/-!
# Odd-order conjugacy classes of the concrete Suzuki group

For `m ≥ 1`, the number of actual odd-order conjugacy classes in
`SuzukiMatrixGroup m` is at most `q = 2^(2*m+1)`.

The root/torus partition puts every nonidentity odd-order element in a conjugate
of one of three fixed tori. For a nonidentity element of a torus `H`, the
centralizer in the full group is `H`. Consequently its conjugacy class in
`N(H)` has size `[N(H) : H]`. Inclusion injects this class into the fiber of
the ambient class map on `H`. Summing these fiber bounds gives at most
`(q-2)/2`, `(q+2^(m+1))/4`, and `(q-2^(m+1))/4` nonidentity classes from the
three tori. Their sum together with the identity is at most `q`. We keep the
arithmetic integral by multiplying the inequalities instead of dividing.

Sources: GLS3, Theorem 6.5.4 and its torus-normalizer discussion
(`refs/KGroup/GLS3/chapter6.tex`); Huppert--Blackburn, *Finite Groups III*,
XI.3.10(i)--(j), for the concrete torus partition assembled in `NonsplitTori`.
-/

open scoped BigOperators
open BenderSuzuki.MatrixGroups
noncomputable section

namespace BenderSuzuki.MatrixGroups.PRegularClassCounting
variable {G : Type*} [Group G] [Finite G]

/-- The ambient classes meeting the nonidentity elements of a subgroup. -/
private def torusClasses (H : Subgroup G) : Finset (ConjClasses G) := by
  classical
  let : Fintype H := Fintype.ofFinite H
  exact (Finset.univ.erase 1).image (fun x : H => ConjClasses.mk (x : G))

private lemma mem_torusClasses (H : Subgroup G) (c : ConjClasses G) :
    c ∈ torusClasses H ↔ ∃ x : G, x ∈ H ∧ x ≠ 1 ∧ ConjClasses.mk x = c := by
  classical
  simp only [torusClasses, Finset.mem_image, Finset.mem_erase, Finset.mem_univ, and_true]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, x.property, fun h => hx (Subtype.ext h), rfl⟩
  · rintro ⟨x, hx, hne, rfl⟩
    exact ⟨⟨x, hx⟩, fun h => hne (congrArg Subtype.val h), rfl⟩

omit [Finite G] in
private lemma normalizer_class_size (H : Subgroup G) (x : H)
    (hc : Subgroup.centralizer {(x : G)} = H) :
    Nat.card (ConjClasses.mk (Subgroup.inclusion H.le_normalizer x)).carrier =
      H.relIndex (Subgroup.normalizer H) := by
  rw [ConjClasses.nat_card_carrier_eq_index_centralizer]
  change (Subgroup.centralizer {Subgroup.inclusion H.le_normalizer x}).index =
    (H.subgroupOf (Subgroup.normalizer H)).index
  congr 1
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff]
  change y * Subgroup.inclusion H.le_normalizer x =
    Subgroup.inclusion H.le_normalizer x * y ↔ (y : G) ∈ H
  have hy := SetLike.ext_iff.mp hc (y : G)
  rw [Subgroup.mem_centralizer_singleton_iff] at hy
  exact Subtype.ext_iff.trans hy

omit [Finite G] in
private lemma normalizer_class_in_fiber (H : Subgroup G) (x : H) (hx : x ≠ 1) :
    Nonempty ((ConjClasses.mk (Subgroup.inclusion H.le_normalizer x)).carrier ↪
      {y : H // y ≠ 1 ∧ ConjClasses.mk (y : G) = ConjClasses.mk (x : G)}) := by
  let N := Subgroup.normalizer (H : Set G)
  let xN : N := Subgroup.inclusion H.le_normalizer x
  have conj (y : (ConjClasses.mk xN).carrier) : IsConj xN y.val :=
    ConjClasses.mk_eq_mk_iff_isConj.mp
      (ConjClasses.mem_carrier_iff_mk_eq.mp y.property).symm
  have hyH (y : (ConjClasses.mk xN).carrier) : (y.val : G) ∈ H := by
    obtain ⟨g, hg⟩ := isConj_iff.mp (conj y)
    rw [← hg]
    exact (Subgroup.mem_normalizer_iff.mp g.property _).mp x.property
  refine ⟨⟨fun y => ⟨⟨y.val, hyH y⟩, ?_, ?_⟩, ?_⟩⟩
  · intro h
    have he : (y.val : G) = 1 := congrArg (fun z : H => (z : G)) h
    have hi : IsConj (x : G) (1 : G) := he ▸ N.subtype.map_isConj (conj y)
    exact hx (Subtype.ext (isConj_one_left.mp hi))
  · exact (ConjClasses.mk_eq_mk_iff_isConj.mpr (N.subtype.map_isConj (conj y))).symm
  · intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => ((z.val : H) : G)) h

private lemma torusClasses_bound (H : Subgroup G)
    (hc : ∀ x ∈ H, x ≠ 1 → Subgroup.centralizer {x} = H) :
    (torusClasses H).card * H.relIndex (Subgroup.normalizer H) ≤ Nat.card H - 1 := by
  classical
  let : Fintype H := Fintype.ofFinite H
  let s : Finset H := Finset.univ.erase 1
  let f : H → ConjClasses G := fun x => ConjClasses.mk (x : G)
  have hfiber (c : ConjClasses G) (hc' : c ∈ s.image f) :
      H.relIndex (Subgroup.normalizer H) ≤ (s.filter (fun x => f x = c)).card := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hc'
    have hx1 : x ≠ 1 := (Finset.mem_erase.mp hx).1
    obtain ⟨e⟩ := normalizer_class_in_fiber H x hx1
    have he := Nat.card_le_card_of_injective e e.injective
    rw [normalizer_class_size H x (hc x x.property (fun h => hx1 (Subtype.ext h)))] at he
    have heq : {y : H | y ≠ 1 ∧ ConjClasses.mk (y : G) = ConjClasses.mk (x : G)} =
        (↑(s.filter (fun y => f y = f x)) : Set H) := by
      ext y
      simp [s, f]
    change _ ≤ Nat.card ↥{y : H | y ≠ 1 ∧ ConjClasses.mk (y : G) = ConjClasses.mk (x : G)} at he
    rw [heq] at he
    change _ ≤ Nat.card ↥(s.filter (fun y => f y = f x)) at he
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using he
  calc
    (torusClasses H).card * H.relIndex (Subgroup.normalizer H) =
        ∑ c ∈ s.image f, H.relIndex (Subgroup.normalizer H) := by simp [torusClasses, s, f]
    _ ≤ ∑ c ∈ s.image f, (s.filter (fun x => f x = c)).card :=
      Finset.sum_le_sum hfiber
    _ = s.card := (Finset.card_eq_sum_card_image f s).symm
    _ = Nat.card H - 1 := by simp [s, Nat.card_eq_fintype_card]

end BenderSuzuki.MatrixGroups.PRegularClassCounting

namespace BenderSuzuki.MatrixGroups.PRegularClassCounting
variable {G : Type*} [Group G] [Finite G]

private lemma mk_mem_torusClasses_of_mem_conjugate (H : Subgroup G) (g : G) {x : G}
    (hx : x ∈ H.map (MulAut.conj g).toMonoidHom) (hne : x ≠ 1) :
    ConjClasses.mk x ∈ torusClasses H := by
  obtain ⟨y, hy, rfl⟩ := hx
  apply (mem_torusClasses H _).mpr
  refine ⟨y, hy, ?_, ?_⟩
  · intro h
    exact hne (by simp [h])
  · exact ConjClasses.mk_eq_mk_iff_isConj.mpr (isConj_iff.mpr ⟨g, rfl⟩)

end BenderSuzuki.MatrixGroups.PRegularClassCounting

namespace BenderSuzuki.MatrixGroups
open PRegularClassCounting

private lemma split_normalizer_index (m : ℕ) (hm : 0 < m) :
    (SuzukiSplitTorus m).relIndex (Subgroup.normalizer (SuzukiSplitTorus m)) = 2 := by
  let N := Subgroup.normalizer (SuzukiSplitTorus m : Set (SuzukiMatrixGroup m))
  let A := (SuzukiSplitTorus m).subgroupOf N
  have hc : Nat.card A = Nat.card (SuzukiSplitTorus m) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv
  have h := A.card_mul_index
  rw [hc, suzukiSplitTorus_card m hm, suzukiSplitTorus_normalizer_card m hm] at h
  change A.index = 2
  have hp : 0 < Nat.card (SuzukiSplitTorus m) := Nat.card_pos
  rw [suzukiSplitTorus_card m hm] at hp
  nlinarith

private lemma odd_class_coverage (m : ℕ) (hm : 0 < m) (T : SuzukiNonsplitTorusPair m)
    (x : SuzukiMatrixGroup m) (hx : ¬ 2 ∣ orderOf x) :
    ConjClasses.mk x = ConjClasses.mk 1 ∨
    ConjClasses.mk x ∈ torusClasses (SuzukiSplitTorus m) ∨
    ConjClasses.mk x ∈ torusClasses T.plus ∨
    ConjClasses.mk x ∈ torusClasses T.minus := by
  by_cases hne : x = 1
  · exact Or.inl (congrArg ConjClasses.mk hne)
  obtain ⟨U, ⟨hU, hxU⟩, _⟩ := T.partition_existsUnique hm x hne
  rcases hU with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exfalso
    have hd := Subgroup.orderOf_dvd_natCard _ hxU
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
      suzukiRootSubgroup_card m hm] at hd
    have ho : Odd (orderOf x) := by
      simpa only [← Nat.not_even_iff_odd, even_iff_two_dvd] using hx
    have he : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
      ((ho.coprime_two_right.pow_right _).pow_right _) (dvd_refl _) hd
    exact hne (orderOf_eq_one_iff.mp he)
  · exact Or.inr (Or.inl (mk_mem_torusClasses_of_mem_conjugate _ g hxU hne))
  · exact Or.inr (Or.inr (Or.inl (mk_mem_torusClasses_of_mem_conjugate _ g hxU hne)))
  · exact Or.inr (Or.inr (Or.inr (mk_mem_torusClasses_of_mem_conjugate _ g hxU hne)))

/-- The actual odd-order conjugacy classes of the concrete Suzuki matrix group
number at most q, including Sz(8). -/
public theorem suzuki_odd_conjClasses_card_le (m : ℕ) (hm : 1 ≤ m) :
    Nat.card (ConjClasses.mk '' {g : SuzukiMatrixGroup m | ¬ 2 ∣ orderOf g}) ≤
      2 ^ (2 * m + 1) := by
  classical
  have hm' : 0 < m := hm
  obtain ⟨T⟩ := exists_suzukiNonsplitTorusPair m hm'
  let S := torusClasses (SuzukiSplitTorus m)
  let P := torusClasses T.plus
  let M := torusClasses T.minus
  let C := insert (ConjClasses.mk (1 : SuzukiMatrixGroup m)) (S ∪ P ∪ M)
  have hcover : (ConjClasses.mk '' {g : SuzukiMatrixGroup m | ¬ 2 ∣ orderOf g}) ⊆
      (C : Set (ConjClasses (SuzukiMatrixGroup m))) := by
    rintro c ⟨x, hx, rfl⟩
    have h := odd_class_coverage m hm' T x hx
    simpa only [C, S, P, M, Finset.mem_coe, Finset.mem_insert, Finset.mem_union,
      or_assoc] using h
  have hcard : Nat.card (ConjClasses.mk '' {g : SuzukiMatrixGroup m | ¬ 2 ∣ orderOf g}) ≤
      C.card := by
    have hi := Nat.card_le_card_of_injective (Set.inclusion hcover)
      (Set.inclusion_injective hcover)
    change _ ≤ Nat.card ↥C at hi
    simpa only [Nat.card_eq_finsetCard] using hi
  have hC : C.card ≤ 1 + S.card + P.card + M.card := by
    have h1 := Finset.card_insert_le (ConjClasses.mk (1 : SuzukiMatrixGroup m)) (S ∪ P ∪ M)
    have h2 := Finset.card_union_le (S ∪ P) M
    have h3 := Finset.card_union_le S P
    dsimp [C]
    omega
  have hS := torusClasses_bound (SuzukiSplitTorus m)
    (fun _ hx hne => suzukiSplitTorus_centralizer_eq m hm' hx hne)
  rw [split_normalizer_index m hm', suzukiSplitTorus_card m hm'] at hS
  have hP := torusClasses_bound T.plus (T.centralizers hm').1
  rw [T.plus_maximal.normalizer_index_eq_four hm', T.plus_card] at hP
  have hM := torusClasses_bound T.minus (T.centralizers hm').2
  rw [T.minus_maximal.normalizer_index_eq_four hm', T.minus_card] at hM
  have hpow : 2 * 2 ^ m ≤ (2 : ℕ) ^ (2 * m + 1) := by
    calc
      2 * 2 ^ m = (2 : ℕ) ^ (m + 1) := by rw [pow_succ, Nat.mul_comm]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hr : 0 < (2 : ℕ) ^ m := pow_pos (by decide) _
  dsimp [S, P, M] at hC
  omega

end BenderSuzuki.MatrixGroups
