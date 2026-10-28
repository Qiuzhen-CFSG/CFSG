module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.PureFirstNormalizers.AllRowTwo.CoreGeometry
public import Theory.ElementaryAbelian.ExtraspecialPrimeAbelianBound
/-!
# Elementary intersections of distinct first-class point cores

In each extraspecial point core, every square lies in the central involution
line. Distinct points have disjoint lines, so their core intersection has
exponent two and is elementary. The extraspecial pairing bounds its order by
128. This also bounds the canonical intersection at all points of X and
contains every all-row-two elementary overgroup of X simultaneously.

These arguments use the literal embedded two-cores and the certified native
centralizer order. They supply the finite ambient reduction for the canonical
supergroup approach to Kleidman--Wilson (1988), Corollary 1.2.2(a) and
Section 2.1, pp.488--489. No eight/sixteen census or named-local normalizer
placement is inferred from the cardinality bound.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
open ElementaryNormalizerCover
attribute [local irreducible] modelGroup matrixA matrixB

private theorem point_core_structure (x : Model) (hx : IsConj a x) :
    IsExtraspecial 2 ((centralizer ({x} : Set Model)).pCoreIn 2) ∧
      (center ((centralizer ({x} : Set Model)).pCoreIn 2)).map
        ((centralizer ({x} : Set Model)).pCoreIn 2).subtype = zpowers x ∧
      Nat.card ((centralizer ({x} : Set Model)).pCoreIn 2) = 8192 := by
  obtain ⟨g,hg⟩ := isConj_iff.mp hx
  have he : firstCore.map (MulAut.conj g).toMonoidHom =
      (centralizer ({x} : Set Model)).pCoreIn 2 := by
    rw [firstCore_conjugate]
    change (centralizer ({g*a*g⁻¹} : Set Model)).pCoreIn 2 = _
    rw [hg]
  have hE : IsExtraspecial 2 ((centralizer ({x} : Set Model)).pCoreIn 2) := by
    rw [← he]
    exact IsExtraspecial.of_mulEquiv
      (firstCore.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
      firstCore_extraspecial
  have hx1 : x ≠ 1 := by
    intro hx1
    have ha := isConj_one_left.mp (hx1 ▸ hx)
    have ho := orderOf_a
    simp [ha] at ho
  have hxR : x ∈ (centralizer ({x} : Set Model)).pCoreIn 2 := by
    rw [← he]
    exact ⟨a,a_mem_firstCore,hg⟩
  let R := (centralizer ({x} : Set Model)).pCoreIn 2
  let := hE
  have hxZ : (⟨x,hxR⟩ : R) ∈ center R := by
    apply mem_center_iff.mpr
    intro u
    apply Subtype.ext
    exact mem_centralizer_singleton_iff.mp (pCoreIn_le 2 _ u.property)
  refine ⟨hE,?_,?_⟩
  · symm
    apply eq_of_le_of_card_ge (zpowers_le.mpr (mem_map_of_mem R.subtype hxZ))
    rw [card_map_of_injective R.subtype_injective,IsExtraspecial.center_order_p 2 R,
      Nat.card_zpowers]
    have ho : orderOf x = orderOf a :=
      (congrArg orderOf hg).symm.trans ((MulAut.conj g).orderOf_eq a)
    change 2 ≤ orderOf x
    rw [ho,orderOf_a]

  · rw [← he,card_map_of_injective (MulAut.conj g).injective]
    exact (card_map_of_injective InvolutionCentralizers.First.centralizer.subtype_injective).trans
      InvolutionCentralizers.First.centralizer_twoCore_card

private theorem point_core_square (x : Model) (hx : IsConj a x) (u : Model)
    (hu : u ∈ (centralizer ({x} : Set Model)).pCoreIn 2) : u^2 = 1 ∨ u^2 = x := by
  obtain ⟨hE,hZ,_⟩ := point_core_structure x hx
  let R := (centralizer ({x} : Set Model)).pCoreIn 2
  let := hE
  have hmem : u^2 ∈ zpowers x := by
    rw [← hZ]
    exact mem_map_of_mem R.subtype
      ((IsExtraspecial.quotient_elementary_abelian 2 R).sq_mem_center_of_central_quotient ⟨u,hu⟩)
  have ho : orderOf x = 2 := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hx
    exact ((congrArg orderOf hg).symm.trans ((MulAut.conj g).orderOf_eq a)).trans orderOf_a
  classical
  rw [mem_zpowers_iff_mem_range_orderOf,ho] at hmem
  obtain ⟨n,hn,he⟩ := Finset.mem_image.mp hmem
  have hn2 : n < 2 := Finset.mem_range.mp hn
  interval_cases n <;> simp_all

theorem point_core_intersection_elementary (x y : Model)
    (hx : IsConj a x) (hy : IsConj a y) (hxy : x ≠ y) :
    IsElementaryAbelian 2
      ((centralizer ({x} : Set Model)).pCoreIn 2 ⊓
       (centralizer ({y} : Set Model)).pCoreIn 2 : Subgroup Model) := by
  let R := ((centralizer ({x} : Set Model)).pCoreIn 2 ⊓
       (centralizer ({y} : Set Model)).pCoreIn 2 : Subgroup Model)
  have hs (u : R) : u^2 = 1 := by
    apply Subtype.ext
    rcases point_core_square x hx u u.property.1 with h | h
    · exact h
    rcases point_core_square y hy u u.property.2 with h' | h'
    · exact h'
    exact (hxy (h.symm.trans h')).elim
  have hm (u v : R) : u*v = v*u := by
    have hi (w : R) : w⁻¹ = w := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs w)
    have he := hi (u*v)
    rw [mul_inv_rev,hi u,hi v] at he
    exact he.symm
  exact {
    toIsMulCommutative := IsMulCommutative.of_comm hm
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs }

theorem point_core_intersection_card_le (x y : Model)
    (hx : IsConj a x) (hy : IsConj a y) (hxy : x ≠ y) :
    Nat.card ((centralizer ({x} : Set Model)).pCoreIn 2 ⊓
       (centralizer ({y} : Set Model)).pCoreIn 2 : Subgroup Model) ≤ 128 := by
  let Q := (centralizer ({x} : Set Model)).pCoreIn 2
  let I := (Q ⊓ (centralizer ({y} : Set Model)).pCoreIn 2 : Subgroup Model)
  obtain ⟨hE,_,hcard⟩ := point_core_structure x hx
  let := hE
  let : IsElementaryAbelian 2 I := point_core_intersection_elementary x y hx hy hxy
  let : IsElementaryAbelian 2 (I.subgroupOf Q) := IsElementaryAbelian.subgroupOf inf_le_left
  have hsq := extraspecial_prime_abelian_card_sq_le_any (p := 2) (I.subgroupOf Q)
  rw [natCard_subgroupOf_eq I Q inf_le_left] at hsq
  change Nat.card I ^ 2 ≤ 2 * Nat.card Q at hsq
  change Nat.card Q = 8192 at hcard
  rw [hcard] at hsq
  change Nat.card I ≤ 128
  nlinarith

private theorem independent_pair (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) :
    ∃ x ∈ X, ∃ y ∈ X, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  have hX : X ≠ ⊥ := by intro he; simp [he] at hcard
  obtain ⟨x,hx⟩ := ne_bot_iff_exists_ne_one.mp hX
  have hx1 : (x : Model) ≠ 1 := fun he => hx (Subtype.ext he)
  have hx2 : orderOf (x : Model) = 2 := orderOf_eq_prime
    (elemPow_eq_one_of_isElementaryAbelian (p := 2) _ x.property) hx1
  have hn : ¬ X ≤ zpowers (x : Model) := by
    intro hh
    have h := Nat.le_of_dvd Nat.card_pos (card_dvd_of_le hh)
    rw [Nat.card_zpowers,hx2] at h
    omega
  obtain ⟨y,hy,hyn⟩ := SetLike.not_le_iff_exists.mp hn
  exact ⟨x,x.property,y,hy,hx1,
    (fun he => hyn (he ▸ one_mem _)),
    (fun he => hyn (he ▸ mem_zpowers (x : Model)))⟩


/-- At least two nonidentity points make the full canonical intersection elementary. -/
theorem commonCore_elementary (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    IsElementaryAbelian 2 (commonCore X) := by
  obtain ⟨x,hx,y,hy,hx1,hy1,hxy⟩ := independent_pair X hcard
  let : IsElementaryAbelian 2
      ((centralizer ({x} : Set Model)).pCoreIn 2 ⊓
        (centralizer ({y} : Set Model)).pCoreIn 2 : Subgroup Model) :=
    point_core_intersection_elementary x y (hpure x hx hx1) (hpure y hy hy1) hxy
  exact IsElementaryAbelian.of_le
    (le_inf (commonCore_le_point_core X x hx hx1) (commonCore_le_point_core X y hy hy1))

/-- The whole canonical intersection has at most 128 elements, independently
of a matrix enumeration or the maximal-two-local hypothesis. -/
theorem commonCore_card_le (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hcard : 4 < Nat.card X) (hpure : ∀ x ∈ X, x ≠ 1 → IsConj a x) :
    Nat.card (commonCore X) ≤ 128 := by
  obtain ⟨x,hx,y,hy,hx1,hy1,hxy⟩ := independent_pair X hcard
  exact (card_le_of_le
    (le_inf (commonCore_le_point_core X x hx hx1) (commonCore_le_point_core X y hy hy1))).trans
    (point_core_intersection_card_le x y (hpure x hx hx1) (hpure y hy hy1) hxy)

/-- Every all-row-two pure elementary overgroup lies in the same actual
canonical core intersection. Thus one finite container controls the whole
family, not only the originally chosen subgroup. -/
theorem overgroup_le_commonCore (X Y : Subgroup Model) [IsElementaryAbelian 2 Y]
    (hXY : X ≤ Y) (hpure : ∀ y ∈ Y, y ≠ 1 → IsConj a y)
    (hno : ¬ ∃ g : Model, PureTwoA.NativePair.nativePair.map
      (MulAut.conj g).toMonoidHom ≤ Y) : Y ≤ commonCore X := by
  intro u hu
  apply (mem_commonCore_iff X u).mpr
  intro x hx hx1
  exact le_point_core Y hpure hno x (hXY hx) hx1 hu

end Janko4.LocalStructure.PureFirstNormalizers.AllRowTwo
