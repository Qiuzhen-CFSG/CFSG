module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.SourceData
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.RootPairs
public import Theory.SpecificGroups.PSL3Four.CentralCover.FixedResiduals.ProjectiveGraphField.Monomial

/-!
# Lifting unitary Sylow coordinates to a double-cover root presentation

The full preimage of the specified projective Sylow subgroup is a Sylow
subgroup of the cover. Source involution lifting makes both lifted root
planes elementary abelian. Their intersection is central, because the two
planes generate the full preimage; the derived subgroup lies in that
intersection and has exponent two.

Choose lifts of the first-root vectors with coordinates 1 and ω. These and
their graph-field images generate modulo the central intersection. Quotienting
by their four cross commutators therefore gives an abelian group, proving the
derived-generation field. The actual projection computes the three diagonal
commutators as highest-root coordinate 1 and the off-diagonal commutators as
ω and ω², whose sum is 1.

The result is conditional on `InvolutionLifting c` and an actual
`UnitarySylowModel`. It constructs every presentation field and imposes no
additional displacement or presentation hypothesis. Supplying those two
inputs and the subsequent Sylow-transfer argument belongs to the consumer.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(3b), printed pp.409–410; the center-C₂ graph-field case of
16.4.9(2), printed p.1191.
-/

open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.RootLifting
open SylowModel ProjectiveGraphField

private theorem field_cases (w : F) (hw0 : w ≠ 0) (hw1 : w ≠ 1) (t : F) :
    t = 0 ∨ t = 1 ∨ t = w ∨ t = 1 + w := by
  classical
  let := Fintype.ofFinite F
  have h01w : (1 : F) + w ≠ 0 := by
    intro h
    have he : (1 : F) = -w := add_eq_zero_iff_eq_neg.mp h
    rw [CharTwo.neg_eq] at he
    exact hw1 he.symm
  have h1w1 : (1 : F) + w ≠ 1 := by simpa using hw0
  have h1ww : (1 : F) + w ≠ w := by simp
  have hcard : ({0, 1, w, 1 + w} : Finset F).card = Fintype.card F := by
    rw [← Nat.card_eq_fintype_card, card_F]
    simp [hw0.symm, hw1.symm, h01w.symm, h1w1.symm, h1ww.symm]
  have ht : t ∈ ({0, 1, w, 1 + w} : Finset F) := by
    rw [Finset.eq_univ_of_card _ hcard]
    exact Finset.mem_univ _
  simpa only [Finset.mem_insert, Finset.mem_singleton] using ht

private theorem inv_x (u : U) : u⁻¹.x = -u.x := rfl
private theorem inv_y (u : U) : u⁻¹.y = -u.y := rfl
private theorem inv_c (u : U) : u⁻¹.c = u.x * u.y - u.c := rfl

private theorem comm_coordinates (u v : U) :
    ⁅u, v⁆ = ⟨0, 0, u.x * v.y + v.x * u.y⟩ := by
  apply U.ext
  · simp [commutatorElement_def, inv_x]
  · simp [commutatorElement_def, inv_y]
  · simp only [commutatorElement_def, mul_c, mul_x, inv_c, inv_x, inv_y]
    calc
      _ = u.x * v.y - v.x * u.y := by ring
      _ = _ := by rw [sub_eq_add_neg, CharTwo.neg_eq]

private theorem square_of_axis (u : U) (hu : u.x = 0 ∨ u.y = 0) : u ^ 2 = 1 := by
  apply U.ext <;> simp only [pow_two, mul_x, mul_y, mul_c, one_x, one_y, one_c,
    CharTwo.add_self_eq_zero]
  rcases hu with h | h <;> simp [h]

private theorem omega_square_ne_one : omega ^ 2 ≠ 1 := by
  intro h
  have h' := congrArg (fun t : F => t ^ 2) h
  rw [← pow_mul, show (2 : ℕ) * 2 = 4 from rfl, pow_four, one_pow] at h'
  exact omega_ne_one h'

private theorem nonzero_cube (t : F) (ht : t ≠ 0) : t ^ 3 = 1 := by
  apply mul_left_cancel₀ ht
  simpa only [← pow_succ', mul_one] using pow_four t

private theorem omega_add_square : omega + omega ^ 2 = 1 := by
  have hc : (omega - 1) * (omega ^ 2 + omega + 1) = 0 := by
    calc
      _ = omega ^ 3 - 1 := by ring
      _ = 0 := by rw [omega_cube, sub_self]
  have h0 : omega - 1 ≠ 0 := sub_ne_zero.mpr omega_ne_one
  have h := (mul_eq_zero.mp hc).resolve_left h0
  have h' : omega ^ 2 + omega = 1 := by
    have he : omega ^ 2 + omega = -(1 : F) := add_eq_zero_iff_eq_neg.mp h
    simpa only [CharTwo.neg_eq] using he
  simpa only [add_comm] using h'

variable {K : Type*} [Group K]

private theorem commute_of_three_squares (s t : K)
    (hs : s ^ 2 = 1) (ht : t ^ 2 = 1) (hst : (s * t) ^ 2 = 1) : Commute s t := by
  have hi (u : K) (hu : u ^ 2 = 1) : u⁻¹ = u :=
    inv_eq_of_mul_eq_one_right (by simpa only [pow_two] using hu)
  change s * t = t * s
  calc
    s * t = (s * t)⁻¹ := (hi _ hst).symm
    _ = t * s := by rw [_root_.mul_inv_rev, hi _ ht, hi _ hs]

/-- Lifts in either elementary root plane commute. -/
private theorem commute_axis (q : K →* U)
    (hsq : ∀ k : K, (q k) ^ 2 = 1 → k ^ 2 = 1) (s t : K)
    (h : ((q s).x = 0 ∧ (q t).x = 0) ∨ ((q s).y = 0 ∧ (q t).y = 0)) :
    Commute s t := by
  apply commute_of_three_squares
  · apply hsq
    apply square_of_axis
    exact h.imp And.left And.left
  · apply hsq
    apply square_of_axis
    exact h.imp And.right And.right
  · apply hsq
    rw [map_mul]
    apply square_of_axis
    rcases h with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · exact Or.inl (by simp [hs, ht])
    · exact Or.inr (by simp [hs, ht])

/-- The intersection of the lifted root planes centralizes the full preimage. -/
private theorem precenter_le_center (q : K →* U) (hq : Function.Surjective q)
    (hsq : ∀ k : K, (q k) ^ 2 = 1 → k ^ 2 = 1) :
    (center U).comap q ≤ center K := by
  intro z hz
  have hz' := (mem_center_U (q z)).mp hz
  apply mem_center_iff.mpr
  intro v
  obtain ⟨v₁, hv₁⟩ := hq ⟨(q v).x, 0, 0⟩
  obtain ⟨v₂, hv₂⟩ := hq ⟨0, (q v).y, (q v).c⟩
  have hv : q (v₂ * v₁) = q v := by
    rw [map_mul, hv₁, hv₂]
    apply U.ext <;> simp
  let k := v * (v₂ * v₁)⁻¹
  have hk : q k = 1 := by
    dsimp [k]
    rw [map_mul, map_inv, hv, mul_inv_cancel]
  have hkz : Commute z k := commute_axis q hsq z k (Or.inl ⟨hz'.1, by rw [hk]; rfl⟩)
  have h₁ : Commute z v₁ := commute_axis q hsq z v₁
    (Or.inr ⟨hz'.2, by rw [hv₁]⟩)
  have h₂ : Commute z v₂ := commute_axis q hsq z v₂
    (Or.inl ⟨hz'.1, by rw [hv₂]⟩)
  have h := (hkz.mul_right (h₂.mul_right h₁)).symm.eq
  simpa only [k, inv_mul_cancel_right] using h

/-- Every commutator lies over the highest-root direction. -/
private theorem derived_le_precenter (q : K →* U) :
    _root_.commutator K ≤ (center U).comap q := by
  apply commutator_le.mpr
  intro u _ v _
  change q ⁅u, v⁆ ∈ center U
  rw [map_commutatorElement, comm_coordinates, mem_center_U]
  exact ⟨rfl, rfl⟩

private theorem lifted_class_two (q : K →* U) (hq : Function.Surjective q)
    (hsq : ∀ k : K, (q k) ^ 2 = 1 → k ^ 2 = 1) :
    _root_.commutator K ≤ center K :=
  (derived_le_precenter q).trans (precenter_le_center q hq hsq)

private theorem lifted_derived_square (q : K →* U)
    (hsq : ∀ k : K, (q k) ^ 2 = 1 → k ^ 2 = 1)
    (z : K) (hz : z ∈ _root_.commutator K) : z ^ 2 = 1 := by
  apply hsq
  exact square_of_axis _ (Or.inl ((mem_center_U _).mp (derived_le_precenter q hz)).1)

/-- Two marked roots span either additive coordinate over the prime field. -/
private theorem coordinate_span (q : K →* U) (L : Subgroup K) (u v : K)
    (hu : u ∈ L) (hv : v ∈ L) (w : F) (hw0 : w ≠ 0) (hw1 : w ≠ 1)
    (i : U → F) (hi : ∀ s t, i (s * t) = i s + i t) (hi1 : i 1 = 0)
    (hui : i (q u) = 1) (hvi : i (q v) = w) (t : F) :
    ∃ k ∈ L, i (q k) = t := by
  rcases field_cases w hw0 hw1 t with rfl | rfl | rfl | rfl
  · exact ⟨1, L.one_mem, by rw [map_one, hi1]⟩
  · exact ⟨u, hu, hui⟩
  · exact ⟨v, hv, hvi⟩
  · exact ⟨u * v, L.mul_mem hu hv, by rw [map_mul, hi, hui, hvi]⟩

/-- The four simple-root images generate modulo the common central direction. -/
private theorem root_generation (q : K →* U) (hq : Function.Surjective q)
    (hsq : ∀ k : K, (q k) ^ 2 = 1 → k ^ 2 = 1)
    (x y bx by' : K)
    (hx : q x = ⟨1, 0, 0⟩) (hy : q y = ⟨omega, 0, 0⟩)
    (hbx : q bx = ⟨0, 1, 0⟩) (hby : q by' = ⟨0, omega ^ 2, 0⟩)
    (L : Subgroup K) (hZ : center K ≤ L)
    (hxL : x ∈ L) (hyL : y ∈ L) (hbxL : bx ∈ L) (hbyL : by' ∈ L) : L = ⊤ := by
  let A : Subgroup K :=
    { carrier := {k | (q k).y = 0}
      one_mem' := by simp
      mul_mem' := by
        intro s t hs ht
        change (q s).y = 0 at hs
        change (q t).y = 0 at ht
        change (q (s * t)).y = 0
        simp [hs, ht]
      inv_mem' := by
        intro s hs
        change (q s).y = 0 at hs
        change (q s⁻¹).y = 0
        rw [map_inv, inv_y, hs, neg_zero] }
  let B : Subgroup K :=
    { carrier := {k | (q k).x = 0}
      one_mem' := by simp
      mul_mem' := by
        intro s t hs ht
        change (q s).x = 0 at hs
        change (q t).x = 0 at ht
        change (q (s * t)).x = 0
        simp [hs, ht]
      inv_mem' := by
        intro s hs
        change (q s).x = 0 at hs
        change (q s⁻¹).x = 0
        rw [map_inv, inv_x, hs, neg_zero] }
  have hxA : x ∈ A := by change (q x).y = 0; rw [hx]
  have hyA : y ∈ A := by change (q y).y = 0; rw [hy]
  have hbxB : bx ∈ B := by change (q bx).x = 0; rw [hbx]
  have hbyB : by' ∈ B := by change (q by').x = 0; rw [hby]
  apply top_unique
  intro k _
  obtain ⟨u, hu, hux⟩ := coordinate_span q (L ⊓ A) x y ⟨hxL, hxA⟩ ⟨hyL, hyA⟩
    omega omega_ne_zero omega_ne_one U.x mul_x one_x
    (by rw [hx]) (by rw [hy]) (q k).x
  obtain ⟨v, hv, hvy⟩ := coordinate_span q (L ⊓ B) bx by' ⟨hbxL, hbxB⟩ ⟨hbyL, hbyB⟩
    (omega ^ 2) (pow_ne_zero _ omega_ne_zero) omega_square_ne_one U.y mul_y one_y
    (by rw [hbx]) (by rw [hby]) (q k).y
  have huz : (q u).y = 0 := hu.2
  have hvz : (q v).x = 0 := hv.2
  have hd : k * (u * v)⁻¹ ∈ (center U).comap q := by
    change q (k * (u * v)⁻¹) ∈ center U
    rw [mem_center_U]
    simp [map_mul, map_inv, inv_x, inv_y, hux, hvy, huz, hvz]
  have h := L.mul_mem (hZ (precenter_le_center q hq hsq hd)) (L.mul_mem hu.1 hv.1)
  simpa only [inv_mul_cancel_right] using h

/-- Commutators of generators suffice when the remaining generators are central. -/
private theorem derived_le_of_central_generators (S : Set K) (D : Subgroup K) [D.Normal]
    (hgen : closure (S ∪ (center K : Set K)) = ⊤)
    (hcomm : ∀ u ∈ S, ∀ v ∈ S, ⁅u, v⁆ ∈ D) : _root_.commutator K ≤ D := by
  let q := QuotientGroup.mk' D
  have hZ (z : K) (hz : z ∈ center K) : q z ∈ center (K ⧸ D) := by
    apply mem_center_iff.mpr
    intro w
    obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective D w
    simpa only [map_mul] using congrArg q (mem_center_iff.mp hz v)
  have hpair : ∀ u ∈ q '' (S ∪ (center K : Set K)),
      ∀ v ∈ q '' (S ∪ (center K : Set K)), u * v = v * u := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    rcases hu with hu | hu
    · rcases hv with hv | hv
      · apply commutatorElement_eq_one_iff_mul_comm.mp
        rw [← map_commutatorElement]
        exact (QuotientGroup.eq_one_iff _).mpr (hcomm u hu v hv)
      · exact mem_center_iff.mp (hZ v hv) (q u)
    · exact (mem_center_iff.mp (hZ u hu) (q v)).symm
  have htop : closure (q '' (S ∪ (center K : Set K))) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen]
    exact map_top_of_surjective q (QuotientGroup.mk'_surjective D)
  let : IsMulCommutative (closure (q '' (S ∪ (center K : Set K)))) :=
    isMulCommutative_closure hpair
  apply Normal.quotient_commutative_iff_commutator_le.mp
  refine ⟨⟨fun u v => ?_⟩⟩
  have hu : u ∈ closure (q '' (S ∪ (center K : Set K))) := by rw [htop]; trivial
  have hv : v ∈ closure (q '' (S ∪ (center K : Set K))) := by rw [htop]; trivial
  exact setLike_mul_comm hu hv

/-- Only the four cross commutators are needed for the derived subgroup. -/
private theorem root_derived_generated (q : K →* U) (hq : Function.Surjective q)
    (hsq : ∀ k : K, (q k) ^ 2 = 1 → k ^ 2 = 1)
    (x y bx by' : K)
    (hx : q x = ⟨1, 0, 0⟩) (hy : q y = ⟨omega, 0, 0⟩)
    (hbx : q bx = ⟨0, 1, 0⟩) (hby : q by' = ⟨0, omega ^ 2, 0⟩) :
    _root_.commutator K ≤ closure ({⁅bx, x⁆, ⁅bx, y⁆, ⁅by', x⁆, ⁅by', y⁆} : Set K) := by
  let D := closure ({⁅bx, x⁆, ⁅bx, y⁆, ⁅by', x⁆, ⁅by', y⁆} : Set K)
  have hD : D ≤ center K := by
    apply (closure_le _).mpr
    intro z hz
    have hc := lifted_class_two q hq hsq
    rcases hz with rfl | rfl | rfl | rfl <;>
      exact hc (commutator_mem_commutator (mem_top _) (mem_top _))
  let : D.Normal := ⟨fun z hz g => by
    rw [mem_center_iff.mp (hD hz) g, mul_inv_cancel_right]
    exact hz⟩
  have hxy : ⁅x, y⁆ = 1 := (commute_axis q hsq x y
    (Or.inr ⟨by rw [hx], by rw [hy]⟩)).commutator_eq
  have hbxy : ⁅bx, by'⁆ = 1 := (commute_axis q hsq bx by'
    (Or.inl ⟨by rw [hbx], by rw [hby]⟩)).commutator_eq
  have h₁ : ⁅bx, x⁆ ∈ D := subset_closure (by simp)
  have h₂ : ⁅bx, y⁆ ∈ D := subset_closure (by simp)
  have h₃ : ⁅by', x⁆ ∈ D := subset_closure (by simp)
  have h₄ : ⁅by', y⁆ ∈ D := subset_closure (by simp)
  have hreverse (u v : K) (huv : ⁅u, v⁆ ∈ D) : ⁅v, u⁆ ∈ D := by
    rw [← commutatorElement_inv]
    exact D.inv_mem huv
  apply derived_le_of_central_generators ({x, y, bx, by'} : Set K) D
  · apply root_generation q hq hsq x y bx by' hx hy hbx hby
    · intro z hz
      exact subset_closure (Or.inr hz)
    · exact subset_closure (Or.inl (by simp))
    · exact subset_closure (Or.inl (by simp))
    · exact subset_closure (Or.inl (by simp))
    · exact subset_closure (Or.inl (by simp))
  · intro u hu v hv
    rcases hu with rfl | rfl | rfl | rfl <;>
      rcases hv with rfl | rfl | rfl | rfl
    all_goals first
      | exact h₁
      | exact h₂
      | exact h₃
      | exact h₄
      | exact hreverse _ _ h₁
      | exact hreverse _ _ h₂
      | exact hreverse _ _ h₃
      | exact hreverse _ _ h₄
      | simpa only [commutatorElement_self] using D.one_mem
      | simpa only [hxy] using D.one_mem
      | simpa only [hbxy] using D.one_mem
      | exact hreverse _ _ (by simpa only [hxy] using D.one_mem)
      | exact hreverse _ _ (by simpa only [hbxy] using D.one_mem)

/-- The graph-field action on an elementary first-root vector. -/
private theorem cross_coordinates (q : K →* U) (b : MulAut K)
    (hb : ∀ k : K, q (b k) = ⟨(q k).y ^ 2, (q k).x ^ 2,
      (q k).c ^ 2 + ((q k).x * (q k).y) ^ 2⟩)
    (u v : K) (s t : F) (hu : q u = ⟨s, 0, 0⟩) (hv : q v = ⟨t, 0, 0⟩) :
    q ⁅b u, v⁆ = ⟨0, 0, s ^ 2 * t⟩ := by
  rw [map_commutatorElement, hb, hu, hv, comm_coordinates]
  apply U.ext <;> simp [mul_comm]

/-- The coordinate presentation, viewed through any injective target embedding. -/
private def coordinateRootPair {B : Type*} [Group B] (j : U →* B) (hj : Function.Injective j)
    (q : K →* U) (hq : Function.Surjective q)
    (hsq : ∀ k : K, (q k) ^ 2 = 1 → k ^ 2 = 1) (b : MulAut K)
    (hb : ∀ k : K, q (b k) = ⟨(q k).y ^ 2, (q k).x ^ 2,
      (q k).c ^ 2 + ((q k).x * (q k).y) ^ 2⟩)
    (x y : K) (hx : q x = ⟨1, 0, 0⟩) (hy : q y = ⟨omega, 0, 0⟩) :
    RootPair (j.comp q) b := by
  have hbx : q (b x) = ⟨0, 1, 0⟩ := by rw [hb, hx]; simp
  have hby : q (b y) = ⟨0, omega ^ 2, 0⟩ := by rw [hb, hy]; simp
  have hxy : q (x * y) = ⟨1 + omega, 0, 0⟩ := by
    rw [map_mul, hx, hy]
    apply U.ext <;> simp
  have hsum : (1 : F) + omega ≠ 0 := by
    intro h
    have h' : (1 : F) = -omega := add_eq_zero_iff_eq_neg.mp h
    rw [CharTwo.neg_eq] at h'
    exact omega_ne_one h'.symm
  have hdiag : q ⁅b x, x⁆ = ⟨0, 0, 1⟩ := by
    rw [cross_coordinates q b hb x x 1 1 hx hx]
    simp
  have hdiagY : q ⁅b y, y⁆ = ⟨0, 0, 1⟩ := by
    rw [cross_coordinates q b hb y y omega omega hy hy, ← pow_succ, omega_cube]
  have hthird : q ⁅b (x * y), x * y⁆ = ⟨0, 0, 1⟩ := by
    rw [cross_coordinates q b hb (x * y) (x * y) _ _ hxy hxy,
      ← pow_succ, nonzero_cube _ hsum]
  have hcross₁ : q ⁅b x, y⁆ = ⟨0, 0, omega⟩ := by
    rw [cross_coordinates q b hb x y 1 omega hx hy]
    simp
  have hcross₂ : q ⁅b y, x⁆ = ⟨0, 0, omega ^ 2⟩ := by
    rw [cross_coordinates q b hb y x omega 1 hy hx]
    simp
  have hcross₃ : q (⁅b x, y⁆ * ⁅b y, x⁆) = ⟨0, 0, 1⟩ := by
    rw [map_mul, hcross₁, hcross₂]
    apply U.ext <;> simp [omega_add_square]
  have hne (u : U) (hu : u.c ≠ 0) : j u ≠ 1 := by
    intro h
    have he : u = 1 := hj (h.trans j.map_one.symm)
    exact hu (congrArg U.c he)
  exact {
    x := x
    y := y
    class_two := lifted_class_two q hq hsq
    derived_generated := root_derived_generated q hq hsq x y (b x) (b y) hx hy hbx hby
    derived_square := lifted_derived_square q hsq
    diagonal_images := by change j (q _) = j (q _); rw [hdiag, hdiagY]
    third_image := by change j (q _) = j (q _); rw [hdiag, hthird]
    cross_one := by change j (q _) ≠ 1; rw [hcross₁]; exact hne _ omega_ne_zero
    cross_two := by change j (q _) ≠ 1; rw [hcross₂]; exact hne _ (pow_ne_zero _ omega_ne_zero)
    cross_product := by change j (q _) ≠ 1; rw [hcross₃]; exact hne _ one_ne_zero }

end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.RootLifting

namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
variable {H : Type*} [Group H]

/-- An invariant unitary Sylow model and source involution lifting construct
all fields of the double-cover root presentation. -/
public theorem nonempty_liftedRootPair [Finite H]
    (c : PerfectCentralCovering.Cover H PSL)
    (hk : c.toMonoidHom.ker = center H) (hZ : Nat.card (center H) = 2)
    (a : MulAut H) (ha2 : a ^ 2 = 1)
    (ha : ∀ x, c.toMonoidHom (a x) =
      ExtendedCentralizer.ProjectiveFixer.graphField (c.toMonoidHom x))
    (hlift : InvolutionLifting c) (m : UnitarySylowModel) :
    Nonempty (LiftedRootPair c a) := by
  classical
  have hker : IsPGroup 2 c.toMonoidHom.ker := by
    rw [hk]
    exact IsPGroup.of_card (p := 2) (n := 1) (by simpa using hZ)
  let S : Sylow 2 H := m.sylow.comapOfKerIsPGroup c.toMonoidHom hker
    (by rw [MonoidHom.range_eq_top.mpr c.surjective]; exact le_top)
  let f : S →* PSL := c.toMonoidHom.comp (S : Subgroup H).subtype
  have hfmem (s : S) : f s ∈ m.embedding.range := by
    rw [m.range_eq]
    exact s.property
  let e := MonoidHom.ofInjective m.injective
  let q : S →* SylowModel.U :=
    e.symm.toMonoidHom.comp (f.codRestrict m.embedding.range hfmem)
  have hproj (s : S) : m.embedding (q s) = f s :=
    congrArg Subtype.val (e.apply_symm_apply ⟨f s, hfmem s⟩)
  have hq : Function.Surjective q := by
    intro u
    obtain ⟨s, hs⟩ := c.surjective (m.embedding u)
    have hsS : s ∈ (S : Subgroup H) := by
      change c.toMonoidHom s ∈ (m.sylow : Subgroup PSL)
      rw [hs, ← m.range_eq]
      exact ⟨u, rfl⟩
    refine ⟨⟨s, hsS⟩, m.injective ?_⟩
    rw [hproj]
    exact hs
  have hsq (s : S) (hs : (q s) ^ 2 = 1) : s ^ 2 = 1 := by
    apply Subtype.ext
    apply square_eq_one_of_projective_square c hk hZ hlift
    change (f s) ^ 2 = 1
    rw [← hproj, ← map_pow, hs, map_one]
  have hstable (s : S) : a (s : H) ∈ (S : Subgroup H) := by
    change c.toMonoidHom (a (s : H)) ∈ (m.sylow : Subgroup PSL)
    rw [ha]
    change ExtendedCentralizer.ProjectiveFixer.graphField (f s) ∈ _
    rw [← hproj, m.compatible, ← m.range_eq]
    exact ⟨_, rfl⟩
  let b : MulAut S := {
    toFun := fun s => ⟨a s, hstable s⟩
    invFun := fun s => ⟨a s, hstable s⟩
    left_inv := fun s => Subtype.ext (involutive_apply a ha2 s)
    right_inv := fun s => Subtype.ext (involutive_apply a ha2 s)
    map_mul' := fun s t => Subtype.ext (a.map_mul s t) }
  have hb (s : S) : q (b s) = ⟨(q s).y ^ 2, (q s).x ^ 2,
      (q s).c ^ 2 + ((q s).x * (q s).y) ^ 2⟩ := by
    apply m.injective
    rw [hproj]
    change c.toMonoidHom (a (s : H)) = _
    rw [ha]
    change ExtendedCentralizer.ProjectiveFixer.graphField (f s) = _
    rw [← hproj, m.compatible]
  obtain ⟨x, hx⟩ := hq ⟨1, 0, 0⟩
  obtain ⟨y, hy⟩ := hq ⟨ProjectiveGraphField.omega, 0, 0⟩
  have hf : m.embedding.comp q = f := MonoidHom.ext hproj
  refine ⟨{ sylow := S, action := b, compatible := fun _ => rfl, roots := ?_ }⟩
  change RootPair f b
  rw [← hf]
  exact RootLifting.coordinateRootPair m.embedding m.injective q hq hsq b hb x y hx hy

end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
