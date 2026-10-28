module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.Contracts
public import CFSG.Quasithin.ChapterI.Section04To05.Janko1.Order.OddPrimeCentralizers.Structure.ExceptionalExclusion.LocalGeometry.Products
public import Theory.GroupAction.KleinFourCubicFixedCard
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# The cubic fixed subgroup in the exceptional normalizer

For every displayed decomposition N_G(A) = A(VX), where A is elementary
abelian of order 27, V is a four-group and X has order three and normalizes
V, the subgroup C_A(X) has order three.

An element of X moving V generates X. Its conjugation action cycles the
three nonidentity elements of V. The corresponding two involutions on A
have trivial common fixed subgroup, by the ambient four-group centralizer
calculation. The unique character-factor coordinates identify the cubic
fixed subgroup with a diagonal, whose order cubed is 27. An explicit
bijection identifies these fixed points with the literal A ∩ C_G(X).
The final corollary discharges the fixed-cardinality premise of the plane
product calculation, giving |C_A(X)X| = 9.

Source: Bender, *Finite groups with large subgroups* (1974), proof of (4.1),
PDF p.3 / printed p.225, the implication C_A(V) = 1 ⇒ |C_A(X)| = 3.
-/

open Subgroup
namespace CFSG.Quasithin.Janko1CentralizerData
variable {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]

/-- The actual cubic fixed subgroup has order three, for every supplied decomposition. -/
public theorem exceptional_fixed_card (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (V X : Subgroup G) (hVe : IsElementaryAbelian 2 V)
    (hV : Nat.card V = 4) (hX : Nat.card X = 3)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X)) :
    Nat.card (A ⊓ centralizer (X : Set G) : Subgroup G) = 3 := by
  classical
  let _ := e.elementary
  let _ := hVe
  let _ : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let _ : Fintype V := Fintype.ofFinite V
  let _ : IsKleinFour V := ⟨hV, IsElementaryAbelian.exponent_eq_prime⟩
  have hVA : V ≤ normalizer (A : Set G) := by rw [hN]; exact le_sup_of_le_right le_sup_left
  have hXA : X ≤ normalizer (A : Set G) := by rw [hN]; exact le_sup_of_le_right le_sup_right
  obtain ⟨x, hx, hxC⟩ := SetLike.not_le_iff_exists.mp
    (h.exceptional_actor_not_centralizes_four V X hV hX)
  have hx3 : x ^ 3 = 1 := by
    have hp := congrArg Subtype.val (pow_card_eq_one' (x := (⟨x,hx⟩ : X)))
    simpa only [Subgroup.coe_pow, Subgroup.coe_one, hX] using hp
  have hx1 : x ≠ 1 := by intro he; exact hxC (he ▸ (centralizer (V : Set G)).one_mem)
  have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hXgen : zpowers x = X := eq_of_le_of_card_ge (zpowers_le.mpr hx)
    (by rw [Nat.card_zpowers, hxord, hX])
  let c : MulAut V := V.normalizerMonoidHom ⟨x,hXV hx⟩
  have hc3pow : c ^ 3 = 1 := by
    rw [← map_pow]
    have he : (⟨x,hXV hx⟩ : normalizer (V : Set G)) ^ 3 = 1 := Subtype.ext hx3
    rw [he, map_one]
  have hc3 (v : V) : c (c (c v)) = v := by
    have he := congrArg (fun f : MulAut V => f v) hc3pow
    simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using he
  have hmove : ∃ v : V, c v ≠ v := by
    by_contra! hf
    apply hxC
    intro v hv
    have he := congrArg Subtype.val (hf ⟨v,hv⟩)
    change x * v * x⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  obtain ⟨v, hv⟩ := hmove
  have hv1 : v ≠ 1 := by intro he; apply hv; simp [he]
  have hcv1 : c v ≠ 1 := by
    intro he
    exact hv1 (c.injective (he.trans (map_one c).symm))
  have hccv1 : c (c v) ≠ 1 := by
    intro he
    exact hcv1 (c.injective (he.trans (map_one c).symm))
  have hccv_v : c (c v) ≠ v := by
    intro he
    have hf := congrArg c he
    rw [hc3] at hf
    exact hv hf.symm
  have hccv_cv : c (c v) ≠ c v := fun he => hv (c.injective he)
  have hcycle : c (c v) = v * c v :=
    IsKleinFour.eq_mul_of_ne_all hv1 hcv1 hv.symm hccv1 hccv_v hccv_cv
  have henum (w : V) : w = 1 ∨ w = v ∨ w = c v ∨ w = v * c v := by
    have hm : w ∈ ({v * c v, v, c v, (1 : V)} : Finset V) := by
      rw [IsKleinFour.eq_finset_univ hv1 hcv1 hv.symm]
      exact Finset.mem_univ w
    simpa only [Finset.mem_insert, Finset.mem_singleton, or_comm, or_left_comm, or_assoc] using hm
  let r : normalizer (A : Set G) := ⟨v, hVA v.property⟩
  let s : normalizer (A : Set G) := ⟨c v, hVA (c v).property⟩
  let z : normalizer (A : Set G) := ⟨x, hXA hx⟩
  let a : MulAut A := A.normalizerMonoidHom r
  let b : MulAut A := A.normalizerMonoidHom s
  let t : MulAut A := A.normalizerMonoidHom z
  have hr2 : r * r = 1 := Subtype.ext (congrArg (fun u : V => (u : G)) (IsKleinFour.mul_self v))
  have hs2 : s * s = 1 := Subtype.ext (congrArg (fun u : V => (u : G)) (IsKleinFour.mul_self (c v)))
  have hrs : Commute r s := by
    apply Subtype.ext
    exact congrArg (fun u : V => (u : G)) (mul_comm' v (c v))
  have hzr : z * r = s * z := by
    apply Subtype.ext
    change x * v.val = (x * v.val * x⁻¹) * x
    group
  have hzs : z * s = (r * s) * z := by
    apply Subtype.ext
    have he := congrArg Subtype.val hcycle
    change x * (c v).val * x⁻¹ = v.val * (c v).val at he
    exact mul_inv_eq_iff_eq_mul.mp he
  have hzrs : z * (r * s) = r * z := by
    calc
      z * (r * s) = (s * z) * s := by rw [← mul_assoc, hzr]
      _ = s * ((r * s) * z) := by rw [mul_assoc, hzs]
      _ = r * z := by rw [← mul_assoc, ← mul_assoc, hrs.eq.symm, mul_assoc r s s, hs2, mul_one]
  have ha : Function.Involutive a := by
    intro u
    have he : a * a = 1 := by rw [← map_mul, hr2, map_one]
    exact congrArg (fun f : MulAut A => f u) he
  have hb : Function.Involutive b := by
    intro u
    have he : b * b = 1 := by rw [← map_mul, hs2, map_one]
    exact congrArg (fun f : MulAut A => f u) he
  have hab : Commute a b := hrs.map A.normalizerMonoidHom
  have ht (u : A) : t (t (t u)) = u := by
    have he : z ^ 3 = 1 := Subtype.ext hx3
    have hf : t ^ 3 = 1 := by rw [← map_pow, he, map_one]
    have hh := congrArg (fun f : MulAut A => f u) hf
    simpa only [pow_succ, pow_zero, MulAut.mul_apply, MulAut.one_apply] using hh
  have hat (u : A) : a (t u) = t (a (b u)) := by
    have he := congrArg A.normalizerMonoidHom hzrs.symm
    simp only [map_mul] at he
    exact congrArg (fun f : MulAut A => f u) he
  have hbt (u : A) : b (t u) = t (a u) := by
    have he := congrArg A.normalizerMonoidHom hzr.symm
    simp only [map_mul] at he
    exact congrArg (fun f : MulAut A => f u) he
  have hcommon (u : A) (hau : a u = u) (hbu : b u = u) : u = 1 := by
    have hav : v.val * u.val = u.val * v.val := by
      have he := congrArg Subtype.val hau
      exact mul_inv_eq_iff_eq_mul.mp he
    have hbv : (c v).val * u.val = u.val * (c v).val := by
      have he := congrArg Subtype.val hbu
      exact mul_inv_eq_iff_eq_mul.mp he
    have huc : u.val ∈ centralizer (V : Set G) := by
      intro w hw
      rcases henum ⟨w,hw⟩ with he | he | he | he
      · have hh := congrArg Subtype.val he
        simp only [Subgroup.coe_one] at hh
        simp [hh]
      · have hh : w = v.val := congrArg Subtype.val he
        simpa only [hh] using hav
      · have hh : w = (c v).val := congrArg Subtype.val he
        simpa only [hh] using hbv
      · have hh := congrArg Subtype.val he
        simp only [Subgroup.coe_mul] at hh
        rw [hh, mul_assoc, hbv, ← mul_assoc, hav, mul_assoc]
    apply Subtype.ext
    exact (h.odd_inf_four_centralizer_eq_bot A V (by rw [e.card]; decide) hV).le
      ⟨u.property,huc⟩
  have hcube := Theory.GroupAction.cubic_fixed_card_cube
    (by rw [e.card]; decide) a b t ha hb hab ht hat hbt hcommon
  have hfixed : Nat.card (MulAut.fixedSubgroup t) = 3 := by
    rw [e.card] at hcube
    have he : Nat.card (MulAut.fixedSubgroup t) ^ 3 = 3 ^ 3 := hcube
    exact Nat.pow_left_injective (by decide : 3 ≠ 0) he
  let f : MulAut.fixedSubgroup t ≃ (A ⊓ centralizer (X : Set G) : Subgroup G) :=
    { toFun := fun u => ⟨u.val.val, u.val.property, by
        have he : t u.val = u.val := by simpa only [MulAut.mem_fixedSubgroup] using u.property
        have he' := congrArg Subtype.val he
        have hux : x * u.val.val = u.val.val * x := mul_inv_eq_iff_eq_mul.mp he'
        have hxcu : x ∈ centralizer ({u.val.val} : Set G) := by
          rw [mem_centralizer_singleton_iff]
          exact hux
        have hle : X ≤ centralizer ({u.val.val} : Set G) := by
          rw [← hXgen]
          exact zpowers_le.mpr hxcu
        intro y hy
        exact (hle hy u.val.val (Set.mem_singleton _)).symm⟩
      invFun := fun u => ⟨⟨u.val,u.property.1⟩, by
        rw [MulAut.mem_fixedSubgroup]
        apply Subtype.ext
        change x * u.val * x⁻¹ = u.val
        exact mul_inv_eq_iff_eq_mul.mpr (u.property.2 x hx)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr f).symm.trans hfixed
/-- The fixed-subgroup calculation gives the order of Bender's literal plane Y. -/
public theorem exceptional_plane_card (h : Janko1CentralizerData G)
    (A : Subgroup G) (e : ExceptionalOddNormalizer A)
    (V X : Subgroup G) (hVe : IsElementaryAbelian 2 V)
    (hV : Nat.card V = 4) (hX : Nat.card X = 3)
    (hXV : X ≤ normalizer (V : Set G))
    (hN : normalizer (A : Set G) = A ⊔ (V ⊔ X)) :
    Nat.card (exceptionalPlane A X) = 9 :=
  h.exceptional_plane_card_of_fixed_card A V X e.card hV hX hXV hN
    (h.exceptional_fixed_card A e V X hVe hV hX hXV hN)

end CFSG.Quasithin.Janko1CentralizerData
