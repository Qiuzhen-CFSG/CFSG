module

public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Center
public import Theory.ElementaryAbelian.Basic

/-!
# Invariant self-centralizing subgroups of `E₄ ≀ C₂`

The diagonal cubic on the two binary planes has four invariant subgroups in
the quotient by the diagonal centre.  Lifting through the explicit quotient
map gives the three source alternatives after the central subgroup is removed
by the self-centralizer condition.  This is the finite local calculation used
for Aschbacher--Smith, Lemma 14.2.21.
-/

namespace FourWreathTwo

open scoped IsMulCommutative

public abbrev C2 := Multiplicative (ZMod 2)
public abbrev E4 := Multiplicative (ZMod 2 × ZMod 2)
public abbrev Wreath := RegularWreathProduct E4 C2
public abbrev CentralQuotient := E4 × C2

public instance : Fintype Wreath := Fintype.ofEquiv ((C2 → E4) × C2)
  (RegularWreathProduct.equivProd E4 C2).symm
public instance : DecidableEq Wreath :=
  (RegularWreathProduct.equivProd E4 C2).injective.decidableEq

@[expose] public def cubicFour (v : E4) : E4 :=
  Multiplicative.ofAdd (v.toAdd.2, v.toAdd.1 + v.toAdd.2)

@[expose] public def cubicFn (w : Wreath) : Wreath :=
  ⟨fun i => cubicFour (w.left i), w.right⟩

@[expose] public def cubicA (a : CentralQuotient) : CentralQuotient :=
  (cubicFour a.1, a.2)

@[expose] public def deltaFn (w : Wreath) : CentralQuotient :=
  (w.left 1 * w.left (Multiplicative.ofAdd 1), w.right)

@[expose] public def cubic : MulAut Wreath where
  toFun := cubicFn
  invFun := fun w => cubicFn (cubicFn w)
  left_inv := by decide
  right_inv := by decide
  map_mul' := by decide

@[expose] public def delta : Wreath →* CentralQuotient where
  toFun := deltaFn
  map_one' := by decide
  map_mul' := by decide

public theorem delta_cubic (w : Wreath) : delta (cubic w) = cubicA (delta w) := by
  revert w
  decide

public theorem delta_surjective : Function.Surjective delta := by decide

@[expose] public def plane : Subgroup CentralQuotient :=
  (MonoidHom.snd E4 C2).ker

@[expose] public def line : Subgroup CentralQuotient :=
  (MonoidHom.fst E4 C2).ker

@[expose] public def base : Subgroup Wreath := plane.comap delta
@[expose] public def other : Subgroup Wreath := line.comap delta

public instance : DecidablePred (· ∈ base) := fun w =>
  inferInstanceAs (Decidable ((delta w).2 = 1))

public instance : DecidablePred (· ∈ other) := fun w =>
  inferInstanceAs (Decidable ((delta w).1 = 1))

public theorem base_eq_rightHom_ker :
    base = (RegularWreathProduct.rightHom : Wreath →* C2).ker := rfl

public theorem mem_other_iff (w : Wreath) :
    w ∈ other ↔ w.left 1 = w.left (Multiplicative.ofAdd 1) := by
  revert w
  decide

public theorem center_eq_ker : Subgroup.center Wreath = delta.ker := by
  have h : ∀ w : Wreath, (∀ v : Wreath, v * w = w * v) ↔ deltaFn w = 1 := by
    decide
  ext w
  exact (Subgroup.mem_center_iff).trans (h w)

private theorem invariant_image_cases (P : Subgroup CentralQuotient)
    (hP : ∀ a ∈ P, cubicA a ∈ P) :
    P = ⊥ ∨ P = plane ∨ P = line ∨ P = ⊤ := by
  classical
  have hsnd : ∀ a ∈ P, (1, a.2) ∈ P := by
    intro a ha
    have h : ∀ a : CentralQuotient,
        a * cubicA a * cubicA (cubicA a) = (1, a.2) := by decide
    rw [← h a]
    exact P.mul_mem (P.mul_mem ha (hP a ha)) (hP _ (hP a ha))
  have hfst : ∀ a ∈ P, (a.1, 1) ∈ P := by
    intro a ha
    have h : ∀ a : CentralQuotient, a * (1, a.2) = (a.1, 1) := by decide
    rw [← h a]
    exact P.mul_mem ha (hsnd a ha)
  have hplane : plane ≤ P ∨ P ≤ line := by
    by_cases h : ∃ a ∈ P, a.1 ≠ 1
    · obtain ⟨a, ha, hne⟩ := h
      left
      intro y hy
      have hy2 : y.2 = 1 := hy
      have hspan : ∀ x : E4, x ≠ 1 → ∀ y : E4,
          y = 1 ∨ y = x ∨ y = cubicFour x ∨ y = x * cubicFour x := by decide
      have ha1 := hfst a ha
      have ha2 := hP (a.1, 1) ha1
      obtain he | he | he | he := hspan a.1 hne y.1
      · have : y = 1 := Prod.ext he hy2
        simp [this]
      · have : y = (a.1, 1) := Prod.ext he hy2
        exact this ▸ ha1
      · have : y = cubicA (a.1, 1) := Prod.ext he hy2
        exact this ▸ ha2
      · have : y = (a.1, 1) * cubicA (a.1, 1) :=
          Prod.ext he (by simpa [cubicA] using hy2)
        exact this ▸ P.mul_mem ha1 ha2
    · right
      intro a ha
      show a.1 = 1
      by_contra hn
      exact h ⟨a, ha, hn⟩
  have hline : line ≤ P ∨ P ≤ plane := by
    by_cases h : ∃ a ∈ P, a.2 ≠ 1
    · obtain ⟨a, ha, hne⟩ := h
      left
      intro y hy
      have hy1 : y.1 = 1 := hy
      have hspan : ∀ x : C2, x ≠ 1 → ∀ y : C2, y = 1 ∨ y = x := by decide
      obtain he | he := hspan a.2 hne y.2
      · have : y = 1 := Prod.ext hy1 he
        simp [this]
      · have : y = (1, a.2) := Prod.ext hy1 he
        exact this ▸ hsnd a ha
    · right
      intro a ha
      show a.2 = 1
      by_contra hn
      exact h ⟨a, ha, hn⟩
  rcases hplane with hplane | hplane <;> rcases hline with hline | hline
  · right; right; right
    apply top_unique
    intro a _
    have he : a = (a.1, 1) * (1, a.2) := by simp
    rw [he]
    exact P.mul_mem (hplane rfl) (hline rfl)
  · exact Or.inr (Or.inl (le_antisymm hline hplane))
  · exact Or.inr (Or.inr (Or.inl (le_antisymm hplane hline)))
  · left
    apply bot_unique
    intro a ha
    exact Prod.ext (hplane ha) (hline ha)

public theorem core_trichotomy (Q : Subgroup Wreath)
    (hcubic : ∀ w ∈ Q, cubic w ∈ Q)
    (hcentral : Subgroup.centralizer (Q : Set Wreath) ≤ Q) :
    Q = ⊤ ∨ Q = base ∨ Q = other := by
  have hcenter : Subgroup.center Wreath ≤ Q :=
    (Subgroup.center_le_centralizer (Q : Set Wreath)).trans hcentral
  have hker : delta.ker ≤ Q := by simpa only [center_eq_ker] using hcenter
  have hrecover := Subgroup.comap_map_eq_self hker
  have hinv : ∀ a ∈ Q.map delta, cubicA a ∈ Q.map delta := by
    rintro a ⟨w, hw, rfl⟩
    exact ⟨cubic w, hcubic w hw, delta_cubic w⟩
  obtain h | h | h | h := invariant_image_cases (Q.map delta) hinv
  · have hQ : Q = Subgroup.center Wreath := by
      rw [h] at hrecover
      exact hrecover.symm.trans center_eq_ker.symm
    left
    apply top_unique
    intro w _
    apply hcentral
    intro q hq
    have hq' : q ∈ Subgroup.center Wreath := hQ ▸ hq
    exact (Subgroup.mem_center_iff.mp hq' w).symm
  · right; left
    simpa only [h, base] using hrecover.symm
  · right; right
    simpa only [h, other] using hrecover.symm
  · left
    simpa only [h, Subgroup.comap_top] using hrecover.symm

public theorem core_trichotomy_of_quotient {D : Type*} [Group D]
    (f : D →* Wreath) (Q : Subgroup D) (hker : f.ker ≤ Q)
    (hcubic : ∀ w ∈ Q.map f, cubic w ∈ Q.map f)
    (hcentral : Subgroup.centralizer (Q.map f : Set Wreath) ≤ Q.map f) :
    Q = ⊤ ∨ Q = base.comap f ∨ Q = other.comap f := by
  have hrecover := Subgroup.comap_map_eq_self hker
  obtain h | h | h := core_trichotomy (Q.map f) hcubic hcentral
  · left
    simpa only [h, Subgroup.comap_top] using hrecover.symm
  · right; left
    simpa only [h] using hrecover.symm
  · right; right
    simpa only [h] using hrecover.symm

public theorem card_wreath : Nat.card Wreath = 32 := by
  rw [Nat.card_eq_fintype_card]
  decide

set_option linter.style.haveILetI false in
public theorem card_base : Nat.card base = 16 := by
  letI : Fintype base :=
    Fintype.subtype (Fintype.elems.filter (fun w => w ∈ base)) (by
      intro x
      rw [Finset.mem_filter]
      constructor
      · exact And.right
      · intro hx
        exact ⟨Fintype.complete x, hx⟩)
  rw [Nat.card_eq_fintype_card]
  decide

set_option linter.style.haveILetI false in
public theorem card_other : Nat.card other = 8 := by
  letI : Fintype other :=
    Fintype.subtype (Fintype.elems.filter (fun w => w ∈ other)) (by
      intro x
      rw [Finset.mem_filter]
      constructor
      · exact And.right
      · intro hx
        exact ⟨Fintype.complete x, hx⟩)
  rw [Nat.card_eq_fintype_card]
  decide

public theorem base_centralizer : Subgroup.centralizer (base : Set Wreath) = base := by
  have h : ∀ x : Wreath, (∀ y : Wreath, (delta y).2 = 1 → y * x = x * y) ↔
      (delta x).2 = 1 := by decide
  ext x
  exact h x

public theorem other_centralizer : Subgroup.centralizer (other : Set Wreath) = other := by
  have h : ∀ x : Wreath, (∀ y : Wreath, (delta y).1 = 1 → y * x = x * y) ↔
      (delta x).1 = 1 := by decide
  ext x
  exact h x

/-- An element outside the base has only eight commuting elements. -/
public theorem centralizer_card_outside_base (x : Wreath) (hx : x ∉ base) :
    Nat.card (Subgroup.centralizer ({x} : Set Wreath)) = 8 := by
  let e : Subgroup.centralizer ({x} : Set Wreath) ≃
      {y : Wreath // y * x = x * y} :=
    Equiv.subtypeEquivRight (fun y => by
      rw [Subgroup.mem_centralizer_singleton_iff, eq_comm])
  rw [Nat.card_congr e, Nat.card_eq_fintype_card]
  have h : ∀ x : Wreath, x ∉ base →
      Fintype.card {y : Wreath // y * x = x * y} = 8 := by decide
  exact h x hx

/-- Every abelian subgroup larger than the other E₈ lies in the base. -/
public theorem large_abelian_le_base (A : Subgroup Wreath)
    [IsMulCommutative A] (hA : 8 < Nat.card A) : A ≤ base := by
  intro x hx
  by_contra hn
  have hle : A ≤ Subgroup.centralizer ({x} : Set Wreath) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm (⟨y, hy⟩ : A) ⟨x, hx⟩)
  have hcard := Subgroup.card_le_of_le hle
  rw [centralizer_card_outside_base x hn] at hcard
  omega

public theorem base_elementary : IsElementaryAbelian 2 base := by
  have hcomm : ∀ x y : Wreath,
      (delta x).2 = 1 → (delta y).2 = 1 → x * y = y * x := by decide
  have hpow : ∀ x : Wreath, (delta x).2 = 1 → x ^ 2 = 1 := by decide
  exact {
    is_comm := ⟨fun x y => Subtype.ext (hcomm x y x.property y.property)⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      (fun x => Subtype.ext (hpow x x.property)) }

public theorem other_square (w : other) : w ^ 2 = 1 := by
  have h : ∀ x : Wreath, (delta x).1 = 1 → x ^ 2 = 1 := by decide
  apply Subtype.ext
  exact h w w.property

public theorem other_elementary : IsElementaryAbelian 2 other := by
  have hcomm : ∀ x y : Wreath,
      (delta x).1 = 1 → (delta y).1 = 1 → x * y = y * x := by decide
  exact {
    is_comm := ⟨fun x y => Subtype.ext (hcomm x y x.property y.property)⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr other_square }

/-- The base is the unique abelian subgroup of order sixteen. -/
public instance base_characteristic : base.Characteristic := by
  let : IsElementaryAbelian 2 base := base_elementary
  apply Subgroup.characteristic_iff_map_le.mpr
  intro a
  let : IsElementaryAbelian 2 (base.map a.toMonoidHom) :=
    base_elementary.map a.toMonoidHom
  apply large_abelian_le_base
  rw [Subgroup.card_map_of_injective a.injective, card_base]
  decide

end FourWreathTwo
