module

public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Inputs
public import CFSG.Quasithin.Chapter16.Section03.ThompsonObstruction.Comparison
public import Theory.Frattini.BinarySquares
public import Stellmacher.ElementaryAbelianMaxJMap

/-!
# The Thompson calculation in C₂ × (D₈ wreath C₂)

For the concrete `LocalSylowModel`, the elementary Thompson subgroup is the
base C₂ × D₈ × D₈. Its maximum elementary two-rank is five, and
Ω₁(Φ(J(P))) is the product of the centers of the two dihedral factors.
The wreath switch interchanges their nonidentity elements, so this four-group
is not centralized by P.

The maximum-order assertion is proved, rather than assumed: every elementary
subgroup in the base lies in one of four subgroups of order 32. An outside
involution is conjugate to a central C₂ element times the switch. There are
only 24 elements squaring to one in the switch centralizer, so an elementary
subgroup meeting the outside coset cannot have maximum order. Two of the
order-32 subgroups generate the base, proving the assertion about the actual
`Stellmacher.elementaryAbelianMaxJ`.

For the Frattini calculation, every square in the base belongs to the product
of the two dihedral centers, and every element of that product has a square
root in the base. The square-generation theorem for finite two-groups then
identifies Φ(base). The displayed finite identities and cardinalities use
kernel reduction on the concrete groups. No subgroup-lattice enumeration or
assumed rank, Thompson-subgroup, or moving-element certificate is used.

`local_calculation` transports the three conclusions needed by the parent
obstruction through any actual equivalence S ≃* LocalSylowModel. Constructing
that equivalence for the source's subgroup P remains with the parent.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, final argument
of Theorem 16.3.7, printed p.1182 / PDF p.1199, `refs/quasithin.pdf`.
-/

@[expose] public section

open Subgroup Stellmacher
open CFSG.Quasithin.Chapter16.ThompsonObstruction

namespace CFSG.Quasithin.Chapter16.ThompsonObstruction.LocalComputation
abbrev C2 := Multiplicative (ZMod 2)
abbrev D8 := DihedralGroup 4
abbrev P := LocalSylowModel
abbrev tau : C2 := Multiplicative.ofAdd 1
instance : DecidableEq (RegularWreathProduct D8 C2) := fun x y => decidable_of_iff
  (x.left = y.left ∧ x.right = y.right) RegularWreathProduct.ext_iff.symm
instance : Fintype (RegularWreathProduct D8 C2) :=
  Fintype.ofEquiv ((C2 → D8) × C2) (RegularWreathProduct.equivProd D8 C2).symm

def base : Subgroup P := (RegularWreathProduct.rightHom.comp (MonoidHom.snd C2 _)).ker

instance (x : P) : Decidable (x ∈ base) :=
  inferInstanceAs (Decidable (x.2.right = 1))

def baseEmbedding : C2 × (D8 × D8) →* P where
  toFun x := (x.1, ⟨fun q => if q = 1 then x.2.1 else x.2.2, 1⟩)
  map_one' := by ext q <;> simp
  map_mul' x y := by
    refine Prod.ext rfl ?_
    refine RegularWreathProduct.ext ?_ (by simp)
    funext q
    change (if q = 1 then x.2.1 * y.2.1 else x.2.2 * y.2.2) =
      (if q = 1 then x.2.1 else x.2.2) *
        (if (1 : C2)⁻¹ * q = 1 then y.2.1 else y.2.2)
    simp only [inv_one, one_mul]
    split <;> rfl

def coordinates (x : P) : C2 × (D8 × D8) := (x.1, x.2.left 1, x.2.left tau)

theorem coordinates_embedding (x : C2 × (D8 × D8)) : coordinates (baseEmbedding x) = x := by
  rcases x with ⟨c, a, b⟩
  simp [coordinates, baseEmbedding, tau]

theorem embedding_coordinates : ∀ x : P, x ∈ base → baseEmbedding (coordinates x) = x := by
  intro x hx
  refine Prod.ext rfl ?_
  apply RegularWreathProduct.ext
  · funext q
    have hq : q = 1 ∨ q = tau := by revert q; decide
    rcases hq with rfl | rfl <;> simp [baseEmbedding, coordinates, tau]
  · exact hx.symm

theorem embedding_injective : Function.Injective baseEmbedding :=
  Function.LeftInverse.injective coordinates_embedding

theorem embedding_range : baseEmbedding.range = base := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    rfl
  · intro x hx
    exact ⟨coordinates x, embedding_coordinates x hx⟩

noncomputable def baseEquiv : base ≃* C2 × (D8 × D8) :=
  ((MonoidHom.ofInjective embedding_injective).trans (MulEquiv.subgroupCongr embedding_range)).symm

theorem card_model : Nat.card P = 256 := by
  rw [Nat.card_prod, RegularWreathProduct.card, DihedralGroup.nat_card]
  norm_num [Nat.card_eq_fintype_card]

theorem model_isPGroup : IsPGroup 2 P := IsPGroup.of_card (by simpa using card_model : Nat.card P = 2 ^ 8)

theorem base_isPGroup : IsPGroup 2 base := model_isPGroup.of_injective base.subtype base.subtype_injective

private theorem elementary_of_square {H : Type*} [Group H] (h : ∀ x : H, x ^ 2 = 1) :
    IsElementaryAbelian 2 H where
  toIsMulCommutative := ⟨⟨fun a b =>
    (Commute.of_orderOf_dvd_two (fun x => orderOf_dvd_of_pow_eq_one (h x)) a b).eq⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr h

def dihedralFour (i : Fin 2) : Subgroup D8 where
  carrier := {d | d = DihedralGroup.r 0 ∨ d = DihedralGroup.r 2 ∨
    d = DihedralGroup.sr i.val ∨ d = DihedralGroup.sr ((i.val : ZMod 4) + 2)}
  one_mem' := Or.inl rfl
  mul_mem' := by revert i; decide +kernel
  inv_mem' := by revert i; decide +kernel

instance (i : Fin 2) (d : D8) : Decidable (d ∈ dihedralFour i) :=
  inferInstanceAs (Decidable (d = DihedralGroup.r 0 ∨ d = DihedralGroup.r 2 ∨
    d = DihedralGroup.sr i.val ∨ d = DihedralGroup.sr ((i.val : ZMod 4) + 2)))

theorem dihedralFour_square : ∀ i : Fin 2, ∀ d ∈ dihedralFour i, d ^ 2 = 1 := by
  decide +kernel

theorem dihedralFour_card (i : Fin 2) : Nat.card (dihedralFour i) = 4 := by
  rw [Nat.card_eq_fintype_card]
  revert i
  decide +kernel

def elementaryDomain (i j : Fin 2) : Subgroup (C2 × (D8 × D8)) :=
  (⊤ : Subgroup C2).prod ((dihedralFour i).prod (dihedralFour j))

def elementaryBase (i j : Fin 2) : Subgroup P := (elementaryDomain i j).map baseEmbedding

theorem elementaryBase_le (i j : Fin 2) : elementaryBase i j ≤ base :=
  (map_le_range _ _).trans embedding_range.le

theorem elementaryBase_elementary (i j : Fin 2) : IsElementaryAbelian 2 (elementaryBase i j) := by
  have hC : ∀ x : C2, x ^ 2 = 1 := by decide
  have : IsElementaryAbelian 2 (elementaryDomain i j) := elementary_of_square fun x => by
    apply Subtype.ext
    exact Prod.ext (hC x.val.1) (Prod.ext
      (dihedralFour_square i _ x.property.2.1) (dihedralFour_square j _ x.property.2.2))
  exact IsElementaryAbelian.map baseEmbedding

theorem elementaryBase_card (i j : Fin 2) : Nat.card (elementaryBase i j) = 32 := by
  rw [elementaryBase, card_map_of_injective embedding_injective]
  change Nat.card ((⊤ : Subgroup C2).prod ((dihedralFour i).prod (dihedralFour j))) = 32
  rw [Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod,
    Nat.card_congr (Subgroup.prodEquiv (dihedralFour i) (dihedralFour j)).toEquiv,
    Nat.card_prod, dihedralFour_card, dihedralFour_card]
  norm_num [Nat.card_eq_fintype_card]

private theorem dihedral_cover (A : Subgroup D8) (hA : IsElementaryAbelian 2 A) :
    ∃ i : Fin 2, A ≤ dihedralFour i := by
  classical
  let := hA
  by_cases h : A ≤ dihedralFour 0
  · exact ⟨0, h⟩
  have hpoint : ∃ a, a ∈ A ∧ a ∉ dihedralFour 0 := by
    simpa only [SetLike.le_def, not_forall, Classical.not_imp, exists_prop] using h
  obtain ⟨a, ha, ha0⟩ := hpoint
  refine ⟨1, fun b hb => ?_⟩
  have calcD : ∀ a b : D8, a ^ 2 = 1 → a ∉ dihedralFour 0 → b ^ 2 = 1 →
      a * b = b * a → b ∈ dihedralFour 1 := by decide +kernel
  exact calcD a b (elemPow_eq_one_of_isElementaryAbelian a ha) ha0
    (elemPow_eq_one_of_isElementaryAbelian b hb)
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance hb a ha)

private def baseCoordinate (q : C2) : base →* D8 where
  toFun x := x.val.2.left q
  map_one' := rfl
  map_mul' x y := by
    change x.val.2.left q * y.val.2.left (x.val.2.right⁻¹ * q) = _
    have hx : x.val.2.right = 1 := x.property
    simp [hx]

private theorem elementary_in_base (A : Subgroup P) (hA : IsElementaryAbelian 2 A)
    (hAb : A ≤ base) : ∃ i j : Fin 2, A ≤ elementaryBase i j := by
  let := hA
  let B := A.subgroupOf base
  have : IsElementaryAbelian 2 B := IsElementaryAbelian.subgroupOf hAb
  obtain ⟨i, hi⟩ := dihedral_cover (B.map (baseCoordinate 1)) (IsElementaryAbelian.map _)
  obtain ⟨j, hj⟩ := dihedral_cover (B.map (baseCoordinate tau)) (IsElementaryAbelian.map _)
  refine ⟨i, j, fun a ha => ?_⟩
  have haB : (⟨a, hAb ha⟩ : base) ∈ B := ha
  refine ⟨coordinates a, ⟨mem_top _, ?_, ?_⟩, embedding_coordinates a (hAb ha)⟩
  · exact hi (mem_map_of_mem (baseCoordinate 1) haB)
  · exact hj (mem_map_of_mem (baseCoordinate tau) haB)

private theorem elementary_in_base_card (A : Subgroup P) (hA : IsElementaryAbelian 2 A)
    (hAb : A ≤ base) : Nat.card A ≤ 32 := by
  obtain ⟨i, j, h⟩ := elementary_in_base A hA hAb
  exact (card_le_of_le h).trans_eq (elementaryBase_card i j)

/-- The top involution interchanging the two dihedral base factors. -/
def switch : P := (1, RegularWreathProduct.inl tau)

private def straightener (x : P) : P := baseEmbedding (1, 1, x.2.left 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem conjugate_outside : ∀ x : P, x ∉ base → x ^ 2 = 1 →
    MulAut.conj (straightener x) x = (x.1, RegularWreathProduct.inl tau) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem switch_involutions_card :
    Nat.card {y : P // y ^ 2 = 1 ∧ y * switch = switch * y} = 24 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

/-- Outside the base, an elementary subgroup has strictly fewer than 32 elements. -/
theorem elementary_outside_card (A : Subgroup P) (hA : IsElementaryAbelian 2 A)
    (hAb : ¬ A ≤ base) : Nat.card A ≤ 24 := by
  classical
  let := hA
  have hpoint : ∃ x, x ∈ A ∧ x ∉ base := by
    simpa only [SetLike.le_def, not_forall, Classical.not_imp, exists_prop] using hAb
  obtain ⟨x, hx, hxb⟩ := hpoint
  let e := MulAut.conj (straightener x)
  have hex : e x = (x.1, RegularWreathProduct.inl tau) :=
    conjugate_outside x hxb (elemPow_eq_one_of_isElementaryAbelian x hx)
  let f : A → {y : P // y ^ 2 = 1 ∧ y * switch = switch * y} := fun a =>
    ⟨e a, by
      constructor
      · rw [← map_pow, elemPow_eq_one_of_isElementaryAbelian a.val a.property, map_one]
      · have hax : a.val * x = x * a.val :=
          (Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance hx a.val a.property)
        have hh := congrArg e hax
        rw [map_mul, map_mul, hex] at hh
        refine Prod.ext ?_ ?_
        · change (e a).1 * 1 = 1 * (e a).1
          simp
        · have hh2 := congrArg (fun z : P => z.2) hh
          exact hh2⟩
  have hf : Function.Injective f := fun a b h => Subtype.ext (e.injective (congrArg Subtype.val h))
  exact (Nat.card_le_card_of_injective f hf).trans_eq switch_involutions_card

/-- The full maximum elementary-subgroup bound, without a rank certificate. -/
theorem elementary_card_le (A : Subgroup P) (hA : IsElementaryAbelian 2 A) :
    Nat.card A ≤ 32 := by
  by_cases h : A ≤ base
  · exact elementary_in_base_card A hA h
  · exact (elementary_outside_card A hA h).trans (by decide)

/-- Each of the four base elementary subgroups has maximum order. -/
theorem elementaryBase_maximal (i j : Fin 2) :
    elementaryBase i j ∈ elementaryAbelianMaxSubgroups (⊤ : Subgroup P) := by
  refine ⟨le_top, elementaryBase_elementary i j, ?_⟩
  intro B _ hB
  rw [elementaryBase_card]
  exact elementary_card_le B hB

theorem maxOrder_model : elementaryAbelianMaxOrder (⊤ : Subgroup P) = 32 :=
  (elementaryAbelianMaxSubgroups_card_eq _ _ (elementaryBase_maximal 0 0)).symm.trans
    (elementaryBase_card 0 0)

theorem twoRank_model : ChapterB.twoRank (⊤ : Subgroup P) = 5 := by
  rw [ChapterB.twoRank, maxOrder_model]
  decide

/-- Two maximum elementary subgroups generate the whole base. -/
theorem base_eq_sup : base = elementaryBase 0 0 ⊔ elementaryBase 1 1 := by
  apply le_antisymm
  · intro x hx
    have splitD : ∀ d : D8, ∃ a b : D8,
        a ∈ dihedralFour 0 ∧ b ∈ dihedralFour 1 ∧ a * b = d := by decide +kernel
    obtain ⟨a, b, ha, hb, hab⟩ := splitD (x.2.left 1)
    obtain ⟨c, d, hc, hd, hcd⟩ := splitD (x.2.left tau)
    have hu : baseEmbedding (x.1, a, c) ∈ elementaryBase 0 0 :=
      mem_map_of_mem baseEmbedding ⟨mem_top _, ha, hc⟩
    have hv : baseEmbedding (1, b, d) ∈ elementaryBase 1 1 :=
      mem_map_of_mem baseEmbedding ⟨mem_top _, hb, hd⟩
    have heq : baseEmbedding (x.1, a, c) * baseEmbedding (1, b, d) = x := by
      rw [← map_mul]
      change baseEmbedding (x.1 * 1, a * b, c * d) = x
      rw [mul_one, hab, hcd]
      exact embedding_coordinates x hx
    rw [← heq]
    exact (elementaryBase 0 0 ⊔ elementaryBase 1 1).mul_mem
      ((le_sup_left : elementaryBase 0 0 ≤ elementaryBase 0 0 ⊔ elementaryBase 1 1) hu)
      ((le_sup_right : elementaryBase 1 1 ≤ elementaryBase 0 0 ⊔ elementaryBase 1 1) hv)
  · exact sup_le (elementaryBase_le 0 0) (elementaryBase_le 1 1)

/-- The intrinsic elementary Thompson subgroup is exactly C₂ × D₈ × D₈. -/
theorem maxJ_model : elementaryAbelianMaxJ (⊤ : Subgroup P) = base := by
  apply le_antisymm
  · apply sSup_le
    intro A hA
    by_contra hAb
    have hsmall := elementary_outside_card A hA.2.1 hAb
    have hlarge := hA.2.2 _ le_top (elementaryBase_elementary 0 0)
    rw [elementaryBase_card] at hlarge
    omega
  · rw [base_eq_sup]
    exact sup_le (le_sSup (elementaryBase_maximal 0 0))
      (le_sSup (elementaryBase_maximal 1 1))

/-- The product of the centers of the two dihedral factors. -/
def fourGroup : Subgroup P where
  carrier := {x | x.1 = 1 ∧ x ∈ base ∧ ∀ q, x.2.left q ∈ center D8}
  one_mem' := ⟨rfl, rfl, fun _ => (center D8).one_mem⟩
  mul_mem' := by
    intro x y hx hy
    refine ⟨?_, base.mul_mem hx.2.1 hy.2.1, ?_⟩
    · change x.1 * y.1 = 1
      rw [hx.1, hy.1, mul_one]
    · intro q
      change x.2.left q * y.2.left (x.2.right⁻¹ * q) ∈ center D8
      exact (center D8).mul_mem (hx.2.2 _) (hy.2.2 _)
  inv_mem' := by
    intro x hx
    refine ⟨?_, base.inv_mem hx.2.1, ?_⟩
    · change x.1⁻¹ = 1
      rw [hx.1, inv_one]
    · intro q
      exact (center D8).inv_mem (hx.2.2 (x.2.right * q))

instance (x : P) : Decidable (x ∈ fourGroup) :=
  inferInstanceAs (Decidable (x.1 = 1 ∧ x ∈ base ∧ ∀ q, x.2.left q ∈ center D8))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem fourGroup_card : Nat.card fourGroup = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem fourGroup_squares : ∀ x ∈ fourGroup, x ^ 2 = 1 := by decide +kernel

instance fourGroup_elementary : IsElementaryAbelian 2 fourGroup :=
  elementary_of_square fun x => Subtype.ext (fourGroup_squares x.val x.property)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem square_mem_fourGroup : ∀ x ∈ base, x ^ 2 ∈ fourGroup := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem fourGroup_square_roots : ∀ x ∈ fourGroup, ∃ y : P, y ∈ base ∧ y ^ 2 = x := by
  decide +kernel

/-- Computing Φ(base) by its square generators gives exactly the central four-group. -/
theorem frattini_base : (frattini base).map base.subtype = fourGroup := by
  apply le_antisymm
  · rw [map_le_iff_le_comap, base_isPGroup.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    exact square_mem_fourGroup x.val x.property
  · intro x hx
    obtain ⟨y, hy, hy2⟩ := fourGroup_square_roots x hx
    let yb : base := ⟨y, hy⟩
    have hmem : yb ^ 2 ∈ frattini base := by
      rw [base_isPGroup.frattini_eq_closure_squares]
      exact subset_closure ⟨yb, rfl⟩
    exact ⟨yb ^ 2, hmem, hy2⟩

/-- First omega is retained explicitly and equals Φ(base) in this model. -/
theorem omegaFrattini_base : base.omegaFrattini = fourGroup := by
  rw [Subgroup.omegaFrattini, frattini_base, omegaOneAmbient_eq_self]

theorem thompsonFrattiniOmega_model : thompsonFrattiniOmega (⊤ : Subgroup P) = fourGroup := by
  rw [thompsonFrattiniOmega, maxJ_model, omegaFrattini_base]

def s1 : P := baseEmbedding (1, DihedralGroup.r 2,1)
def s2 : P := baseEmbedding (1,1, DihedralGroup.r 2)

theorem s1_mem : s1 ∈ fourGroup := by decide +kernel
theorem s2_mem : s2 ∈ fourGroup := by decide +kernel

theorem fourGroup_generated : fourGroup = zpowers s1 ⊔ zpowers s2 := by
  apply le_antisymm
  · have h : ∀ x ∈ fourGroup, x = 1 ∨ x = s1 ∨ x = s2 ∨ x = s1 * s2 := by decide +kernel
    intro x hx
    have h1 : s1 ∈ zpowers s1 ⊔ zpowers s2 :=
      (le_sup_left : zpowers s1 ≤ zpowers s1 ⊔ zpowers s2) (mem_zpowers s1)
    have h2 : s2 ∈ zpowers s1 ⊔ zpowers s2 :=
      (le_sup_right : zpowers s2 ≤ zpowers s1 ⊔ zpowers s2) (mem_zpowers s2)
    rcases h x hx with rfl | rfl | rfl | rfl
    · exact one_mem _
    · exact h1
    · exact h2
    · exact (zpowers s1 ⊔ zpowers s2).mul_mem h1 h2
  · exact sup_le (zpowers_le.mpr s1_mem) (zpowers_le.mpr s2_mem)

theorem switch_s1 : switch * s1 * switch⁻¹ = s2 := by decide +kernel
theorem switch_s2 : switch * s2 * switch⁻¹ = s1 := by decide +kernel

theorem noncentral_model : ¬ (⊤ : Subgroup P) ≤ centralizer (fourGroup : Set P) := by
  intro h
  have hh := h (mem_top switch) s1 s1_mem
  have hne : s1 * switch ≠ switch * s1 := by decide +kernel
  exact hne hh

/-- The first and second embedded dihedral groups. -/
def axis1 : D8 →* P := baseEmbedding.comp ((MonoidHom.inr C2 (D8 × D8)).comp (MonoidHom.inl D8 D8))
def axis2 : D8 →* P := baseEmbedding.comp ((MonoidHom.inr C2 (D8 × D8)).comp (MonoidHom.inr D8 D8))
def S1 : Subgroup P := axis1.range
def S2 : Subgroup P := axis2.range

theorem axis1_injective : Function.Injective axis1 := by
  intro a b h
  have hh := embedding_injective h
  exact congrArg (fun x : C2 × (D8 × D8) => x.2.1) hh

theorem axis2_injective : Function.Injective axis2 := by
  intro a b h
  have hh := embedding_injective h
  exact congrArg (fun x : C2 × (D8 × D8) => x.2.2) hh

noncomputable def S1_equiv : S1 ≃* D8 := (MonoidHom.ofInjective axis1_injective).symm
noncomputable def S2_equiv : S2 ≃* D8 := (MonoidHom.ofInjective axis2_injective).symm

/-- The intrinsic direct-product identification with the actual two base factors. -/
noncomputable def baseFactorsEquiv : base ≃* C2 × (S1 × S2) :=
  baseEquiv.trans (MulEquiv.prodCongr (MulEquiv.refl C2)
    (MulEquiv.prodCongr S1_equiv.symm S2_equiv.symm))

private theorem dihedral_center : center D8 = zpowers (DihedralGroup.r 2) := by
  apply le_antisymm
  · have h : ∀ d ∈ center D8, d = 1 ∨ d = DihedralGroup.r 2 := by decide +kernel
    intro d hd
    rcases h d hd with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · exact zpowers_le.mpr (by decide +kernel)

private theorem range_center_map {H K : Type*} [Group H] [Group K]
    (f : H →* K) (hf : Function.Injective f) :
    (center f.range).map f.range.subtype = (center H).map f := by
  let e := MonoidHom.ofInjective hf
  apply le_antisymm
  · rintro x ⟨z, hz, hzx⟩
    exact ⟨e.symm z, ((centerCongr e.symm) ⟨z, hz⟩).property,
      (congrArg Subtype.val (e.apply_symm_apply z)).trans hzx⟩
  · rintro x ⟨d, hd, rfl⟩
    exact ⟨e d, ((centerCongr e) ⟨d, hd⟩).property, rfl⟩

theorem center_S1 : (center S1).map S1.subtype = zpowers s1 := by
  rw [S1, range_center_map axis1 axis1_injective, dihedral_center, MonoidHom.map_zpowers]
  rfl

theorem center_S2 : (center S2).map S2.subtype = zpowers s2 := by
  rw [S2, range_center_map axis2 axis2_injective, dihedral_center, MonoidHom.map_zpowers]
  rfl

/-- The displayed product equality is also an internal generation equality in P. -/
theorem base_internal_product : base =
    (⊤ : Subgroup C2).prod (⊥ : Subgroup (RegularWreathProduct D8 C2)) ⊔ S1 ⊔ S2 := by
  let C : Subgroup P := (⊤ : Subgroup C2).prod (⊥ : Subgroup (RegularWreathProduct D8 C2))
  have hC : C ≤ base := by
    rintro ⟨c, w⟩ ⟨_, hw⟩
    change w.right = 1
    rw [show w = 1 from hw]
    rfl
  have h1 : S1 ≤ base := by
    rintro x ⟨d, rfl⟩
    rfl
  have h2 : S2 ≤ base := by
    rintro x ⟨d, rfl⟩
    rfl
  apply le_antisymm
  · intro x hx
    have hc : (x.1,1) ∈ C ⊔ S1 ⊔ S2 :=
      (le_sup_left.trans le_sup_left : C ≤ C ⊔ S1 ⊔ S2) ⟨mem_top _, mem_bot.mpr rfl⟩
    have ha : axis1 (x.2.left 1) ∈ C ⊔ S1 ⊔ S2 :=
      (le_sup_right.trans le_sup_left : S1 ≤ C ⊔ S1 ⊔ S2) ⟨_, rfl⟩
    have hb : axis2 (x.2.left tau) ∈ C ⊔ S1 ⊔ S2 :=
      (le_sup_right : S2 ≤ C ⊔ S1 ⊔ S2) ⟨_, rfl⟩
    have heq : (x.1,1) * axis1 (x.2.left 1) * axis2 (x.2.left tau) = x := by
      have hc' : (x.1, (1 : RegularWreathProduct D8 C2)) = baseEmbedding (x.1,1,1) := by
        simp only [baseEmbedding, MonoidHom.coe_mk, OneHom.coe_mk, ite_self]
        rfl
      rw [hc']
      change baseEmbedding (x.1,1,1) * baseEmbedding (1, x.2.left 1,1) *
        baseEmbedding (1,1, x.2.left tau) = x
      rw [← map_mul, ← map_mul]
      simpa [coordinates] using embedding_coordinates x hx
    rw [← heq]
    exact (C ⊔ S1 ⊔ S2).mul_mem ((C ⊔ S1 ⊔ S2).mul_mem hc ha) hb
  · exact sup_le (sup_le hC h1) h2

/-- The source's internal product formula for the elementary Thompson subgroup. -/
theorem maxJ_internal_product : elementaryAbelianMaxJ (⊤ : Subgroup P) =
    (⊤ : Subgroup C2).prod (⊥ : Subgroup (RegularWreathProduct D8 C2)) ⊔ S1 ⊔ S2 :=
  maxJ_model.trans base_internal_product

/-- This is an actual direct-product isomorphism for J(P), using the embedded factors. -/
noncomputable def maxJFactorsEquiv :
    elementaryAbelianMaxJ (⊤ : Subgroup P) ≃* C2 × (S1 × S2) :=
  (MulEquiv.subgroupCongr maxJ_model).trans baseFactorsEquiv

/-- The source's two central involutions generate exactly Ω₁(Φ(J(P))). -/
theorem thompsonFrattiniOmega_generated :
    thompsonFrattiniOmega (⊤ : Subgroup P) = zpowers s1 ⊔ zpowers s2 :=
  thompsonFrattiniOmega_model.trans fourGroup_generated

/-- The explicitly constructed switch has order two. -/
theorem switch_orderOf : orderOf switch = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

variable {G : Type*} [Group G]

/-- Realize the model in the supplied ambient subgroup, using the actual equivalence. -/
def modelEmbedding (S : Subgroup G) (e : S ≃* P) : P →* G :=
  S.subtype.comp e.symm.toMonoidHom

theorem modelEmbedding_injective (S : Subgroup G) (e : S ≃* P) :
    Function.Injective (modelEmbedding S e) := S.subtype_injective.comp e.symm.injective

theorem modelEmbedding_range (S : Subgroup G) (e : S ≃* P) :
    (modelEmbedding S e).range = S := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    exact (e.symm x).property
  · intro x hx
    refine ⟨e ⟨x, hx⟩, ?_⟩
    change (e.symm (e ⟨x, hx⟩) : G) = x
    simp

private theorem modelEmbedding_top (S : Subgroup G) (e : S ≃* P) :
    (⊤ : Subgroup P).map (modelEmbedding S e) = S := by
  rw [← MonoidHom.range_eq_map, modelEmbedding_range]

theorem isPGroup_of_equiv (S : Subgroup G) (e : S ≃* P) : IsPGroup 2 S :=
  model_isPGroup.of_injective e.toMonoidHom e.injective

/-- The calculation of J(P) transports through an injective model realization. -/
theorem maxJ_of_equiv (S : Subgroup G) (e : S ≃* P) :
    elementaryAbelianMaxJ S = base.map (modelEmbedding S e) := by
  calc
    elementaryAbelianMaxJ S = elementaryAbelianMaxJ ((⊤ : Subgroup P).map (modelEmbedding S e)) :=
      congrArg elementaryAbelianMaxJ (modelEmbedding_top S e).symm
    _ = base.map (modelEmbedding S e) := by
      rw [elementaryAbelianMaxJ_map_injective (modelEmbedding S e)
        (modelEmbedding_injective S e), maxJ_model]

/-- Every elementary two-subgroup of S has order at most 32. -/
theorem elementary_card_le_of_equiv (S : Subgroup G) (e : S ≃* P)
    (A : Subgroup G) (hAS : A ≤ S) (hA : IsElementaryAbelian 2 A) : Nat.card A ≤ 32 := by
  let := hA
  have : IsElementaryAbelian 2 (A.subgroupOf S) := IsElementaryAbelian.subgroupOf hAS
  have hbound := elementary_card_le ((A.subgroupOf S).map e.toMonoidHom)
    (IsElementaryAbelian.map e.toMonoidHom)
  rw [card_map_of_injective e.injective,
    Nat.card_congr (subgroupOfEquivOfLe hAS).toEquiv] at hbound
  exact hbound

variable [Finite G]

/-- An actual equivalence to the local Sylow model forces maximum two-rank five. -/
theorem twoRank_of_equiv (S : Subgroup G) (e : S ≃* P) : ChapterB.twoRank S = 5 := by
  let f := modelEmbedding S e
  let E := (elementaryBase 0 0).map f
  have hEcard : Nat.card E = 32 :=
    (card_map_of_injective (modelEmbedding_injective S e)).trans (elementaryBase_card 0 0)
  have hEelem : IsElementaryAbelian 2 E := (elementaryBase_elementary 0 0).map f
  have hE : E ∈ elementaryAbelianMaxSubgroups S := by
    refine ⟨(map_le_range f _).trans (modelEmbedding_range S e).le, hEelem, ?_⟩
    intro A hAS hA
    rw [hEcard]
    exact elementary_card_le_of_equiv S e A hAS hA
  have hm : elementaryAbelianMaxOrder S = 32 :=
    (elementaryAbelianMaxSubgroups_card_eq S E hE).symm.trans hEcard
  rw [ChapterB.twoRank, hm]
  decide

private theorem frattini_base_map (f : P →* G) :
    (frattini (base.map f)).map (base.map f).subtype = fourGroup.map f := by
  have htwo := base_isPGroup.map f
  apply le_antisymm
  · rw [map_le_iff_le_comap, htwo.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨x, rfl⟩
    obtain ⟨b, hb, hbx⟩ := x.property
    change x.val ^ 2 ∈ fourGroup.map f
    rw [← hbx, ← map_pow]
    exact mem_map_of_mem f (square_mem_fourGroup b hb)
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨b, hb, hbu⟩ := fourGroup_square_roots u hu
    let b' : base.map f := ⟨f b, mem_map_of_mem f hb⟩
    have hmem : b' ^ 2 ∈ frattini (base.map f) := by
      rw [htwo.frattini_eq_closure_squares]
      exact subset_closure ⟨b', rfl⟩
    refine ⟨b' ^ 2, hmem, ?_⟩
    change (f b) ^ 2 = f u
    rw [← map_pow, hbu]

/-- The transported subgroup is exactly the image of the computed four-group. -/
theorem thompsonFrattiniOmega_of_equiv (S : Subgroup G) (e : S ≃* P) :
    thompsonFrattiniOmega S = fourGroup.map (modelEmbedding S e) := by
  rw [thompsonFrattiniOmega, maxJ_of_equiv S e, Subgroup.omegaFrattini, frattini_base_map]
  have : IsElementaryAbelian 2 (fourGroup.map (modelEmbedding S e)) :=
    IsElementaryAbelian.map _
  exact omegaOneAmbient_eq_self _

theorem thompsonFrattiniOmega_card_of_equiv (S : Subgroup G) (e : S ≃* P) :
    Nat.card (thompsonFrattiniOmega S) = 4 := by
  rw [thompsonFrattiniOmega_of_equiv S e, card_map_of_injective (modelEmbedding_injective S e),
    fourGroup_card]

theorem thompsonFrattiniOmega_elementary_of_equiv (S : Subgroup G) (e : S ≃* P) :
    IsElementaryAbelian 2 (thompsonFrattiniOmega S) := by
  rw [thompsonFrattiniOmega_of_equiv S e]
  exact IsElementaryAbelian.map _

/-- The switch still acts nontrivially after realizing P as the actual subgroup S. -/
theorem noncentral_of_equiv (S : Subgroup G) (e : S ≃* P) :
    ¬ S ≤ centralizer (thompsonFrattiniOmega S : Set G) := by
  intro h
  apply noncentral_model
  intro x _ u hu
  apply modelEmbedding_injective S e
  rw [map_mul, map_mul]
  apply h (by exact (e.symm x).property)
  rw [thompsonFrattiniOmega_of_equiv S e]
  exact mem_map_of_mem (modelEmbedding S e) hu

/-- The full output consumed by the terminal Thompson obstruction. -/
theorem local_calculation (S : Subgroup G) (e : S ≃* P) :
    ChapterB.twoRank S = 5 ∧ Nat.card (thompsonFrattiniOmega S) = 4 ∧
      ¬ S ≤ centralizer (thompsonFrattiniOmega S : Set G) :=
  ⟨twoRank_of_equiv S e, thompsonFrattiniOmega_card_of_equiv S e, noncentral_of_equiv S e⟩

end CFSG.Quasithin.Chapter16.ThompsonObstruction.LocalComputation
