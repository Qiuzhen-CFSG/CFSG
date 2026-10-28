module

public import Theory.SpecificGroups.SymmetricFourWreath.Planes
public import Theory.ElementaryAbelian.Injective
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.GroupTheory.Subgroup.Center

/-!
# Cubic automorphisms of products of square-dihedral groups

The largest elementary subgroups of D₈^I × E, for E elementary abelian,
are the products of the two four-groups in each dihedral coordinate with E.
They form a Boolean cube. Each member has a unique opposite, characterized
by intersection equal to the center. A cubic automorphism fixes a member
because three does not divide the size of the cube, and fixes its opposite.
In particular, a fixed member can be prescribed to use either four-group at
one coordinate.

This supplies the dihedral-product exclusion in Goldschmidt, Automorphisms
of trivalent graphs (1980), §2.15, printed p.385, without a bound on the
number of dihedral factors.
-/

@[expose] public section
namespace DihedralCubeAutomorphisms
open Subgroup SymmetricFourWreath
open scoped IsMulCommutative

abbrev Model (I E : Type*) := (I → D8) × E

variable {I E : Type*} [Group E]

/-- A vertex of the cube of largest elementary subgroups. -/
def family (b : I → Bool) : Subgroup (Model I E) where
  carrier := {x | ∀ i, x.1 i ∈ plane (b i)}
  one_mem' i := (plane (b i)).one_mem
  mul_mem' hx hy i := (plane (b i)).mul_mem (hx i) (hy i)
  inv_mem' hx i := (plane (b i)).inv_mem (hx i)

private def familyEquiv (b : I → Bool) :
    family (E := E) b ≃* ((i : I) → plane (b i)) × E where
  toFun x := (fun i => ⟨x.1.1 i, x.2 i⟩, x.1.2)
  invFun x := ⟨(fun i => (x.1 i).1, x.2), fun i => (x.1 i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

instance family_elementary [IsElementaryAbelian 2 E] (b : I → Bool) :
    IsElementaryAbelian 2 (family (E := E) b) where
  is_comm.comm x y := by
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨x.1.1 i, x.2 i⟩ : plane (b i)) ⟨y.1.1 i, y.2 i⟩)
    · exact IsMulCommutative.is_comm.comm _ _
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    intro x
    apply Subtype.ext
    apply Prod.ext
    · funext i
      exact elemPow_eq_one_of_isElementaryAbelian (x.1.1 i) (x.2 i)
    · exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 E) x.1.2)

private theorem family_card [Fintype I] (b : I → Bool) :
    Nat.card (family (E := E) b) = 4 ^ Fintype.card I * Nat.card E := by
  rw [Nat.card_congr (familyEquiv b).toEquiv, Nat.card_prod, Nat.card_pi]
  simp only [card_plane, Finset.prod_const, Finset.card_univ]

private theorem elementary_cover (A : Subgroup (Model I E))
    (hA : IsElementaryAbelian 2 A) : ∃ b, A ≤ family b := by
  classical
  have hcoord (i : I) : ∃ b, ∀ x ∈ A, x.1 i ∈ plane b := by
    by_cases ht : ∀ x ∈ A, x.1 i ∈ plane true
    · exact ⟨true, ht⟩
    push Not at ht
    obtain ⟨x, hx, hxt⟩ := ht
    refine ⟨false, fun y hy => ?_⟩
    have hlocal : ∀ u v : D8, u ^ 2 = 1 → v ^ 2 = 1 → u * v = v * u →
        u ∉ plane true → v ∈ plane false := by decide +kernel
    let : IsElementaryAbelian 2 A := hA
    apply hlocal (x.1 i) (y.1 i)
    · exact congrArg (fun z : Model I E => z.1 i)
        (elemPow_eq_one_of_isElementaryAbelian x hx)
    · exact congrArg (fun z : Model I E => z.1 i)
        (elemPow_eq_one_of_isElementaryAbelian y hy)
    · exact congrArg (fun z : A => z.1.1 i)
        (hA.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
    · exact hxt
  choose b hb using hcoord
  exact ⟨b, fun x hx i => hb i x hx⟩

private theorem family_update [DecidableEq I] (b : I → Bool) (i : I) (u : D8) :
    (Function.update (1 : I → D8) i u, (1 : E)) ∈ family b ↔ u ∈ plane (b i) := by
  constructor
  · intro h
    simpa only [Function.update_self] using h i
  · intro h j
    by_cases hj : j = i
    · subst j; simpa only [Function.update_self] using h
    · simpa only [Function.update_of_ne hj, Pi.one_apply] using (plane (b j)).one_mem

private theorem family_injective :
    Function.Injective (family (I := I) (E := E)) := by
  classical
  intro b c he
  funext i
  have hcheck : ∀ b c : Bool, (∀ u : D8, u ∈ plane b ↔ u ∈ plane c) → b = c := by
    decide +kernel
  apply hcheck
  intro u
  have h := SetLike.ext_iff.mp he (Function.update (1 : I → D8) i u, (1 : E))
  simpa only [family_update] using h

variable [Fintype I] [Finite E] [IsElementaryAbelian 2 E]

private theorem exists_family_image (a : MulAut (Model I E)) (b : I → Bool) :
    ∃ c, (family b).map a.toMonoidHom = family c := by
  obtain ⟨c, hc⟩ := elementary_cover ((family b).map a.toMonoidHom)
    (IsElementaryAbelian.map a.toMonoidHom)
  exact ⟨c, eq_of_le_of_card_ge hc (by
    rw [card_map_of_injective a.injective, family_card, family_card])⟩

private noncomputable def familyMap (a : MulAut (Model I E)) (b : I → Bool) : I → Bool :=
  Classical.choose (exists_family_image a b)

private theorem familyMap_spec (a : MulAut (Model I E)) (b : I → Bool) :
    (family b).map a.toMonoidHom = family (familyMap a b) :=
  Classical.choose_spec (exists_family_image a b)

private theorem familyMap_injective (a : MulAut (Model I E)) :
    Function.Injective (familyMap a) := by
  intro b c he
  apply family_injective (E := E)
  apply map_injective (f := a.toMonoidHom) a.injective
  rw [familyMap_spec, familyMap_spec, he]

private noncomputable def familyAction : MulAut (Model I E) →* Equiv.Perm (I → Bool) where
  toFun a := Equiv.ofBijective (familyMap a)
    ⟨familyMap_injective a, Finite.surjective_of_injective (familyMap_injective a)⟩
  map_one' := by
    apply Equiv.ext
    intro b
    apply family_injective (E := E)
    exact (familyMap_spec 1 b).symm.trans (by ext x; simp)
  map_mul' a c := by
    apply Equiv.ext
    intro b
    apply family_injective (E := E)
    change family (familyMap (a * c) b) = family (familyMap a (familyMap c b))
    rw [← familyMap_spec, ← familyMap_spec, ← familyMap_spec, map_map]
    rfl

omit [Fintype I] [Finite E] in
private theorem opposite_iff (b c : I → Bool) :
    family (E := E) b ⊓ family c = center (Model I E) ↔ c = fun i => !(b i) := by
  classical
  have hlocal : ∀ b c : Bool,
      (∀ u : D8, (u ∈ plane b ∧ u ∈ plane c) ↔ u ∈ center D8) ↔ c = !b := by
    decide +kernel
  have hcenter (x : Model I E) : x ∈ center (Model I E) ↔ ∀ i, x.1 i ∈ center D8 := by
    rw [Subgroup.center_prod, Subgroup.center_pi]
    simp only [mem_prod, mem_pi, Set.mem_univ, forall_true_left,
      center_eq_top, mem_top, and_true]
  constructor
  · intro he
    funext i
    apply (hlocal _ _).mp
    intro u
    have hh := SetLike.ext_iff.mp he (Function.update (1 : I → D8) i u, (1 : E))
    rw [mem_inf, family_update, family_update, hcenter] at hh
    refine hh.trans ?_
    constructor
    · intro h; simpa only [Function.update_self] using h i
    · intro h j
      by_cases hj : j = i
      · subst j; simpa only [Function.update_self] using h
      · simpa only [Function.update_of_ne hj, Pi.one_apply] using (center D8).one_mem
  · rintro rfl
    ext x
    rw [hcenter]
    change (∀ i, x.1 i ∈ plane (b i)) ∧ (∀ i, x.1 i ∈ plane (!(b i))) ↔ _
    rw [← forall_and]
    exact forall_congr' fun i => (hlocal _ _).mpr rfl (x.1 i)

private theorem familyAction_opposite (a : MulAut (Model I E)) (b : I → Bool) :
    familyAction a (fun i => !(b i)) = fun i => !(familyAction a b i) := by
  apply (opposite_iff (E := E) _ _).mp
  change family (familyMap a b) ⊓ family (familyMap a (fun i => !(b i))) = _
  rw [← familyMap_spec, ← familyMap_spec, ← Subgroup.map_inf _ _ _ a.injective,
    (opposite_iff b (fun i => !(b i))).mpr rfl]
  exact characteristic_iff_map_eq.mp inferInstance a

/-- A cubic automorphism preserves a largest elementary subgroup with either
prescribed four-group at any one dihedral coordinate. -/
theorem exists_invariant_family (a : MulAut (Model I E)) (ha : a ^ 3 = 1)
    (i : I) (value : Bool) :
    ∃ b : I → Bool, b i = value ∧ (family b).map a.toMonoidHom = family b := by
  classical
  have hcard : ¬ 3 ∣ Fintype.card (I → Bool) := by
    rw [Fintype.card_fun, Fintype.card_bool]
    exact fun h => (by decide : ¬ 3 ∣ 2) (Nat.Prime.dvd_of_dvd_pow (by decide) h)
  have hpow : familyAction a ^ (3 ^ 1) = 1 := by
    simp only [pow_one, ← map_pow, ha, map_one]
  obtain ⟨b, hb⟩ := Equiv.Perm.exists_fixed_point_of_prime hcard hpow
  have hfix : (family b).map a.toMonoidHom = family b := (familyMap_spec a b).trans
    (congrArg (family (E := E)) hb)
  by_cases hv : b i = value
  · exact ⟨b, hv, hfix⟩
  · refine ⟨fun j => !(b j), ?_, ?_⟩
    · cases hbi : b i <;> cases value <;> simp_all
    · exact (familyMap_spec a _).trans (congrArg (family (E := E)) (by
        change familyAction a (fun j => !(b j)) = _
        rw [familyAction_opposite, hb]))

end DihedralCubeAutomorphisms
