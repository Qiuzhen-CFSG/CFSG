module
public import Theory.ElementaryAbelian.Quotient
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Pure involution fusion in a dihedral pair

Every involution of D₈ × D₈ belongs to a product of elementary four-groups.
The six nonidentity elements on its two axes exhaust any fusion class
having at most six elements in that elementary sixteen. Thus a class
containing all pure involutions contains no mixed involution.

The two explicit four-groups of D₈ supply the covering; all tables involve
only D₈ or a group of order sixteen. The counting argument transports these
subgroups through the supplied marking to literal subgroups of the ambient
group before applying the local fusion bound.

Source: Aschbacher–Smith, 2.4.37, printed p.550, combined manuscript
of 1 March 2004. This lemma isolates its elementary counting argument.
-/

@[expose] public section
noncomputable section
namespace Theory.GroupTheory.DihedralPairPureFusion
open Subgroup
private def four (i : Fin 2) : Subgroup (DihedralGroup 4) where
  carrier := {x | x = 1 ∨ x = DihedralGroup.r 2 ∨
    x = DihedralGroup.sr i.val ∨ x = DihedralGroup.sr ((i.val : ZMod 4) + 2)}
  one_mem' := Or.inl rfl
  mul_mem' := by
    have h : ∀ (i : Fin 2) (x y : DihedralGroup 4),
        (x = 1 ∨ x = .r 2 ∨ x = .sr i.val ∨ x = .sr ((i.val : ZMod 4) + 2)) →
        (y = 1 ∨ y = .r 2 ∨ y = .sr i.val ∨ y = .sr ((i.val : ZMod 4) + 2)) →
        (x*y = 1 ∨ x*y = .r 2 ∨ x*y = .sr i.val ∨ x*y = .sr ((i.val : ZMod 4) + 2)) := by decide +kernel
    exact fun {x y} => h i x y
  inv_mem' := by
    have h : ∀ (i : Fin 2) (x : DihedralGroup 4),
        (x = 1 ∨ x = .r 2 ∨ x = .sr i.val ∨ x = .sr ((i.val : ZMod 4) + 2)) →
        (x⁻¹ = 1 ∨ x⁻¹ = .r 2 ∨ x⁻¹ = .sr i.val ∨ x⁻¹ = .sr ((i.val : ZMod 4) + 2)) := by decide +kernel
    exact fun {x} => h i x

private instance (i : Fin 2) : DecidablePred (fun x => x ∈ four i) :=
  fun x => show Decidable (x = 1 ∨ x = DihedralGroup.r 2 ∨
    x = DihedralGroup.sr i.val ∨ x = DihedralGroup.sr ((i.val : ZMod 4) + 2)) from inferInstance

private instance (i j : Fin 2) : DecidablePred (fun x => x ∈ (four i).prod (four j)) :=
  fun x => show Decidable (x.1 ∈ four i ∧ x.2 ∈ four j) from inferInstance

private theorem four_cover (x : DihedralGroup 4) (hx : x^2=1) :
    ∃ i : Fin 2, x ∈ four i := by
  have h : ∀ x : DihedralGroup 4, x^2=1 → ∃ i : Fin 2, x ∈ four i := by decide +kernel
  exact h x hx

private theorem pair_card (i j : Fin 2) : Nat.card ((four i).prod (four j)) = 16 := by
  rw [Nat.card_eq_fintype_card]
  revert i j
  decide +kernel

private instance pair_elementary (i j : Fin 2) : IsElementaryAbelian 2 ((four i).prod (four j)) where
  toIsMulCommutative := ⟨⟨by
    have h : ∀ (i j : Fin 2) (x y : (four i).prod (four j)), x*y=y*x := by decide +kernel
    exact h i j⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    have h : ∀ (i j : Fin 2) (x : (four i).prod (four j)), x^2=1 := by decide +kernel
    exact h i j)

private theorem pair_pure_card (i j : Fin 2) :
    Nat.card {x : (four i).prod (four j) // x ≠ 1 ∧ (x.val.1 = 1 ∨ x.val.2 = 1)} = 6 := by
  rw [Nat.card_eq_fintype_card]
  revert i j
  decide +kernel

/-- A six-point fusion bound on actual elementary sixteens excludes mixed
involutions in a marked dihedral pair. -/
theorem pure_of_elementary_sixteen_bound {G : Type*} [Group G] [Finite G]
    (z : G) (hz : z^2=1) (R : Subgroup G) (e : R ≃* (DihedralGroup 4 × DihedralGroup 4))
    (haxes : ∀ x : R, x^2=1 → x≠1 → (e x).1=1 ∨ (e x).2=1 → IsConj z (x:G))
    (hlocal : ∀ A : Subgroup G, A ≤ R → IsElementaryAbelian 2 A → Nat.card A=16 →
      Nat.card {a : A // IsConj z (a:G)} ≤ 6)
    (a : R) (ha : IsConj z (a:G)) : (e a).1=1 ∨ (e a).2=1 := by
  have ha2 : a^2=1 := Subtype.ext (isConj_one_right.mp (hz ▸ ha.pow 2))
  have he2 : (e a)^2=1 := by rw [←map_pow,ha2,map_one]
  obtain ⟨i,hi⟩ := four_cover (e a).1 (congrArg Prod.fst he2)
  obtain ⟨j,hj⟩ := four_cover (e a).2 (congrArg Prod.snd he2)
  let B := (four i).prod (four j)
  let f : B →* G := R.subtype.comp (e.symm.toMonoidHom.comp B.subtype)
  have hf : Function.Injective f := R.subtype_injective.comp (e.symm.injective.comp B.subtype_injective)
  let A := f.range
  have hAR : A ≤ R := by rintro _ ⟨b,rfl⟩; exact (e.symm b).property
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hAc : Nat.card A=16 := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans (pair_card i j)
  have hbound := hlocal A hAR inferInstance hAc
  let Pure := {x : B // x ≠ 1 ∧ (x.val.1=1 ∨ x.val.2=1)}
  let Fused := {x : A // IsConj z (x:G)}
  let m : Pure → Fused := fun x => ⟨⟨f x.val,⟨x.val,rfl⟩⟩, by
    apply haxes (e.symm x.val)
    · rw [←map_pow, show x.val.val^2=1 from congrArg Subtype.val
        (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 B) x.val),map_one]
    · intro h
      exact x.property.1 (Subtype.ext (e.symm.injective (h.trans e.symm.map_one.symm)))
    · simpa only [MulEquiv.apply_symm_apply] using x.property.2⟩
  have hm : Function.Injective m := by
    intro x y h
    exact Subtype.ext (hf (congrArg (fun t : Fused => (t.val:G)) h))
  have hms : Function.Surjective m := (hm.bijective_of_nat_card_le (by
    rw [show Nat.card Pure = 6 from pair_pure_card i j]
    exact hbound)).surjective
  let b : B := ⟨e a,hi,hj⟩
  have hfa : f b = a := by change (e.symm (e a):G)=(a:G); rw [e.symm_apply_apply]
  obtain ⟨x,hx⟩ := hms ⟨⟨f b,⟨b,rfl⟩⟩,by change IsConj z (f b); rw [hfa]; exact ha⟩
  have hxb : x.val=b := hf (congrArg (fun t : Fused => (t.val:G)) hx)
  simpa only [hxb] using x.property.2
end Theory.GroupTheory.DihedralPairPureFusion
