module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus

/-!
# The norm diagonal of two commuting conjugate components

If an involution a moves a component L, the map `l ↦ l (a l a⁻¹)`
is a homomorphism. Its kernel is central in L, and its image is a nontrivial
quasisimple group fixed by a. This constructs the actual diagonal map used
in GLS2, Lemma 3.27 and Theorem 25.14, rather than an abstract factor tag.
Identification of the entire centralizer layer is a separate assertion.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory

variable {G : Type*} [Group G] {L : Subgroup G} {a : G}

/-- Multiplication into the two commuting conjugate factors. -/
def componentSwapNorm (hL : IsComponent G L)
    (hm : L.map (MulAut.conj a).toMonoidHom ≠ L) : L →* G where
  toFun x := (x : G) * (MulAut.conj a) x
  map_one' := by simp
  map_mul' x y := by
    have hc := hL.commutator_eq_bot_of_ne (hL.map_conj a) hm.symm
    have hcomm : (y : G) * (MulAut.conj a) x = (MulAut.conj a) x * y :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc y.property)
        _ (mem_map_of_mem _ x.property)).symm
    change ((x : G) * y) * (MulAut.conj a) (x * y) = _
    rw [map_mul]
    calc
      ((x : G) * y) * ((MulAut.conj a) x * (MulAut.conj a) y) =
          x * (y * (MulAut.conj a) x) * (MulAut.conj a) y := by group
      _ = x * ((MulAut.conj a) x * y) * (MulAut.conj a) y := by rw [hcomm]
      _ = _ := by group

@[simp] theorem componentSwapNorm_apply (hL : IsComponent G L)
    (hm : L.map (MulAut.conj a).toMonoidHom ≠ L) (x : L) :
    componentSwapNorm hL hm x = (x : G) * (a * x * a⁻¹) := rfl

/-- The norm's kernel lies in the intrinsic centre of the component. -/
theorem componentSwapNorm_ker_le_center (hL : IsComponent G L)
    (hm : L.map (MulAut.conj a).toMonoidHom ≠ L) :
    (componentSwapNorm hL hm).ker ≤ center L := by
  intro x hx
  have he : (x : G) * (MulAut.conj a) x = 1 := hx
  have hxconj : (x : G) ∈ L.map (MulAut.conj a).toMonoidHom := by
    have hxinv : (MulAut.conj a) x ∈ L.map (MulAut.conj a).toMonoidHom :=
      mem_map_of_mem _ x.property
    have hxe : (x : G) = ((MulAut.conj a) x)⁻¹ :=
      (eq_inv_iff_mul_eq_one.mpr he)
    rw [hxe]
    exact inv_mem hxinv
  have hc := (hL.map_conj a).commutator_eq_bot_of_ne hL hm
  have hxC := commutator_eq_bot_iff_le_centralizer.mp hc hxconj
  apply mem_center_iff.mpr
  intro y
  apply Subtype.ext
  exact mem_centralizer_iff.mp hxC y y.property

/-- The genuine norm image is quasisimple, including for central products. -/
theorem componentSwapNorm_range_quasisimple (hL : IsComponent G L)
    (hm : L.map (MulAut.conj a).toMonoidHom ≠ L) :
    IsQuasisimple (componentSwapNorm hL hm).range := by
  let := hL.2
  let : IsSimpleGroup (L ⧸ center L) := IsQuasisimple.simple
  let : Nontrivial L := (QuotientGroup.mk'_surjective (center L)).nontrivial
  have hr : (componentSwapNorm hL hm).range ≠ ⊥ := by
    intro hr
    have hcenter : center L = ⊤ := by
      apply top_unique
      intro x _
      apply componentSwapNorm_ker_le_center hL hm
      have hx : componentSwapNorm hL hm x ∈ (componentSwapNorm hL hm).range := ⟨x, rfl⟩
      rw [hr, mem_bot] at hx
      exact hx
    exact Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp hcenter)
  let : Nontrivial (componentSwapNorm hL hm).range := (nontrivial_iff_ne_bot _).mpr hr
  exact IsQuasisimple.of_surjective (componentSwapNorm hL hm).rangeRestrict
    (componentSwapNorm hL hm).rangeRestrict_surjective

/-- An involution fixes each element of the norm diagonal. -/
theorem componentSwapNorm_range_le_centralizer (hL : IsComponent G L)
    (hm : L.map (MulAut.conj a).toMonoidHom ≠ L) (ha : a ^ 2 = 1) :
    (componentSwapNorm hL hm).range ≤ centralizer ({a} : Set G) := by
  rintro _ ⟨x, rfl⟩
  have haa : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ha)
  have hc := hL.commutator_eq_bot_of_ne (hL.map_conj a) hm.symm
  have hcomm : (x : G) * (a * x * a⁻¹) = (a * x * a⁻¹) * x :=
    (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hc x.property)
      _ (mem_map_of_mem _ x.property)).symm
  apply mem_centralizer_singleton_iff.mpr
  change ((x : G) * (a * x * a⁻¹)) * a = a * (x * (a * x * a⁻¹))
  calc
    _ = ((a * x * a⁻¹) * x) * a := by rw [hcomm]
    _ = _ := by rw [haa]; group

/-- The norm diagonal is contained in the actual orbit as soon as a belongs
to the acting subgroup. -/
theorem componentSwapNorm_range_le_orbit (hL : IsComponent G L)
    (hm : L.map (MulAut.conj a).toMonoidHom ≠ L) {B : Subgroup G} (ha : a ∈ B) :
    (componentSwapNorm hL hm).range ≤ componentOrbit L B := by
  rintro _ ⟨x, rfl⟩
  exact mul_mem (le_componentOrbit L B x.property)
    ((le_iSup (fun b : B => L.map (MulAut.conj (b : G)).toMonoidHom) ⟨a, ha⟩)
      (mem_map_of_mem _ x.property))

end Theory.GroupTheory

end
