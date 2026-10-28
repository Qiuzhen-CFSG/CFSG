module
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Coordinate subgroups of regular wreath products

For a subgroup H of D, the elements whose base coordinates lie in H form
the literal copy of H wr Q inside D wr Q. This copy is maximal whenever
D and Q are finite and H is maximal and self-normalizing.

An element outside the copy conjugates one coordinate subgroup to a
subgroup escaping H. Maximality then supplies the whole coordinate D;
the regular shifts supply every coordinate, which generate the base.

This is the elementary product-action argument used for the paired point
parabolic in Aschbacher--Smith 10.2.4 and 10.2.11, pp.747,753--754.
-/

public noncomputable section
open Subgroup
namespace RegularWreathProduct
variable {D Q : Type*} [Group D] [Group Q]

@[expose] def coordinateSubgroup (H : Subgroup D) : Subgroup (D ≀ᵣ Q) where
  carrier := {w | ∀ i, w.left i ∈ H}
  one_mem' := fun _ => H.one_mem
  mul_mem' ha hb i := H.mul_mem (ha i) (hb _)
  inv_mem' ha _i := H.inv_mem (ha _)

@[simp] theorem mem_coordinateSubgroup (H : Subgroup D) (w : D ≀ᵣ Q) :
    w ∈ coordinateSubgroup H ↔ ∀ i, w.left i ∈ H := Iff.rfl

/-- The coordinate subgroup is the wreath product of the factor subgroup. -/
def coordinateSubgroupEquiv (H : Subgroup D) :
    coordinateSubgroup (Q := Q) H ≃* (H ≀ᵣ Q) where
  toFun w := ⟨fun i => ⟨w.val.left i, w.property i⟩, w.val.right⟩
  invFun w := ⟨⟨fun i => (w.left i).val, w.right⟩, fun i => (w.left i).property⟩
  left_inv _w := rfl
  right_inv _w := rfl
  map_mul' _a _b := rfl

private def baseHom : (Q → D) →* (D ≀ᵣ Q) where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext <;> simp

private def coordinateHom [DecidableEq Q] (i : Q) : D →* (D ≀ᵣ Q) :=
  baseHom.comp (MonoidHom.mulSingle (fun _ : Q => D) i)

@[simp] private theorem coordinateHom_left [DecidableEq Q] (i : Q) (d : D) :
    (coordinateHom i d).left = Pi.mulSingle i d := rfl
@[simp] private theorem coordinateHom_right [DecidableEq Q] (i : Q) (d : D) :
    (coordinateHom i d).right = 1 := rfl

private theorem conj_coordinateHom [DecidableEq Q] (w : D ≀ᵣ Q) (i : Q) (d : D) :
    w * coordinateHom i d * w⁻¹ =
      coordinateHom (w.right * i) (w.left (w.right * i) * d * (w.left (w.right * i))⁻¹) := by
  apply RegularWreathProduct.ext
  · funext j
    by_cases h : j = w.right * i
    · subst j
      simp [Pi.mulSingle_apply, mul_assoc]
    · have h' : w.right⁻¹ * j ≠ i := by
        intro he
        apply h
        rw [← he, mul_inv_cancel_left]
      simp [Pi.mulSingle_apply, h, h', mul_assoc]
  · simp

private theorem coordinateHom_mem [DecidableEq Q] (H : Subgroup D) (i : Q) {d : D}
    (hd : d ∈ H) : coordinateHom i d ∈ coordinateSubgroup H := by
  intro j
  by_cases h : j = i <;> simp [h, hd]

private theorem inl_mem_coordinateSubgroup (H : Subgroup D) (q : Q) :
    (inl q : D ≀ᵣ Q) ∈ coordinateSubgroup H := fun _ => H.one_mem

/-- A self-normalizing maximal subgroup remains maximal in the regular product action. -/
theorem coordinateSubgroup_isCoatom [Finite D] [Finite Q] (H : Subgroup D)
    (hmax : IsCoatom H) (hn : normalizer (H : Set D) = H) :
    IsCoatom (coordinateSubgroup (Q := Q) H) := by
  classical
  refine ⟨?_, ?_⟩
  · intro he
    apply hmax.1
    apply top_unique
    intro d _
    have hd : coordinateHom (1 : Q) d ∈ coordinateSubgroup H := he ▸ mem_top _
    simpa using hd (1 : Q)
  · intro K hK
    obtain ⟨w, hwK, hw⟩ := SetLike.exists_of_lt hK
    obtain ⟨i, hi⟩ : ∃ i, w.left i ∉ H := by
      simpa only [mem_coordinateSubgroup, not_forall] using hw
    have hconj : H.map (MulAut.conj (w.left i)).toMonoidHom ≤
        K.comap (coordinateHom i) := by
      rintro _ ⟨d, hd, rfl⟩
      have hc := K.mul_mem (K.mul_mem hwK
        (hK.le (coordinateHom_mem H (w.right⁻¹ * i) hd))) (K.inv_mem hwK)
      rw [conj_coordinateHom] at hc
      change coordinateHom i (w.left i * d * (w.left i)⁻¹) ∈ K
      simpa only [mul_inv_cancel_left] using hc
    have hHi : H ≤ K.comap (coordinateHom i) := by
      intro d hd
      exact hK.le (coordinateHom_mem H i hd)
    have hstrict : H < K.comap (coordinateHom i) := lt_of_le_of_ne hHi (by
      intro he
      have hc : H.map (MulAut.conj (w.left i)).toMonoidHom ≤ H := he ▸ hconj
      have heq : H.map (MulAut.conj (w.left i)).toMonoidHom = H :=
        eq_of_le_of_card_ge hc (by
          rw [card_map_of_injective (MulAut.conj (w.left i)).injective])
      exact hi (hn ▸ mem_normalizer_iff_map_conj_eq.mpr heq))
    have hfull := hmax.2 _ hstrict
    have hall : ∀ j d, coordinateHom j d ∈ K := by
      intro j d
      have hd : coordinateHom i d ∈ K := by
        change d ∈ K.comap (coordinateHom i)
        rw [hfull]
        exact mem_top _
      have hs := hK.le (inl_mem_coordinateSubgroup H (j * i⁻¹))
      have hc := K.mul_mem (K.mul_mem hs hd) (K.inv_mem hs)
      rw [conj_coordinateHom] at hc
      simpa using hc
    apply top_unique
    intro g _
    have hb : baseHom g.left ∈ K := by
      exact Subgroup.pi_mem_of_mulSingle_mem (H := K.comap baseHom) g.left
        (fun i => hall i (g.left i))
    have hh := K.mul_mem hb (hK.le (inl_mem_coordinateSubgroup H g.right))
    convert hh using 1
    ext <;> simp [baseHom]
end RegularWreathProduct
