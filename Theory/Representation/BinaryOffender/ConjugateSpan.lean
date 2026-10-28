module
public import Theory.Representation.BinaryOffender.EndFieldTransfer
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.ConjugateSpanCentralizer

/-!
# Conjugate spans of internal non-FF modules

The cardinal offender criterion uses the actual conjugation map and identifies
its kernel and fixed vectors with the two relative centralizers. For an
equal-order conjugate actor, non-FF forces a strict inequality between those
centralizer orders. Conjugation by the inverse element reverses that inequality,
so all conjugates commute with the original elementary module. Its full
conjugate span is therefore elementary. Only the local acting group and module
are finite; the ambient group need not be finite.
Source: Aschbacher–Smith, D.1.2(1), printed p.172.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Representation.BinaryOffender
variable {G X : Type*} [Group G] [Group X]

/-- The actual cardinal criterion for a conjugation offender. -/
theorem isFF_of_conjugation_card
    (H V A : Subgroup G) [Finite H] [Finite V] [Finite X]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 A]
    (q : H →* X) (ρ : Representation (ZMod 2) X (Additive V))
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf H)
    (he : ∀ (h : H) (v : Additive V),
      ((ρ (q h) v).toMul : G) = (h : G) * v.toMul * (h : G)⁻¹)
    (hAH : A ≤ H) (hnc : ¬ A ≤ centralizer (V : Set G))
    (hcard : Nat.card V * Nat.card (A ⊓ centralizer (V : Set G) : Subgroup G) ≤
      Nat.card A * Nat.card (V ⊓ centralizer (A : Set G) : Subgroup G)) :
    IsFFModule ρ := by
  let f := q.comp (inclusion hAH)
  let B := f.range
  let C := A ⊓ centralizer (V : Set G)
  let D := V ⊓ centralizer (A : Set G)
  have hkf : f.ker = C.subgroupOf A := by
    ext a
    change inclusion hAH a ∈ q.ker ↔ (a : G) ∈ C
    rw [hk]
    exact ⟨fun h => ⟨a.property,h⟩, fun h => h.2⟩
  have hb : IsElementaryTwo B := by
    refine ⟨?_,IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective⟩
    intro hbot
    apply hnc
    intro a ha
    have ham : f ⟨a,ha⟩ ∈ B := ⟨_,rfl⟩
    rw [hbot] at ham
    have hak : (⟨a,ha⟩ : A) ∈ f.ker := ham
    rw [hkf] at hak
    exact hak.2
  have hm : Nat.card C * Nat.card B = Nat.card A := by
    have hh := f.ker.card_mul_index
    rw [index_ker, hkf, Nat.card_congr (subgroupOfEquivOfLe (show C ≤ A from inf_le_left)).toEquiv] at hh
    exact hh
  let E : fixedSpace ρ B ≃ D := {
    toFun := fun v => ⟨v.val.toMul,v.val.toMul.property,by
      intro a ha
      have hh := congrArg (fun w : Additive V => (w.toMul : G))
        (v.property ⟨f ⟨a,ha⟩,⟨_,rfl⟩⟩)
      change ((ρ (q (inclusion hAH ⟨a,ha⟩)) v.val).toMul : G) = v.val.toMul at hh
      rw [he] at hh
      exact mul_inv_eq_iff_eq_mul.mp hh⟩
    invFun := fun v => ⟨Additive.ofMul ⟨v,v.property.1⟩,by
      intro b
      obtain ⟨a,ha⟩ := b.property
      apply Additive.toMul.injective
      apply Subtype.ext
      change ((ρ b.val (Additive.ofMul ⟨v,v.property.1⟩)).toMul : G) = v
      rw [← ha]
      change ((ρ (q (inclusion hAH a)) _).toMul : G) = v
      rw [he]
      change (a : G) * (v : G) * (a : G)⁻¹ = v
      rw [v.property.2 a a.property,mul_inv_cancel_right]⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  refine ⟨B,(EndFieldTransfer.offender_iff_card ρ B hb).mpr ?_⟩
  rw [Nat.card_congr E]
  change Nat.card V ≤ Nat.card B * Nat.card D
  have hc : Nat.card C * Nat.card V ≤ Nat.card C * (Nat.card B * Nat.card D) := by
    change Nat.card V * Nat.card C ≤ Nat.card A * Nat.card D at hcard
    rw [← hm] at hcard
    simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hcard
  let : Finite A := Finite.of_injective (inclusion hAH) (inclusion_injective hAH)
  let : Finite C := Finite.of_injective (inclusion (show C ≤ A from inf_le_left))
    (inclusion_injective inf_le_left)
  exact Nat.le_of_mul_le_mul_left hc Nat.card_pos

end Representation.BinaryOffender

namespace Representation.BinaryOffender
variable {G X : Type*} [Group G] [Group X]
private theorem centralizer_map_equiv (V : Subgroup G) (f : G ≃* G) :
    (centralizer (V : Set G)).map f.toMonoidHom =
      centralizer (V.map f.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨f.symm x, ?_, f.apply_symm_apply x⟩
    intro y hy
    apply f.injective
    simpa only [map_mul, f.apply_symm_apply] using hx (f y) (mem_map_of_mem _ hy)

private theorem card_conjugate_centralizer (V : Subgroup G) (g : G) :
    Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) : Subgroup G) =
      Nat.card (V ⊓ centralizer (V.map (MulAut.conj g⁻¹).toMonoidHom : Set G) : Subgroup G) := by
  have hi : (V.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom = V := by
    rw [map_map]
    have he : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
      ext x
      simp only [MonoidHom.coe_comp,Function.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,MonoidHom.id_apply]
      group
    rw [he,map_id]
  have hc := card_map_of_injective (K := V ⊓ centralizer
    (V.map (MulAut.conj g⁻¹).toMonoidHom : Set G))
    (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  rw [map_inf _ _ _ (MulAut.conj g).injective,centralizer_map_equiv,hi] at hc
  exact hc

/-- Equal-order conjugate actors cannot move a non-FF internal module. -/
theorem conjugateSpan_elementary_of_notFF
    (H L V : Subgroup G) [Finite H] [Finite V] [Finite X]
    [IsElementaryAbelian 2 V]
    (q : H →* X) (ρ : Representation (ZMod 2) X (Additive V))
    (hk : q.ker = (centralizer (V : Set G)).subgroupOf H)
    (he : ∀ (h : H) (v : Additive V),
      ((ρ (q h) v).toMul : G) = (h : G) * v.toMul * (h : G)⁻¹)
    (hconj : ∀ g ∈ L, V.map (MulAut.conj g).toMonoidHom ≤ H)
    (hnf : ¬ IsFFModule ρ) : IsElementaryAbelian 2 (conjugateSpanBy V L) := by
  have hh (g : G) (hg : g ∈ L)
      (hnc : ¬ V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G)) :
      Nat.card (V ⊓ centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) <
        Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) : Subgroup G) := by
    let A := V.map (MulAut.conj g).toMonoidHom
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
    have hc : Nat.card A = Nat.card V := card_map_of_injective (MulAut.conj g).injective
    have hn := fun h => hnf (isFF_of_conjugation_card H V A q ρ hk he (hconj g hg) hnc h)
    have hl := Nat.lt_of_not_ge hn
    rw [hc] at hl
    exact (Nat.mul_lt_mul_left Nat.card_pos).mp hl
  have hc (g : G) (hg : g ∈ L) : V.map (MulAut.conj g).toMonoidHom ≤ centralizer (V : Set G) := by
    by_contra hn
    have hni : ¬ V.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer (V : Set G) := by
      intro hi
      have hm := map_mono (f := (MulAut.conj g).toMonoidHom) hi
      rw [centralizer_map_equiv,map_map] at hm
      have heq : (MulAut.conj g).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom = MonoidHom.id G := by
        ext x
        simp only [MonoidHom.coe_comp,Function.comp_apply,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,MonoidHom.id_apply]
        group
      rw [heq,map_id] at hm
      exact hn (le_centralizer_iff.mp hm)
    have h1 := hh g hg hn
    have h2 := hh g⁻¹ (L.inv_mem hg) hni
    rw [card_conjugate_centralizer] at h1 h2
    simp only [inv_inv] at h2
    exact (lt_asymm h1 h2)
  have hspan : conjugateSpanBy V L ≤ centralizer (V : Set G) := by
    apply (closure_le _).mpr
    rintro x ⟨g,hg,v,hv,rfl⟩
    exact hc g hg (mem_map_of_mem _ hv)
  let : IsMulCommutative (conjugateSpanBy V L) :=
    (conjugateSpanBy_commutative_iff V L).mpr (le_centralizer_iff.mp hspan)
  exact conjugateSpanBy_elementary_of_commutative V L
end Representation.BinaryOffender

