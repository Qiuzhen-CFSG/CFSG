module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.FFSelection.Existence.Setup
public import Mathlib.GroupTheory.Perm.Fin
public import Theory.ElementaryAbelian.AbelianNormalClosure

/-!
# Maximum-elementary witnesses for the literal preimage Thompson equality

A normal subgroup of S₃ containing a nonidentity involution is S₃.
Consequently a maximum elementary subgroup of the full preimage with
nontrivial image in a specified S₃ factor forces that factor into the
preimage's Thompson image. Two coordinate witnesses give the product.
All maps below are the original star quotient maps.

These are conditional closing lemmas. Constructing their maximum-elementary
witnesses from the native B.5.6 alternatives is a separate obligation; no
monotonicity of elementaryAbelianMaxJ is asserted or used.

Source application: Aschbacher–Smith, combined manuscript of 1 March 2004,
first construction of 13.6.13, printed p.929.
-/

@[expose] public section
open Subgroup Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson
variable {D : Type*} [Group D]
local notation "S3" => Equiv.Perm (Fin 3)

private theorem involution_words : ∀ t : S3, t ≠ 1 → t ^ 2 = 1 →
    ∃ g : S3, ∀ x : S3,
      let u := g * t * g⁻¹
      x = 1 ∨ x = t ∨ x = u ∨ x = t * u ∨ x = u * t ∨ x = t * u * t := by
  decide +kernel

private theorem normal_contains_involution (K : Subgroup S3) (hn : K.Normal)
    {t : S3} (ht : t ∈ K) (hne : t ≠ 1) (htwo : t ^ 2 = 1) : K = ⊤ := by
  obtain ⟨g, hg⟩ := involution_words t hne htwo
  have hu : g * t * g⁻¹ ∈ K := hn.conj_mem t ht g
  apply top_unique
  intro x _
  rcases hg x with h | h | h | h | h | h
  · exact h ▸ K.one_mem
  · exact h ▸ ht
  · exact h ▸ hu
  · exact h ▸ K.mul_mem ht hu
  · exact h ▸ K.mul_mem hu ht
  · exact h ▸ K.mul_mem (K.mul_mem ht hu) ht

private theorem symmetricThree_le (H J B : Subgroup D) [J.Normal]
    (e : H ≃* S3) (hBH : B ≤ H) (hBJ : B ≤ J)
    (hB : IsElementaryAbelian 2 B) (hne : B ≠ ⊥) : H ≤ J := by
  let K := (J.subgroupOf H).map e.toMonoidHom
  let : K.Normal := (inferInstance : (J.subgroupOf H).Normal).map _ e.surjective
  obtain ⟨b, hb, hbne⟩ : ∃ b ∈ B, b ≠ 1 := by
    by_contra! hh
    exact hne (B.eq_bot_iff_forall.mpr hh)
  let a : H := ⟨b, hBH hb⟩
  have han : e a ≠ 1 := by
    intro he
    have ha : a = 1 := e.injective (he.trans e.map_one.symm)
    exact hbne (congrArg Subtype.val ha)
  have ha2 : (e a) ^ 2 = 1 := by
    rw [← map_pow]
    have hb2 := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hB.exponent_dvd_p (⟨b,hb⟩ : B)
    have ha2 : a ^ 2 = 1 := Subtype.ext (congrArg (fun x : B => (x : D)) hb2)
    rw [ha2, map_one]
  have hK := normal_contains_involution K inferInstance
    (mem_map_of_mem e.toMonoidHom (show a ∈ J.subgroupOf H from hBJ hb)) han ha2
  intro h hh
  have hm : e ⟨h, hh⟩ ∈ K := hK ▸ mem_top _
  have hj : (⟨h, hh⟩ : H) ∈ J.subgroupOf H :=
    (mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp hm
  exact hj

private theorem maxJ_normal (N : Subgroup D) [N.Normal] : (elementaryAbelianMaxJ N).Normal := by
  let : (elementaryAbelianMaxJ (⊤ : Subgroup N)).Characteristic :=
    elementaryAbelianMaxJ_top_characteristic
  have he : (⊤ : Subgroup N).map N.subtype = N := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  rw [← he, elementaryAbelianMaxJ_map_injective _ N.subtype_injective]
  exact ConjAct.normal_of_characteristic_of_normal

private theorem thompson_contains_of_maximum {C : Type*} [Group C]
    (f : C →* D) (hf : Function.Surjective f)
    (P H : Subgroup D) [P.Normal] (e : H ≃* S3)
    (E : Subgroup C) (hE : E ∈ elementaryAbelianMaxSubgroups (P.comap f))
    (hEH : E.map f ≤ H) (hne : E.map f ≠ ⊥) :
    H ≤ (elementaryAbelianMaxJ (P.comap f)).map f := by
  let J := (elementaryAbelianMaxJ (P.comap f)).map f
  let : J.Normal := (maxJ_normal (P.comap f)).map f hf
  exact symmetricThree_le H J (E.map f) e hEH
    (map_mono (le_sSup hE)) (hE.2.1.map f) hne
private theorem thompson_contains_of_maximum_intersection {C : Type*} [Group C]
    (f : C →* D) (hf : Function.Surjective f)
    (P H : Subgroup D) [P.Normal] (e : H ≃* S3)
    (E : Subgroup C) (hE : E ∈ elementaryAbelianMaxSubgroups (P.comap f))
    (hne : E.map f ⊓ H ≠ ⊥) :
    H ≤ (elementaryAbelianMaxJ (P.comap f)).map f := by
  let J := (elementaryAbelianMaxJ (P.comap f)).map f
  let : J.Normal := (maxJ_normal (P.comap f)).map f hf
  let : IsElementaryAbelian 2 (E.map f) := hE.2.1.map f
  exact symmetricThree_le H J (E.map f ⊓ H) e inf_le_right
    (inf_le_left.trans (map_mono (le_sSup hE)))
    (IsElementaryAbelian.of_le inf_le_left) hne

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products.NormalThompson

namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
variable {G : Type*} [Group G]

/-- A moving maximum elementary subgroup in the full preimage puts the selected S₃ in its Thompson image. -/
theorem star_thompson_contains_of_maximum (z v : G)
    (P H : Subgroup (Gstar z v)) [P.Normal]
    (e : H ≃* Equiv.Perm (Fin 3))
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (P.comap (starMk z v)))
    (hEH : E.map (starMk z v) ≤ H) (hne : E.map (starMk z v) ≠ ⊥) :
    H ≤ starImage z v (elementaryAbelianMaxJ (starPreimage z v P)) := by
  rw [← starImage_intrinsic_thompson z v (P.comap (starMk z v)) (starPreimage z v P) rfl]
  exact NormalThompson.thompson_contains_of_maximum (starMk z v) (starMk_surjective z v)
    P H e E hE hEH hne

/-- It suffices that the maximum elementary image meet the coordinate nontrivially;
it need not be contained in that coordinate. -/
theorem star_thompson_contains_of_maximum_intersection (z v : G)
    (P H : Subgroup (Gstar z v)) [P.Normal]
    (e : H ≃* Equiv.Perm (Fin 3))
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (P.comap (starMk z v)))
    (hne : E.map (starMk z v) ⊓ H ≠ ⊥) :
    H ≤ starImage z v (elementaryAbelianMaxJ (starPreimage z v P)) := by
  rw [← starImage_intrinsic_thompson z v (P.comap (starMk z v)) (starPreimage z v P) rfl]
  exact NormalThompson.thompson_contains_of_maximum_intersection
    (starMk z v) (starMk_surjective z v) P H e E hE hne

/-- A single moving maximum elementary subgroup gives the literal preimage equality for a normal S₃. -/
theorem star_thompson_eq_of_maximum (z v : G)
    (H : Subgroup (Gstar z v)) [H.Normal]
    (e : H ≃* Equiv.Perm (Fin 3))
    (E : Subgroup (Gv v))
    (hE : E ∈ elementaryAbelianMaxSubgroups (H.comap (starMk z v)))
    (hne : E.map (starMk z v) ≠ ⊥) :
    starImage z v (elementaryAbelianMaxJ (starPreimage z v H)) = H := by
  have hEH : E.map (starMk z v) ≤ H := map_le_iff_le_comap.mpr hE.1
  apply le_antisymm _ (star_thompson_contains_of_maximum z v H H e E hE hEH hne)
  rw [← starImage_intrinsic_thompson z v (H.comap (starMk z v)) (starPreimage z v H) rfl]
  exact map_le_iff_le_comap.mpr (sSup_le fun _ h => h.1)

/-- Two coordinate witnesses supply both factors of the literal Thompson image.
The witnesses must be maximum in the full preimage of P. -/
theorem star_thompson_eq_of_two_maxima (z v : G)
    (P H₁ H₂ : Subgroup (Gstar z v)) [P.Normal]
    (e₁ : H₁ ≃* Equiv.Perm (Fin 3)) (e₂ : H₂ ≃* Equiv.Perm (Fin 3))
    (hgen : H₁ ⊔ H₂ = P)
    (E₁ E₂ : Subgroup (Gv v))
    (hE₁ : E₁ ∈ elementaryAbelianMaxSubgroups (P.comap (starMk z v)))
    (hE₂ : E₂ ∈ elementaryAbelianMaxSubgroups (P.comap (starMk z v)))
    (hEH₁ : E₁.map (starMk z v) ≤ H₁) (hne₁ : E₁.map (starMk z v) ≠ ⊥)
    (hEH₂ : E₂.map (starMk z v) ≤ H₂) (hne₂ : E₂.map (starMk z v) ≠ ⊥) :
    starImage z v (elementaryAbelianMaxJ (starPreimage z v P)) = P := by
  apply le_antisymm
  · rw [← starImage_intrinsic_thompson z v (P.comap (starMk z v)) (starPreimage z v P) rfl]
    exact map_le_iff_le_comap.mpr (sSup_le fun _ h => h.1)
  · apply hgen.ge.trans
    exact sup_le (star_thompson_contains_of_maximum z v P H₁ e₁ E₁ hE₁ hEH₁ hne₁)
      (star_thompson_contains_of_maximum z v P H₂ e₂ E₂ hE₂ hEH₂ hne₂)

/-- Nontrivial intersections with the two coordinates suffice for the full product. -/
theorem star_thompson_eq_of_two_intersections (z v : G)
    (P H₁ H₂ : Subgroup (Gstar z v)) [P.Normal]
    (e₁ : H₁ ≃* Equiv.Perm (Fin 3)) (e₂ : H₂ ≃* Equiv.Perm (Fin 3))
    (hgen : H₁ ⊔ H₂ = P)
    (E₁ E₂ : Subgroup (Gv v))
    (hE₁ : E₁ ∈ elementaryAbelianMaxSubgroups (P.comap (starMk z v)))
    (hE₂ : E₂ ∈ elementaryAbelianMaxSubgroups (P.comap (starMk z v)))
    (hne₁ : E₁.map (starMk z v) ⊓ H₁ ≠ ⊥)
    (hne₂ : E₂.map (starMk z v) ⊓ H₂ ≠ ⊥) :
    starImage z v (elementaryAbelianMaxJ (starPreimage z v P)) = P := by
  apply le_antisymm
  · rw [← starImage_intrinsic_thompson z v (P.comap (starMk z v)) (starPreimage z v P) rfl]
    exact map_le_iff_le_comap.mpr (sSup_le fun _ h => h.1)
  · apply hgen.ge.trans
    exact sup_le (star_thompson_contains_of_maximum_intersection z v P H₁ e₁ E₁ hE₁ hne₁)
      (star_thompson_contains_of_maximum_intersection z v P H₂ e₂ E₂ hE₂ hne₂)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Solvable.Construction.Products
end
