module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight

/-!
# Constant displacements for regular degree-eight actions

The preimage of a deleted fixed space consists of vectors with constant
displacements. A regular action identifies the points with the acting group,
and these vectors become a constant plus an additive character. If this
preimage lies in the even core, its quotient by the constant line is exactly
the natural fixed space; rank-nullity lowers the dimension by one.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Proposition B.3.2(3),(6), printed pp.83–84.
-/

public section

open BinaryPermutation Representation.BinaryOffender

namespace CFSG.Quasithin.ChapterB.Offenders

/-- The full-vector preimage of the deleted fixed space. -/
@[expose] noncomputable def eightDisplacementSpace (B : Subgroup (Equiv.Perm (Fin 8))) :
    Submodule (ZMod 2) (Full (Fin 8)) :=
  (fixedSpace (deletedRepresentation (Fin 8)) B).comap (constants (Fin 8)).mkQ

theorem mem_eightDisplacementSpace_iff (B : Subgroup (Equiv.Perm (Fin 8)))
    (v : Full (Fin 8)) :
    v ∈ eightDisplacementSpace B ↔
      ∀ b ∈ B, ∃ c : ZMod 2, ∀ i, v (b.symm i) - v i = c :=
  mem_deleted_fixedSpace_iff B v

theorem constants_le_eightDisplacementSpace (B : Subgroup (Equiv.Perm (Fin 8))) :
    constants (Fin 8) ≤ eightDisplacementSpace B := by
  intro v hv
  change (Submodule.Quotient.mk v : Deleted (Fin 8)) ∈ fixedSpace (deletedRepresentation (Fin 8)) B
  rw [(Submodule.Quotient.mk_eq_zero (constants (Fin 8))).mpr hv]
  exact Submodule.zero_mem _

theorem regularEight_eval_bijective {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (x : Fin 8) : Function.Bijective (fun a : A => a.val x) := by
  constructor
  · intro a b hab
    obtain ⟨c, _, hc⟩ := hA.2.2.2 x (a.val x)
    exact (hc a rfl).trans (hc b hab.symm).symm
  · intro y
    obtain ⟨a, ha, _⟩ := hA.2.2.2 x y
    exact ⟨a, ha⟩

theorem regularEight_subgroup_free {A B : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (hBA : B ≤ A) (b : B) (x : Fin 8)
    (h : b.val x = x) : b = 1 := by
  apply Subtype.ext
  have heq : (⟨b.val, hBA b.property⟩ : A) = 1 :=
    (regularEight_eval_bijective hA x).1 (by simpa using h)
  exact congrArg (fun a : A => a.val) heq

theorem mem_eightDisplacementSpace_iff_forward (B : Subgroup (Equiv.Perm (Fin 8)))
    (v : Full (Fin 8)) :
    v ∈ eightDisplacementSpace B ↔
      ∀ b : B, ∃ c : ZMod 2, ∀ i, v (b.val i) - v i = c := by
  rw [mem_eightDisplacementSpace_iff]
  constructor
  · intro h b
    have hb := h b.val⁻¹ (B.inv_mem b.property)
    change ∃ c, ∀ i, v (b.val.symm.symm i) - v i = c at hb
    simpa only [Equiv.symm_symm] using hb
  · intro h b hb
    simpa using h ⟨b⁻¹, B.inv_mem hb⟩

theorem regularEight_displacement_iff_affine {A : Subgroup (Equiv.Perm (Fin 8))}
    (hA : IsRegularEight A) (x : Fin 8) (v : Full (Fin 8)) :
    v ∈ eightDisplacementSpace A ↔
      ∃ χ : Additive A →+ ZMod 2, ∀ a : A, v (a.val x) = v x + χ (Additive.ofMul a) := by
  rw [mem_eightDisplacementSpace_iff_forward]
  constructor
  · intro hv
    have hd (a : A) (i : Fin 8) :
        v (a.val i) - v i = v (a.val x) - v x := by
      obtain ⟨c, hc⟩ := hv a
      exact (hc i).trans (hc x).symm
    let χ : Additive A →+ ZMod 2 :=
      { toFun := fun a => v (a.toMul.val x) - v x
        map_zero' := by simp
        map_add' := by
          intro a b
          change v (a.toMul.val (b.toMul.val x)) - v x =
            (v (a.toMul.val x) - v x) + (v (b.toMul.val x) - v x)
          have := hd a.toMul (b.toMul.val x)
          linear_combination this }
    exact ⟨χ, fun a => by dsimp [χ]; ring⟩
  · rintro ⟨χ, hχ⟩ a
    refine ⟨χ (Additive.ofMul a), ?_⟩
    intro i
    obtain ⟨b, rfl⟩ := (regularEight_eval_bijective hA x).2 i
    have hm : v (a.val (b.val x)) = v x + χ (Additive.ofMul (a * b)) := hχ (a * b)
    rw [hm, hχ b]
    change v x + χ (Additive.ofMul a + Additive.ofMul b) -
      (v x + χ (Additive.ofMul b)) = _
    rw [map_add]
    ring

/-- Quotienting the constant line lowers the preimage dimension by one,
provided all its vectors have even weight. -/
theorem eightDisplacementSpace_finrank_eq_natural_add_one
    (B : Subgroup (Equiv.Perm (Fin 8)))
    (heven : eightDisplacementSpace B ≤ core (Fin 8)) :
    Module.finrank (ZMod 2) (eightDisplacementSpace B) =
      Module.finrank (ZMod 2) (fixedSpace (naturalRepresentation (Fin 8)) B) + 1 := by
  let W := eightDisplacementSpace B
  let N := fixedSpace (naturalRepresentation (Fin 8)) B
  let f : W →ₗ[ZMod 2] N :=
    { toFun := fun v => ⟨⟨(constants (Fin 8)).mkQ v.val, ⟨v.val, heven v.property, rfl⟩⟩,
        (mem_natural_fixedSpace_iff B ⟨v.val, heven v.property⟩).mpr
          ((mem_eightDisplacementSpace_iff B v.val).mp v.property)⟩
      map_add' := by intro v w; apply Subtype.ext; apply Subtype.ext; exact map_add _ _ _
      map_smul' := by intro c v; apply Subtype.ext; apply Subtype.ext; exact map_smul _ _ _ }
  have hf : Function.Surjective f := by
    rintro ⟨⟨q, v, hv, rfl⟩, hq⟩
    have hvW : v ∈ W := (mem_eightDisplacementSpace_iff B v).mpr
      ((mem_natural_fixedSpace_iff B ⟨v, hv⟩).mp hq)
    exact ⟨⟨v, hvW⟩, rfl⟩
  have hk : LinearMap.ker f = (constants (Fin 8)).comap W.subtype := by
    ext v
    change f v = 0 ↔ v.val ∈ constants (Fin 8)
    rw [Subtype.ext_iff, Subtype.ext_iff]
    exact Submodule.Quotient.mk_eq_zero (constants (Fin 8))
  have hkdim : Module.finrank (ZMod 2) (LinearMap.ker f) = 1 := by
    rw [hk, (Submodule.comapSubtypeEquivOfLe
      (constants_le_eightDisplacementSpace B)).finrank_eq, finrank_constants]
  have hd := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hf, finrank_top, hkdim] at hd
  exact hd.symm



end CFSG.Quasithin.ChapterB.Offenders
