module
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Torus

/-!
# No unipotent fixed points of the full symplectic Cartan subgroup

Write a Sylow element in its four native matrix coordinates. Commuting with
both independent diagonal parameters kills the two short-root coordinates;
commuting with a nontrivial unit and its inverse kills the long-root ones.
In characteristic two a unit equal to its inverse is one. Thus every field
of order greater than two works, including order four.

This is the full unipotent fixed-subgroup calculation needed by the Cartan
route discussed in Aschbacher–Smith F.4.10 and F.4.16, printed pp.279,282 of
`refs/quasithin.pdf`. It does not construct an apartment in a completion.
-/

@[expose] public noncomputable section
open Matrix Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-- The whole unipotent group has no nonidentity element fixed by the full
rank-two diagonal torus. In particular the field-four case is included. -/
theorem unipotent_torus_fixed_eq_bot (hF : 2 < Nat.card F) :
    unipotent (F := F) ⊓ centralizer ((diagonalTorusHom (F := F)).range : Set (Sp F)) = ⊥ := by
  have hc : 1 < Nat.card Fˣ := by rw [Nat.card_units]; omega
  have : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hc
  obtain ⟨c,hc⟩ := exists_ne (1 : Fˣ)
  have hc1 : (c : F) ≠ 1 := fun he => hc (Units.ext he)
  have hc2 : (c : F) ≠ (c⁻¹ : Fˣ) := by
    intro he
    have hs : (c : F)^2 = 1 := by
      calc
        (c : F)^2 = (c : F) * (c⁻¹ : Fˣ) := by rw [pow_two]; exact congrArg ((c : F) * ·) he
        _ = 1 := Units.mul_inv c
    exact hc1 (CharTwo.sq_injective (by simpa using hs))
  apply bot_unique
  rintro g ⟨hg,ht⟩
  obtain ⟨⟨b,u,w,v⟩,he⟩ := element_surjective (⟨g,hg⟩ : unipotent (F := F))
  have hmatrix : g.val = (element b u w v).val.val := (congrArg (fun x : unipotent (F := F) => x.val.val) he).symm
  have comm (a d : Fˣ) :
      (diagonalTorus a d).val * g.val = g.val * (diagonalTorus a d).val :=
    congrArg (fun x : Sp F => x.val) ((mem_centralizer_iff.mp ht) _ ⟨(a,d),rfl⟩)
  have hentry (a d : Fˣ) (i j : Fin 2 ⊕ Fin 2) := congrArg (fun M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F => M i j) (comm a d)
  have hb : b = 0 := by
    have hh : (c : F) * b = b := by
      simpa [hmatrix, element_matrix, diagonalTorus] using hentry c 1 (.inl 0) (.inl 1)
    exact (mul_eq_mul_right_iff.mp (hh.trans (one_mul b).symm)).resolve_left hc1
  have hu : u = 0 := by
    have hh : (c : F) * u = u * (c⁻¹ : Fˣ) := by
      simpa [hmatrix, element_matrix, diagonalTorus] using hentry c 1 (.inl 0) (.inr 0)
    rw [mul_comm u] at hh
    exact (mul_eq_mul_right_iff.mp hh).resolve_left hc2
  have hw : w = 0 := by
    have hh : (c : F) * w = w := by
      simpa [hmatrix, element_matrix, diagonalTorus] using hentry 1 c (.inl 1) (.inr 0)
    exact (mul_eq_mul_right_iff.mp (hh.trans (one_mul w).symm)).resolve_left hc1
  have hv : v = 0 := by
    have hh : (c : F) * v = v * (c⁻¹ : Fˣ) := by
      simpa [hmatrix, element_matrix, diagonalTorus] using hentry 1 c (.inl 1) (.inr 1)
    rw [mul_comm v] at hh
    exact (mul_eq_mul_right_iff.mp hh).resolve_left hc2
  have he1 : (⟨g,hg⟩ : unipotent (F := F)) = 1 := by
    rw [←he,hb,hu,hw,hv]
    exact element_zero
  exact congrArg Subtype.val he1
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
