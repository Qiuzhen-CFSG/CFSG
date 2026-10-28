module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.BlockRigidity.SourceContracts
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.CenterProduct

/-!
# Applying Krull–Schmidt to the actual center quotient

The finite-family A.1.15 parameter is specialized to the two factors using
the supplied multiplication isomorphism. If the quotient's center is trivial,
its conclusion permutes these factors themselves. The normalizer action on
X induces the quotient action, and pulling back identifies its factors with
WZ(X) and VZ(X) in the original ambient group.

This is a conditional algebraic application: commutation and direct
indecomposability must still be established by the binary-block assembly.
No permutation or trace equality is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, A.1.15,
printed p.23, and proof of 1.3.8, printed p.514.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity
universe u
variable {D : Type u} [Group D] [Finite D]

/-- The binary case of the full source parameter, with both actual factors. -/
theorem sourceA115_pair (h115 : SourceA115.{u})
    (A B : Subgroup D) (hA : DirectlyIndecomposable A) (hB : DirectlyIndecomposable B)
    (hprod : ∃ e : A × B ≃* D, ∀ a b, e (a,b) = (a : D) * (b : D))
    (hz : center D = ⊥) (α : MulAut D) :
    (A.map α.toMonoidHom = A ∨ A.map α.toMonoidHom = B) ∧
    (B.map α.toMonoidHom = A ∨ B.map α.toMonoidHom = B) := by
  let F : Fin 2 → Subgroup D := ![A, B]
  have hi : ∀ i, DirectlyIndecomposable (F i) := by
    intro i
    fin_cases i
    · exact hA
    · exact hB
  obtain ⟨e, he⟩ := hprod
  let ef : (∀ i, F i) ≃* A × B :=
    { piFinTwoEquiv (fun i => F i) with map_mul' := fun _ _ => rfl }
  have hf : ∃ e : (∀ i, F i) ≃* D, ∀ i (x : F i), e (Pi.mulSingle i x) = (x : D) := by
    refine ⟨ef.trans e, ?_⟩
    intro i x
    fin_cases i
    · change e ((Pi.mulSingle 0 x : ∀ i, F i) 0, (Pi.mulSingle 0 x : ∀ i, F i) 1) = (x : D)
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (1 : Fin 2) ≠ 0)]
      exact (he x 1).trans (mul_one _)
    · change e ((Pi.mulSingle 1 x : ∀ i, F i) 0, (Pi.mulSingle 1 x : ∀ i, F i) 1) = (x : D)
      simp only [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 2) ≠ 1)]
      exact (he 1 x).trans (one_mul _)
  have hp (i : Fin 2) : (F i).map α.toMonoidHom = A ∨ (F i).map α.toMonoidHom = B := by
    obtain ⟨j, hj⟩ := h115 D 2 F hi hf α i
    rw [hz, sup_bot_eq, sup_bot_eq] at hj
    fin_cases j
    · exact Or.inl hj
    · exact Or.inr hj
  exact ⟨hp 0, hp 1⟩


variable {G : Type u} [Group G]

private theorem preimage_map_quotientAut (X : Subgroup G)
    (F : Subgroup (X ⧸ center X)) (α : MulAut X) :
    (F.map (quotientAut (center X) α).toMonoidHom).comap
        (QuotientGroup.mk' (center X)) =
      (F.comap (QuotientGroup.mk' (center X))).map α.toMonoidHom := by
  ext x
  rw [mem_comap, mem_map_equiv, mem_map_equiv, mem_comap]
  have he : (quotientAut (center X) α).symm (QuotientGroup.mk' (center X) x) =
      QuotientGroup.mk' (center X) (α.symm x) := by
    apply (quotientAut (center X) α).injective
    rw [MulEquiv.apply_symm_apply, quotientAut_apply_mk, MulEquiv.apply_symm_apply]
  rw [he]

/-- The quotient action pulls back to literal ambient conjugation. -/
theorem preimage_map_quotient_conj (X : Subgroup G)
    (F : Subgroup (X ⧸ center X)) (d : normalizer (X : Set G)) :
    (((F.map (quotientAut (center X) (X.normalizerMonoidHom d)).toMonoidHom).comap
      (QuotientGroup.mk' (center X))).map X.subtype) =
      ((F.comap (QuotientGroup.mk' (center X))).map X.subtype).conjBy (d : G) := by
  rw [preimage_map_quotientAut, map_map]
  change _ = (((F.comap (QuotientGroup.mk' (center X))).map X.subtype).map
    (MulAut.conj (d : G)).toMonoidHom)
  rw [map_map]
  rfl


private theorem lift_centerFactor_eq {X W V : Subgroup G}
    (hWX : W ≤ X) (hVX : V ≤ X) (d : normalizer (X : Set G))
    (he : (centerFactor X W).map
      (quotientAut (center X) (X.normalizerMonoidHom d)).toMonoidHom = centerFactor X V) :
    (W ⊔ (center X).map X.subtype).conjBy (d : G) = V ⊔ (center X).map X.subtype := by
  have hh := congrArg (fun F : Subgroup (X ⧸ center X) =>
    (F.comap (QuotientGroup.mk' (center X))).map X.subtype) he
  rw [preimage_map_quotient_conj, centerFactor_preimage hWX, centerFactor_preimage hVX] at hh
  exact hh

/-- Applying A.1.15 to the actual multiplication isomorphism and pulling
back both quotient factors. Indecomposability is still an explicit premise. -/
theorem centerFactor_pair_of_source [Finite G] (h115 : SourceA115.{u})
    {X W V : Subgroup G} (hgen : W ⊔ V = X) (hcomm : ⁅W, V⁆ = ⊥)
    (hW : DirectlyIndecomposable (centerFactor X W))
    (hV : DirectlyIndecomposable (centerFactor X V))
    (hz : center (X ⧸ center X) = ⊥) :
    ∀ d ∈ normalizer (X : Set G),
      ((W ⊔ (center X).map X.subtype).conjBy d = W ⊔ (center X).map X.subtype ∨
        (W ⊔ (center X).map X.subtype).conjBy d = V ⊔ (center X).map X.subtype) ∧
      ((V ⊔ (center X).map X.subtype).conjBy d = W ⊔ (center X).map X.subtype ∨
        (V ⊔ (center X).map X.subtype).conjBy d = V ⊔ (center X).map X.subtype) := by
  have hWX : W ≤ X := le_sup_left.trans_eq hgen
  have hVX : V ≤ X := le_sup_right.trans_eq hgen
  intro d hd
  have hp := sourceA115_pair h115 (centerFactor X W) (centerFactor X V) hW hV
    (centerFactor_product hgen hcomm) hz
    (quotientAut (center X) (X.normalizerMonoidHom ⟨d, hd⟩))
  constructor
  · exact hp.1.imp (lift_centerFactor_eq hWX hWX ⟨d, hd⟩)
      (lift_centerFactor_eq hWX hVX ⟨d, hd⟩)
  · exact hp.2.imp (lift_centerFactor_eq hVX hWX ⟨d, hd⟩)
      (lift_centerFactor_eq hVX hVX ⟨d, hd⟩)

end CFSG.Quasithin.Chapter1.RadicalExclusions.BlockRigidity
