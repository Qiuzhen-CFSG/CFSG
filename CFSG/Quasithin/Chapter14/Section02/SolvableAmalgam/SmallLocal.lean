module

public import Theory.GroupTheory.AbelianImageCoreEquality
public import Theory.GroupAction.ElementaryEightPointEnlargement
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Common reductions for the small solvable amalgams

The centralizer chain (*) recovers `Q = QH` when `QH/Z` is abelian.
For the elementary eight-group in the second parabolic, an actual S₄ point
stabilizer and an element moving the distinguished point give the full
automorphism image, isomorphic to PSL₃(2).

These reductions retain quotient maps and conjugation actions. They do not
yet compute the concrete G₂ and Mathieu parabolics, their core automorphisms,
or the Aut(M₁₂) invariant-core alternatives. Those model calculations are
needed before applying these results to the recognized amalgams.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
Lemma 14.2.21, printed p.988 (PDF page 1005).
-/

namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal

/-- The abelian quotient branches of the centralizer chain (*). The ambient
group here is `Mc`, and the quotient map is literally the map modulo `Z`. -/
public theorem core_eq_of_abelian_quotient
    {D : Type*} [Group D] (Z Q QH : Subgroup D) [Z.Normal]
    (hZQ : Z ≤ Q) (hQQH : Q ≤ QH)
    [IsMulCommutative (QH.map (QuotientGroup.mk' Z))]
    (hcentralizer : Subgroup.centralizer (Q.map (QuotientGroup.mk' Z) : Set (D ⧸ Z)) ≤
      Q.map (QuotientGroup.mk' Z)) : Q = QH := by
  apply Subgroup.eq_of_abelian_map_of_centralizer_le (QuotientGroup.mk' Z)
    Q QH _ hQQH hcentralizer
  simpa only [QuotientGroup.ker_mk'] using hZQ

/-- The actual conjugation image becomes all of Aut(E) when it contains the
S₄ stabilizer and an element moving the distinguished point. -/
public theorem normalizer_image_eq_top_of_moves
    {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) (z : E)
    (hS : Nonempty (MulAction.stabilizer (MulAut E) z ≃* Equiv.Perm (Fin 4)))
    (hSimage : MulAction.stabilizer (MulAut E) z ≤ E.normalizerMonoidHom.range)
    (hmoves : ∃ g : Subgroup.normalizer (E : Set G),
      E.normalizerMonoidHom g z ≠ z) :
    E.normalizerMonoidHom.range = ⊤ := by
  apply MulAut.eq_top_of_elementaryEight_stabilizer_of_moves hE _ z hS hSimage
  obtain ⟨g, hg⟩ := hmoves
  exact ⟨E.normalizerMonoidHom g, ⟨g, rfl⟩, hg⟩

/-- The enlarged normalizer action realizes PSL₃(2) with its actual
centralizer kernel. No self-centralization of `E` is assumed. -/
public theorem normalizer_PSL3_of_moves
    {G : Type*} [Group G] [Finite G] (E : Subgroup G)
    [IsElementaryAbelian 2 E] (hE : Nat.card E = 8) (z : E)
    (hS : Nonempty (MulAction.stabilizer (MulAut E) z ≃* Equiv.Perm (Fin 4)))
    (hSimage : MulAction.stabilizer (MulAut E) z ≤ E.normalizerMonoidHom.range)
    (hmoves : ∃ g : Subgroup.normalizer (E : Set G),
      E.normalizerMonoidHom g z ≠ z) :
    ∃ e : MulAut E ≃* Matrix.PSL3Two.PSL,
      Function.Surjective (e.toMonoidHom.comp E.normalizerMonoidHom) ∧
        (e.toMonoidHom.comp E.normalizerMonoidHom).ker =
          (Subgroup.centralizer (E : Set G)).subgroupOf
            (Subgroup.normalizer (E : Set G)) := by
  obtain ⟨e⟩ := MulAut.elementaryEight_equiv_PSL3 hE
  have hsurj : Function.Surjective E.normalizerMonoidHom :=
    MonoidHom.range_eq_top.mp (normalizer_image_eq_top_of_moves E hE z hS hSimage hmoves)
  refine ⟨e, e.surjective.comp hsurj, ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ e.injective, Subgroup.normalizerMonoidHom_ker]

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallLocal
