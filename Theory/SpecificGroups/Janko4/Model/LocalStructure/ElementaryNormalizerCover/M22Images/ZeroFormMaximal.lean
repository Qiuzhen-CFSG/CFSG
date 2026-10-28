module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormReduction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.M22Images.EightEnlargement

/-!
# Completing the mixed zero-form reduction at maximal-two-local level

The exhaustive M22 lift calculation leaves E/F coverage, a pure-2A normalizer,
or the exceptional order-sixteen lift. Its newly proved strict normalizer
enlargement excludes the last case at a maximal TWO-local. This removes the
previous lower bound on the order of the mixed zero-form witness.

Combining this result with the intrinsic-form reduction leaves only the
pure-2A and nonsingular source families outside E/F. The final theorem applies
this narrowing to every native radical P, chooses an actual maximal two-local
above N(P), and retains the local full normalizer and embedded two-core maps.
Any remaining elementary witness is contained in P by radical saturation.
The pure-2A and nonsingular alternatives remain explicit mathematical work;
this is not the completed four-local cover.

Source: Kleidman--Wilson, *The Maximal Subgroups of J4* (1988), Section 2,
p.488, Proposition 2.2.3, p.491, and the maximal-two-local assembly.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormMaximal
open Cardinality LinearFive InvolutionCentralizers.Second LargeCenterRadicals.OuterHalf
open M23Geometry ZeroFormReduction EightEnlargement
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel

/-- Strictness excludes the final exceptional image at maximal TWO-local level.
Every mixed zero-form normalizer now reduces to native E/F or a pure-2A
normalizer, with no lower bound on the witness's order. -/
theorem maximal_mixed_zero_form (X H : Subgroup Model)
    [IsElementaryAbelian 2 X] (hzero : intrinsicElementaryForm X = 0)
    (hn : ¬ ∀ x ∈ X, x ≠ 1 → IsConj a x)
    (hH : IsMaximalTwoLocal H) (hHX : H = normalizer (X : Set Model)) :
    (∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
      H = max1.map (MulAut.conj g).toMonoidHom) ∨
    (∃ Y : Subgroup Model, Y ≠ ⊥ ∧ IsElementaryAbelian 2 Y ∧
      H = normalizer (Y : Set Model) ∧ ∀ y ∈ Y, y ≠ 1 → IsConj a y) := by
  rcases mixed_zero_form_reduction X hzero hn with ⟨g,hg | hg⟩ | ⟨Y,hY,hYe,hNY,hp⟩ |
      ⟨g,Y,hXY,hNY,hYe,hzY,hYcard,hYker,n,hlift,himage⟩
  · exact Or.inl ⟨g,Or.inl (hH.eq_of_le
      (nativeF_generated_isTwoLocal.map_equiv (MulAut.conj g)) (hHX ▸ hg))⟩
  · exact Or.inl ⟨g,Or.inr (hH.eq_of_le
      (embedded_localKernel_isTwoLocal.map_equiv (MulAut.conj g)) (hHX ▸ hg))⟩
  · let := hYe
    exact Or.inr ⟨Y,hY,hYe,hH.eq_of_le ⟨Y,hY,IsElementaryAbelian.isPGroup 2 Y,rfl⟩
      (hHX ▸ hNY),hp⟩
  · let := hYe
    have hs : (seed : Model) ∈ Y := by
      have hm : (seed : Model) ∈ Y ⊓ embeddedKernel := by
        rw [hYker]
        exact mem_zpowers _
      exact hm.1
    have hs1 : (seed : Model) ≠ 1 := by
      intro he
      have ho := seed_order
      rw [he,orderOf_one] at ho
      contradiction
    have hYR : Y ≤ residualInclusion.range := by
      have hr := zero_form_le_involution_residual Y hzY _ hs hs1
      change Y ≤ (ambientCentralizer.subtype.comp residual.subtype).range
      rw [MonoidHom.range_comp,range_subtype]
      exact hr
    let W := omegaCenterIn (centralizer (Y : Set Model))
    have hW : W ≠ ⊥ := by
      intro he
      have hm := elementary_le_centralizer_omegaCenter Y hs
      change (seed : Model) ∈ W at hm
      exact hs1 (mem_bot.mp (he ▸ hm))
    have hlt := residual_eight_normalizer_lt Y hYR n himage hzY hs
    have hltg := (map_lt_map_iff_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mpr hlt
    rw [map_equiv_normalizer_eq,map_equiv_normalizer_eq] at hltg
    have hlocal : IsTwoLocal (normalizer (W : Set Model)) :=
      ⟨W,hW,IsElementaryAbelian.isPGroup 2 W,rfl⟩
    have hlocalg := hlocal.map_equiv (MulAut.conj g)
    rw [map_equiv_normalizer_eq] at hlocalg
    have hstrict := lt_of_le_of_lt (hHX ▸ hNY) hltg
    exact (hstrict.ne (hH.eq_of_le hlocalg hstrict.le)).elim

/-- After the exhaustive zero-form calculation, only the pure-2A and
nonsingular source families remain outside the native E/F normalizers. -/
theorem maximal_twoLocal_remaining_cases (H : Subgroup Model) (hH : IsMaximalTwoLocal H) :
    (∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
      H = max1.map (MulAut.conj g).toMonoidHom) ∨
    ∃ X : Subgroup Model, X ≠ ⊥ ∧ ∃ _ : IsElementaryAbelian 2 X,
      H = normalizer (X : Set Model) ∧
      ((∀ x ∈ X, x ≠ 1 → IsConj a x) ∨ (intrinsicElementaryForm X).Nondegenerate) := by
  obtain ⟨X,hX,hXe,hHX,hform⟩ := maximal_twoLocal_zero_or_nonsingular H hH
  let := hXe
  by_cases hp : ∀ x ∈ X, x ≠ 1 → IsConj a x
  · exact Or.inr ⟨X,hX,hXe,hHX,Or.inl hp⟩
  rcases hform with hz | hns
  · rcases maximal_mixed_zero_form X H hz hp hH hHX with h | ⟨Y,hY,hYe,hHY,hpure⟩
    · exact Or.inl h
    · exact Or.inr ⟨Y,hY,hYe,hHY,Or.inl hpure⟩
  · exact Or.inr ⟨X,hX,hXe,hHX,Or.inr hns⟩

/-- Literal application to every native radical, with no center-order, Sylow,
or zero-form hypothesis. The remaining pure/nonsingular source alternatives
are explicit; the final four-local cover must still discharge them. -/
theorem radical_remaining_cases (P : Subgroup Model) (hP : P.IsPRadical 2) :
    ∃ H : Subgroup Model, IsMaximalTwoLocal H ∧
      ((∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
        H = max1.map (MulAut.conj g).toMonoidHom) ∨
        ∃ X : Subgroup Model, X ≠ ⊥ ∧ X ≤ P ∧ ∃ _ : IsElementaryAbelian 2 X,
          H = normalizer (X : Set Model) ∧
          ((∀ x ∈ X, x ≠ 1 → IsConj a x) ∨ (intrinsicElementaryForm X).Nondegenerate)) ∧
      normalizer (P : Set Model) ≤ H ∧ P ≤ H ∧
      (normalizer (P.subgroupOf H : Set H)).map H.subtype = normalizer (P : Set Model) ∧
      (P.subgroupOf H).IsPRadical 2 ∧
      (normalizer (P.subgroupOf H : Set H)).pCoreIn 2 = P.subgroupOf H ∧
      ((normalizer (P.subgroupOf H : Set H)).pCoreIn 2).map H.subtype = P := by
  have hlocal : IsTwoLocal (normalizer (P : Set Model)) := ⟨P,hP.1,hP.isPGroup,rfl⟩
  obtain ⟨H,hNH,hH⟩ := Finite.exists_le_maximal hlocal
  have rows : (∃ g : Model, H = M_F.map (MulAut.conj g).toMonoidHom ∨
      H = max1.map (MulAut.conj g).toMonoidHom) ∨
      ∃ X : Subgroup Model, X ≠ ⊥ ∧ X ≤ P ∧ ∃ _ : IsElementaryAbelian 2 X,
        H = normalizer (X : Set Model) ∧
        ((∀ x ∈ X, x ≠ 1 → IsConj a x) ∨ (intrinsicElementaryForm X).Nondegenerate) := by
    rcases maximal_twoLocal_remaining_cases H hH with h | ⟨X,hX,hXe,hHX,hcase⟩
    · exact Or.inl h
    · let := hXe
      have hXP : X ≤ P := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
        P X hP.isPGroup (IsElementaryAbelian.isPGroup 2 X) hP.2.le (hHX ▸ hNH)
      exact Or.inr ⟨X,hX,hXP,hXe,hHX,hcase⟩
  have hPH := P.le_normalizer.trans hNH
  have hN := hNH.trans H.le_normalizer
  have hcore := hP.normalizer_core_subgroupOf H hPH hN
  refine ⟨H,hH,rows,hNH,hPH,?_,hP.subgroupOf_of_normalizer_normalizes H hPH hN,hcore,?_⟩
  · rw [← subgroupOf_normalizer_eq hPH,map_subgroupOf_eq_of_le hNH]
  · rw [hcore,map_subgroupOf_eq_of_le hPH]


end Janko4.LocalStructure.ElementaryNormalizerCover.M22Images.ZeroFormMaximal
