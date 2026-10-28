module
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.Stabilizers
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.QuotientCoordinates
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.EmbeddingReduction.Basic

/-!
# Actual embedding inputs for a contrary source Sylow subgroup

The original two source pairs produce every action, core and marked quotient
field of the placed contrary configuration. The given Sylow choice is the
one maximizing the two-order among H-overgroups; no embedding alternative
or final Sylow conclusion is assumed. The resulting local 1.3.4 input uses
the original X, its literal quotient action and its actual Sylow supplement.

Source: Aschbacher--Smith, 15.4.20, printed pp.1163--1164.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure EmbeddingReduction
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M₁ M₂ X Y : Subgroup G}

/-- Every source action field of the placed-X input is derived on the same
raw Geometry and pair from the preceding source input. -/
theorem source_placedX
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (i j : Bool) (H U : Subgroup G)
    (hH : H ∈ Chapter1.HOver G ((geometry pX pY).I i j : Set G))
    (P : Sylow 2 H) (hP : (P : Subgroup H).map H.subtype = U)
    (hlo : (geometry pX pY).T₀ < U) (hup : U < (T : Subgroup G))
    (hi₀ : (geometry pX pY).T₀.relIndex U = 2)
    (hiT : U.relIndex (T : Subgroup G) = 2)
    (hmax : ∀ A ∈ Chapter1.HOver G ((geometry pX pY).I i j : Set G),
      ∀ Q : Sylow 2 A, Nat.card ((Q : Subgroup A).map A.subtype) ≤ Nat.card U)
    (hN : ∃ Q : Sylow 2 (normalizer (H.pCoreIn 2 : Set G)),
      (Q : Subgroup (normalizer (H.pCoreIn 2 : Set G))).map
        (normalizer (H.pCoreIn 2 : Set G)).subtype = U)
    (hmove : ¬ U ≤ normalizer ((geometry pX pY).X i : Set G)) :
    Nonempty (PlacedX (geometry pX pY) i j H U) := by
  let d := geometry pX pY
  have ht : d.T = T := rfl
  have hx : d.wholeX = X := pX.quotient.factor_generate hX
  have hm₁ : d.M₁ = M₁ := by change normalizer (d.wholeX : Set G) = M₁; rw [hx, hM₁]
  have hmark : ∃ f : (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G) →*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)),
      Function.Surjective f ∧
      f.ker = pCore 2 (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G) : Subgroup G) ∧
      ((d.X false).subgroupOf (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G))).map f =
        (alternatingGroup (Fin 3)).prod ⊥ ∧
      ((d.X true).subgroupOf (d.wholeX ⊔ ChapterB.baumann (d.T : Subgroup G))).map f =
        (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup (Fin 3)) := by
    rw [hx, ht]
    exact MarkedProduct.source_marked_product hX pX
  obtain ⟨f, hf, hk, hf₀, hf₁⟩ := hmark
  obtain ⟨_, e, _⟩ := MarkedProduct.source_quotient_coordinates hX
  have he : Nonempty ((d.wholeX ⧸ pCore 2 d.wholeX) ≃* Multiplicative (ZMod 3 × ZMod 3)) :=
    hx.symm ▸ (show Nonempty ((X ⧸ pCore 2 X) ≃* Multiplicative (ZMod 3 × ZMod 3)) from ⟨e⟩)
  obtain ⟨e⟩ := he
  refine ⟨{
    overgroup := hH
    sylow := P
    sylow_image := hP
    lower := hlo
    upper := hup
    lower_index := hi₀
    upper_index := hiT
    maximal := hmax
    core_sylow := hN
    T_normalizes := hX.sylow_le.trans_eq hm₁.symm
    baumann_le := (baumann_le_geometry_T₀ pX pY).trans hlo.le
    permutes := ?_
    moves := hmove
    outside := ?_
    perfect := hx.symm ▸ YFamily.perfect hX.member
    core_nontrivial := hx.symm ▸ MarkedProduct.source_member_core_ne_bot hX
    quotient := e
    product := f
    product_surjective := hf
    product_kernel := hk
    first_image := hf₀
    second_image := hf₁
    first_perfect := pX.quotient.factor_perfect i
    other_perfect := pY.quotient.factor_perfect j
    first_quotient_card := pX.quotient.factor_quotient_card i
    other_quotient_card := pY.quotient.factor_quotient_card j }⟩
  · intro u hu
    let m : M₁ := ⟨u, hX.sylow_le (hup.le hu)⟩
    exact ⟨pX.quotient.action.permutation m, pX.quotient.action.conjugation m⟩
  · intro hy
    have hyM : pY.quotient.factor j ≤ M₁ := hy.trans_eq hm₁
    exact (factor_not_le_other (pY.factor_join_sylow hY j) huniqueY
      hX.maximal hX.sylow_le hne.symm) hyM

/-- Exchanging the two original source pairs preserves the common stabilizer. -/
theorem geometry_swap_T₀ (pX : Pair T M₁ X) (pY : Pair T M₂ Y) :
    (geometry pY pX).T₀ = (geometry pX pY).T₀ := by
  exact inf_right_comm _ _ _

/-- The same four amalgams survive exchange of the two source pairs. -/
theorem geometry_swap_I (pX : Pair T M₁ X) (pY : Pair T M₂ Y) (i j : Bool) :
    (geometry pY pX).I j i = (geometry pX pY).I i j := by
  change (pY.quotient.factor j ⊔ (geometry pY pX).T₀) ⊔
    (pX.quotient.factor i ⊔ (geometry pY pX).T₀) =
    (pX.quotient.factor i ⊔ (geometry pX pY).T₀) ⊔
      (pY.quotient.factor j ⊔ (geometry pX pY).T₀)
  rw [geometry_swap_T₀]
  exact sup_comm _ _

/-- A failed source Sylow conclusion constructs a genuine placed embedding
input in one of the two original orientations. The finite maximal-Sylow
choice supplies the corrected larger-Sylow property in the core normalizer;
the full marked quotient and every factor property are derived above. -/
theorem exists_source_placed_counterexample
    (hX : Input K T M₁ X 2) (hY : Input K T M₂ Y 2)
    (pX : Pair T M₁ X) (pY : Pair T M₂ Y)
    (hM₁ : normalizer (X : Set G) = M₁) (hM₂ : normalizer (Y : Set G) = M₂)
    (hS₁ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₁)
    (hS₂ : normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ M₂)
    (huniqueX : ∀ M : Subgroup G, IsMaximalTwoLocal M → X ⊔ (T : Subgroup G) ≤ M → M = M₁)
    (huniqueY : ∀ M : Subgroup G, IsMaximalTwoLocal M → Y ⊔ (T : Subgroup G) ≤ M → M = M₂)
    (hne : M₁ ≠ M₂)
    (hfail : ∃ i j, ∃ H ∈ Chapter1.HOver G ((geometry pX pY).I i j : Set G),
      ¬ ∃ P : Sylow 2 H, (P : Subgroup H).map H.subtype = (geometry pX pY).T₀) :
    ∃ i j, ∃ H U : Subgroup G,
      Nonempty (PlacedX (geometry pX pY) i j H U) ∨
        Nonempty (PlacedX (geometry pY pX) j i H U) := by
  obtain ⟨i,j,H,hH,U,hlo,hup,_,_,⟨P,hP⟩,hmax,_,hN,hiT,hi₀,hmove⟩ :=
    exists_source_maximal_sylow_counterexample hX hY pX pY hM₁ hM₂ hS₁ hS₂
      huniqueX huniqueY hne hfail
  refine ⟨i,j,H,U,?_⟩
  rcases hmove with hmove | hmove
  · exact Or.inl (source_placedX hX hY pX pY hM₁ huniqueY hne i j H U
      hH P hP hlo hup hi₀ hiT hmax hN hmove)
  · apply Or.inr
    refine source_placedX hY hX pY pX hM₂ huniqueX hne.symm j i H U
      ?_ P hP ?_ hup ?_ hiT ?_ hN hmove
    · simpa only [geometry_swap_I] using hH
    · simpa only [geometry_swap_T₀] using hlo
    · simpa only [geometry_swap_T₀] using hi₀
    · simpa only [geometry_swap_I] using hmax

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
