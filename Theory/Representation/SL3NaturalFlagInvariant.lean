module
public import Theory.Representation.SL3RepeatedNaturalFlagTypes
public import Mathlib.Algebra.Module.ZMod

/-!
# Natural-module automorphisms preserve the two SL₃ flag types

An additive automorphism of the natural module is binary linear in
characteristic two. Applying the existing repeated-natural flag theorem to
one copy shows that its compatible group automorphism preserves both
standard maximal parabolics whenever it preserves the unitriangular Sylow.
A single Sylow conjugation gives a common parabolic pair for all such actors;
the pair contains the full Sylow normalizer and generates SL₃.

This is the intrinsic linear-three input to Aschbacher--Smith 15.3.20,
printed pp.1127--1128. The argument uses the fixed-vector distinction of
the derived parabolics, without a graph-automorphism classification.
-/

public section
open Matrix Subgroup
open scoped MatrixGroups
namespace Representation.SL3NaturalFlagInvariant
open Matrix.PSL3.LinearThree
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- An additive natural-module intertwiner fixes both standard parabolics
whenever its induced group automorphism preserves the standard Sylow. -/
theorem flags_of_additive_intertwiner
    (a : MulAut SL(3, F))
    (hU : (unipotentSL F).map a.toMonoidHom = unipotentSL F)
    (f : MulAut SL(3, F))
    (b : (Fin 3 → F) ≃+ (Fin 3 → F))
    (hb : ∀ g v, b ((f g).val.mulVec v) = (f (a g)).val.mulVec (b v)) :
    (pointParabolicSL F).map a.toMonoidHom = pointParabolicSL F ∧
      (lineParabolicSL F).map a.toMonoidHom = lineParabolicSL F := by
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  let b₀ : (Fin 3 → F) ≃ₗ[ZMod 2] (Fin 3 → F) :=
    LinearEquiv.ofBijective (b.toAddMonoidHom.toZModLinearMap 2) b.bijective
  let B : (Fin 1 → Fin 3 → F) ≃ₗ[ZMod 2] (Fin 1 → Fin 3 → F) :=
    LinearEquiv.piCongrRight (fun _ : Fin 1 => b₀)
  apply SL3RepeatedNaturalFlagTypes.flags_of_intertwiner a hU f (by decide : 0 < 1) B
  intro g v
  funext i
  exact hb g (v i)

/-- For any Sylow two-subgroup, a single pair of maximal parabolics contains
its normalizer, generates SL₃, and is individually fixed by every
Sylow-preserving automorphism implemented additively on the natural module. -/
theorem exists_invariant_parabolic_pair (U : Sylow 2 SL(3, F)) :
    ∃ P Q : Subgroup SL(3, F), IsCoatom P ∧ IsCoatom Q ∧
      P ⊔ Q = ⊤ ∧ normalizer (U : Set SL(3, F)) ≤ P ⊓ Q ∧
      ∀ a : MulAut SL(3, F),
        (U : Subgroup SL(3, F)).map a.toMonoidHom = U →
        (∃ b : (Fin 3 → F) ≃+ (Fin 3 → F),
          ∀ g v, b (g.val.mulVec v) = (a g).val.mulVec (b v)) →
        P.map a.toMonoidHom = P ∧ Q.map a.toMonoidHom = Q := by
  let _ := Fintype.ofFinite F
  obtain ⟨n, _, hF⟩ := FiniteField.card F 2
  rw [← Nat.card_eq_fintype_card] at hF
  obtain ⟨c, hcU, hcB⟩ :=
    Matrix.PSL3.CartanActions.BorelQuotient.sylowSL_normalizer_conjugate F n.pos hF U
  let f : MulAut SL(3, F) := MulAut.conj c
  let P := (pointParabolicSL F).map f.toMonoidHom
  let Q := (lineParabolicSL F).map f.toMonoidHom
  refine ⟨P, Q,
    (OrderIso.isCoatom_iff f.mapSubgroup _).mpr (pointParabolicSL_isCoatom F),
    (OrderIso.isCoatom_iff f.mapSubgroup _).mpr (lineParabolicSL_isCoatom F), ?_, ?_, ?_⟩
  · change (pointParabolicSL F).map f.toMonoidHom ⊔
      (lineParabolicSL F).map f.toMonoidHom = ⊤
    rw [← Subgroup.map_sup, parabolicsSL_sup_eq_top, map_top_of_surjective _ f.surjective]
  · rw [← hcB]
    exact le_inf (map_mono inf_le_left) (map_mono inf_le_right)
  · intro a ha
    rintro ⟨b, hb⟩
    let α : MulAut SL(3, F) := f.trans (a.trans f.symm)
    have hm (R : Subgroup SL(3, F)) :
        (R.map α.toMonoidHom).map f.toMonoidHom =
          (R.map f.toMonoidHom).map a.toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext g
      simp [α]
    have hα : (unipotentSL F).map α.toMonoidHom = unipotentSL F := by
      apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
      rw [hm, hcU, ha]
    have hbf : ∀ g v, b ((f g).val.mulVec v) = (f (α g)).val.mulVec (b v) := by
      intro g v
      simpa [α] using hb (f g) v
    obtain ⟨hp, hq⟩ := flags_of_additive_intertwiner α hα f b hbf
    constructor
    · change ((pointParabolicSL F).map f.toMonoidHom).map a.toMonoidHom = _
      rw [← hm, hp]
    · change ((lineParabolicSL F).map f.toMonoidHom).map a.toMonoidHom = _
      rw [← hm, hq]

end Representation.SL3NaturalFlagInvariant
