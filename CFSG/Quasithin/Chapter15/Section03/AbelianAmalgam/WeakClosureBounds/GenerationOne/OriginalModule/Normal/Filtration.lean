module
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.FixedFiltration
public import Theory.Representation.BinaryOffender.QuadraticSection
public import Theory.Representation.BinaryOffender.QuadraticQuotient
public import Theory.Representation.SubrepresentationLattice

/-!
# Fixed-space equality through quadratic composition factors

For a fixed actor and an odd-index subgroup of a component, the equality of
Borel-fixed and component-fixed spaces extends through every invariant
submodule and quotient. Strong induction on binary dimension uses the literal
quotient projection; quadraticity and the same fixed-codimension bound descend.

The irreducible calculation is discharged by the normal-model producer in
`QuadraticModules`. This is the extension step in Aschbacher–Smith 15.3.65,
printed p.1152, using the odd-index trace.
-/

@[expose] public section
open Representation Representation.BinaryOffender Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction
universe u
variable {D : Type u} [Group D] [Finite D]

/-- The odd-index trace extends a verified irreducible calculation through
all invariant submodules and quotients for the same quadratic actor. -/
theorem fixedSpace_le_by_quadratic_irreducibles
    (K A : Subgroup D) (B : Subgroup K) (hindex : Odd B.index)
    (hirr : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (σ : Representation (ZMod 2) D W), IsIrreducible σ → IsQuadratic σ A →
      fixedCodim σ A ≤ 2 * rank A →
      fixedSpace (σ.comp K.subtype) B ≤ fixedSpace (σ.comp K.subtype) ⊤)
    {V : Type u} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) D V) (hq : IsQuadratic ρ A)
    (hc : fixedCodim ρ A ≤ 2 * rank A) :
    fixedSpace (ρ.comp K.subtype) B ≤ fixedSpace (ρ.comp K.subtype) ⊤ := by
  classical
  have main : ∀ n, ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (σ : Representation (ZMod 2) D W), Module.finrank (ZMod 2) W = n →
      IsQuadratic σ A → fixedCodim σ A ≤ 2 * rank A →
      fixedSpace (σ.comp K.subtype) B ≤ fixedSpace (σ.comp K.subtype) ⊤ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro W _ _ _ σ hn hq hc
      let : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
      by_cases ht : Subsingleton W
      · let := ht
        intro w hw k
        exact Subsingleton.elim _ _
      · let : Nontrivial W := not_subsingleton_iff_nontrivial.mp ht
        by_cases hi : IsIrreducible σ
        · exact hirr W σ hi hq hc
        · obtain ⟨C,hCb,hCt⟩ : ∃ C : Subrepresentation σ, C ≠ ⊥ ∧ C ≠ ⊤ := by
            by_contra h
            push Not at h
            apply hi
            rw [Representation.IsIrreducible,isSimpleOrder_iff]
            exact ⟨inferInstance, fun C => (eq_or_ne C ⊥).imp_right (h C)⟩
          let : Finite (W ⧸ C.toSubmodule) := Finite.of_surjective
            C.toSubmodule.mkQ C.toSubmodule.mkQ_surjective
          have hCb' : C.toSubmodule ≠ ⊥ := fun h => hCb (Subrepresentation.toSubmodule_injective h)
          have hCt' : C.toSubmodule ≠ ⊤ := fun h => hCt (Subrepresentation.toSubmodule_injective h)
          have hCdim : Module.finrank (ZMod 2) C.toSubmodule < n := by
            rw [← hn, ← finrank_top (R := ZMod 2) (M := W)]
            exact Submodule.finrank_lt_finrank_of_lt (lt_top_iff_ne_top.mpr hCt')
          have hQdim : Module.finrank (ZMod 2) (W ⧸ C.toSubmodule) < n := by
            have hpos : 0 < Module.finrank (ZMod 2) C.toSubmodule :=
              Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr hCb')
            have hd := C.toSubmodule.finrank_quotient_add_finrank
            omega
          have hC := ih _ hCdim C.toSubmodule C.toRepresentation rfl
            (quadratic_subrepresentation σ C hq)
            ((fixedCodim_subrepresentation_le σ C A).trans hc)
          have hQ := ih _ hQdim (W ⧸ C.toSubmodule) C.quotientRepresentation rfl
            (quadratic_of_equivariant_surjection σ C.quotientRepresentation
              C.toSubmodule.mkQ C.toSubmodule.mkQ_surjective (fun _ _ => rfl) A hq)
            ((fixedCodim_le_of_equivariant_surjection σ C.quotientRepresentation
              C.toSubmodule.mkQ C.toSubmodule.mkQ_surjective (fun _ _ => rfl) A).trans hc)
          let C' : Subrepresentation (σ.comp K.subtype) :=
            ⟨C.toSubmodule,fun k w hw => C.apply_mem_toSubmodule k hw⟩
          apply fixedSpace_le_of_extension (σ.comp K.subtype) C' B hindex ?_ hQ
          intro w hw k
          have hf : (⟨w,hw.1⟩ : C.toSubmodule) ∈
              fixedSpace (C.toRepresentation.comp K.subtype) B := by
            intro b
            exact Subtype.ext (hw.2 b)
          exact congrArg Subtype.val (hC hf k)
  exact main _ V ρ rfl hq hc
end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.OriginalModule.Normal
