module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal.Generation
public import CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.NaturalSetup.Complement

/-!
# The original orthogonal closure is the full two-core

For the actual Ω₄⁺(4) action on the original U/Z(U), residual generation has
already proved C_D(L)=1. The natural complement now yields D=V₁ᵍ. Substitute
this into the original extraspecial core product Qᵍ=UᵍD and undo the same
right conjugation to obtain O₂(H)=U. This supplies the literal two-core
identification required by the selected-involution argument of 14.4.9.

The natural orthogonal action, its original quotient and the source conjugator
are retained. No complement or two-core identification is assumed. Selection
of i=zˣ and the ensuing orthogonal exclusion remain later source deductions.

Source: Aschbacher--Smith, 14.4.7 and its use in 14.4.9,
printed pp.1009--1010; refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Module
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource CaseOneGeometry
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open LargerDimension CoreGeometry ClassicalOrthogonal ClassicalOrthogonal.FourPlusMatrix
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Source 14.4.7 for the original orthogonal row: the H-closure is the
whole two-core. The selected involution may therefore use the literal quotient. -/
theorem source_orthogonal_twoCore (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) [IsElementaryAbelian 2 F.Uhat]
    (hne : ¬ IsMulCommutative F.U) (hZ : F.ZU = F.Vi 1)
    (g : G) (hg : g ∈ L) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (κ : ((pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) ≃* OmegaPlus 2 Binary.F)
    (e : Additive F.Uhat ≃ₗ[ZMod 2] VectorD 2 Binary.F)
    (he : letI := chosen.elementary
      letI := F.U_normal
      ∀ (k : (pResidual 2 F.H).map (QuotientGroup.mk' (pCore 2 F.H))) v,
        e ((sourceAction F (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)).representation k v) =
          subgroupNatural (OmegaPlus 2 Binary.F) (κ k) (e v)) :
    (conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G) = conjugate (F.Vi 1) g) ∧
      F.H.pCoreIn 2 = F.U := by
  let := chosen.elementary
  let := F.U_normal
  have models : RankCore.ActionAlternative.{u} (sourceAction F
    (source_terminal_kernel F d earlier hq chosen structural alternatives hne hZ)) := .orthogonal κ e he
  have hd := NaturalSetup.source_natural_complement d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH models
  have hz := (source_orthogonal_centralizer_trivial d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH κ e he).2
  have hd' : conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G) = conjugate (F.Vi 1) g := by
    change conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G) =
      conjugate (F.Vi 1) g ⊔ ((conjugate F.H g ⊓ centralizer (conjugate F.U g : Set G)) ⊓ centralizer (L : Set G)) at hd
    simpa only [hz,sup_bot_eq] using hd
  refine ⟨hd',?_⟩
  have hcore := source_conjugate_core_product d earlier hq chosen structural alternatives F hne hZ g hg hgP hgH
  have hline : conjugate (F.Vi 1) g ≤ conjugate F.U g :=
    map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
      ((F.le_seed 1).trans (le_conjugateSpanBy V F.H))
  rw [hd',sup_eq_left.mpr hline] at hcore
  exact Subgroup.map_injective (MulAut.conj g⁻¹).injective hcore
end CFSG.Quasithin.Chapter14.Section04.CaseOneLarge.Orthogonal
