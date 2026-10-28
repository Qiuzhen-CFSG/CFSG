module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.ParabolicActions.RootTransfer
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup
public import Theory.SpecificGroups.SymplecticFour.RootTori
public import Theory.SpecificGroups.SymplecticFour.RootNormalizerResidual

/-!
# The parabolic component action in E.6.11

For the parabolic subcase of the symplectic alternative, construct a cyclic
complement X to C_L(V) in L ∩ M, regular on the nonidentity elements of
[V,X]. Identify this displacement with an actual matrix root subgroup, and
identify C_L(V) with the solvable residual computed inside L ∩ M.

The root realization from `RootTransfer` retains the given isomorphism through
the inclusion of Sp₄(2ⁿ)' into Sp₄(2ⁿ), which is an isomorphism for n > 1.
Transport the intrinsic matrix torus, its normalizer and its centralizer through
that same embedding. If W = [V,L ∩ M], the matrix identity [W,X] = W and the
containments W ≤ V and X ≤ L ∩ M give [V,X] = W. The intrinsic root-normalizer
residual formula then gives the asserted residual inside the parabolic.

Only the symplectic alternative and its explicit parabolic root-action subcase
are needed for this intrinsic conclusion. Construction of that alternative and
the ambient E.6.11 assembly remain with their respective source owners.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.11(3c),
printed p.250 (PDF p.261).
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterE.Section06.Components.ParabolicActions
variable {G : Type*} [Group G]

private theorem regular_conjugation_map {A : Type*} [Group A]
    (f : A →* G) (hf : Function.Injective f) (Y R : Subgroup A)
    (hYN : Y ≤ normalizer (R : Set A))
    (hreg : ∀ a ∈ R, a ≠ 1 → ∀ b ∈ R, b ≠ 1 →
      ∃! y : Y, (y : A) * a * (y : A)⁻¹ = b) :
    RegularConjugation (Y.map f) (R.map f) := by
  refine ⟨(map_mono hYN).trans (le_normalizer_map f), ?_⟩
  rintro a ⟨a₀, ha, rfl⟩ hane b ⟨b₀, hb, rfl⟩ hbne
  obtain ⟨y, hy, huniq⟩ := hreg a₀ ha
    (fun h => hane (by rw [h, map_one])) b₀ hb
    (fun h => hbne (by rw [h, map_one]))
  refine ⟨⟨f y, ⟨y, y.property, rfl⟩⟩, ?_, ?_⟩
  · simpa only [map_mul, map_inv] using congrArg f hy
  · intro x hx
    obtain ⟨x₀, hx₀, he⟩ := x.property
    have hxy : (⟨x₀, hx₀⟩ : Y) = y :=
      huniq _ (hf (by simpa only [map_mul, map_inv, he] using hx))
    apply Subtype.ext
    exact he.symm.trans (congrArg (fun z : Y => f z) hxy)

private theorem map_back {L : Subgroup G} {A : Type*} [Group A]
    (e : L ≃* A) {P : Subgroup G} (hP : P ≤ L) :
    ((P.subgroupOf L).map e.toMonoidHom).map
      (L.subtype.comp e.symm.toMonoidHom) = P := by
  rw [map_map]
  have he : (L.subtype.comp e.symm.toMonoidHom).comp e.toMonoidHom = L.subtype := by
    ext x
    simp
  rw [he, map_subgroupOf_eq_of_le hP]

open Theory.SpecificGroups.SymplecticFour

/-- The intrinsic parabolic conclusion of E.6.11(3c), conditional only on the
symplectic alternative and its explicit parabolic root-action subcase. -/
theorem parabolic_torus_conclusion [Finite G] {M V U L : Subgroup G} {n : ℕ}
    (hn : 1 < n) (hs : SymplecticAlternative M V U L n)
    (hP : MaximalParabolic L (L ⊓ M)) (hroot : SymplecticRootAction L V n) :
    ParabolicTorusConclusion M V L n := by
  have hWroot := displacement_is_root hn hs hroot
  obtain ⟨hWL, F, hfield, hfinite, hcard, e, r, hR⟩ := hWroot
  let := hfield
  let := hfinite
  let := EvenProjective.charTwo_of_card hcard
  change ((⁅V, L ⊓ M⁆ : Subgroup G).subgroupOf L).map e.toMonoidHom =
    RootSubgroup.group (F := F) r at hR
  let R := RootSubgroup.group (F := F) r
  change _ = R at hR
  let N := normalizer (R : Set (Sp F))
  let C := centralizer (R : Set (Sp F))
  have hN : N ≠ ⊤ := RootNormalizerResidual.normalizer_ne_top r
  have hPN := parabolic_map_eq_root_normalizer e R hroot.1 hP hR hN
  have hCV := displacement_centralizer_map hn hs hroot.1 e R hR
  change _ = N at hPN
  change _ = C at hCV
  let f : Sp F →* G := L.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := Subtype.val_injective.comp e.symm.injective
  have hRf : R.map f = ⁅V, L ⊓ M⁆ := by
    rw [← hR]
    exact map_back e hWL
  have hNf : N.map f = L ⊓ M := by
    rw [← hPN]
    exact map_back e inf_le_left
  have hCf : C.map f = L ⊓ centralizer (V : Set G) := by
    rw [← hCV]
    exact map_back e inf_le_left
  obtain ⟨Y, hYN, ⟨eY⟩, hsup, hinf, hcomm, hreg⟩ :=
    RootTori.exists_regular_cyclic_complement hcard hn r
  let X := Y.map f
  have hXP : X ≤ L ⊓ M := by
    rw [← hNf]
    exact map_mono hYN
  have hsupX : (L ⊓ centralizer (V : Set G)) ⊔ X = L ⊓ M := by
    rw [← hCf, ← hNf]
    exact (map_sup C Y f).symm.trans (congrArg (Subgroup.map f) hsup)
  have hinfX : (L ⊓ centralizer (V : Set G)) ⊓ X = ⊥ := by
    rw [← hCf]
    change C.map f ⊓ Y.map f = ⊥
    rw [← map_inf C Y f hf, hinf, Subgroup.map_bot]
  have hWX : ⁅⁅V, L ⊓ M⁆, X⁆ = ⁅V, L ⊓ M⁆ := by
    rw [← hRf]
    change ⁅R.map f, Y.map f⁆ = R.map f
    rw [← map_commutator, hcomm]
  have hWV : ⁅V, L ⊓ M⁆ ≤ V := le_sup_left.trans_eq (hs.decomposition hn).1
  have hdis : ⁅V, X⁆ = ⁅V, L ⊓ M⁆ :=
    le_antisymm (commutator_mono le_rfl hXP)
      (hWX.ge.trans (commutator_mono hWV (le_refl X)))
  refine ⟨X, ⟨hXP, ⟨(Y.equivMapOfInjective f hf).symm.trans eY⟩,
    hsupX, hinfX, hdis, ?_⟩, ?_, ?_⟩
  · rw [hdis, ← hRf]
    exact regular_conjugation_map f hf Y R hYN hreg
  · rw [hdis]
    exact ⟨hWL, F, hfield, hfinite, hcard, e, r, hR⟩
  · exact parabolic_residual_of_root_normalizer_residual hn hs hroot.1 hP e R hR hN
      (RootNormalizerResidual.solvableResidual_eq_centralizer hcard hn r)

end CFSG.Quasithin.ChapterE.Section06.Components.ParabolicActions
