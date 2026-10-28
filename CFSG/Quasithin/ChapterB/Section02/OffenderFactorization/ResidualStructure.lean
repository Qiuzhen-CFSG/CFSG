module

public import CFSG.Quasithin.ChapterB.Section02.OffenderFactorization
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual
public import Theory.GroupTheory.GeneralizedFitting.InternalModuleResidual.Structure

/-!
# The residual step for relative internal offenders

The actual relative maximum-offender family contains a nontrivial elementary
abelian two-subgroup of its generated normal subgroup. The finite-group
structure theorem identifies the ambient generalized Fitting subgroup with
the image of `L` and shows that the centralizer's normal Sylow two-subgroup
has ambient image `O₂(G)`. Restricting to `O₂(G) ≤ R ≤ T` gives
`O₂(G) = C_R(V)`. When `J(R)` has nontrivial image, the normal-subgroup
theorem identifies the generated subgroup's generalized Fitting subgroup
with that same image of `L`.

The concluding adapters discharge the structural premises from the literal
factorization `G = LT` and the C-component or cyclic-three source alternatives.
The earlier conditional interfaces are retained. Source: Aschbacher–Smith,
B.2.10(2), printed p.77, under B.2.1, p.74 (combined 1 March 2004 manuscript).
The final Baumann-versus-generalized-Fitting alternative is assembled separately.
-/

public section

open Subgroup Stellmacher Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

/-- A member of the literal relative family is a nontrivial elementary
abelian two-subgroup of the literal generated subgroup. -/
theorem relativeMaxOffenderImages_exists_elementary_generator
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V] (hVR : V ≤ R)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker) :
    ∃ A ∈ relativeMaxOffenderImages R V q, IsElementaryTwo A ∧
      A ≤ generatedBy (relativeMaxOffenderImages R V q) ⊤ := by
  have hs := (lemma_B_2_10_relative V R hVR q hq hker hJ).2.1
  obtain ⟨A, hA⟩ := hs.1
  exact ⟨A, hA, (hs.2.1 A hA).1,
    le_iSup_of_le A (le_iSup_of_le ⟨hA, le_top⟩ le_rfl)⟩

/-- The final generalized-Fitting step of B.2.10(2), conditional on the
separate structural identification of the actual image of `L`. -/
theorem relativeMaxOffenderImages_fitting_eq_of_structure
    (V R L : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (hQR : pCore 2 G ≤ R)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker)
    (hLF : L.map q = generalizedFitting H)
    (hshape : IsQuasisimple (L.map q) ∨ Nat.card (L.map q) = 3) :
    let N := generatedBy (relativeMaxOffenderImages R V q) ⊤
    (generalizedFitting N).map N.subtype = L.map q := by
  have hVR : V ≤ R := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  let N := generatedBy (relativeMaxOffenderImages R V q) ⊤
  let : N.Normal :=
    (relativeMaxOffenderImages_generated_facts V R hVR q hq hker hJ).1
  obtain ⟨A, _, hAe, hAN⟩ :=
    relativeMaxOffenderImages_exists_elementary_generator V R hVR q hq hker hJ
  let : IsElementaryAbelian 2 A := hAe.2
  have hf := generalizedFitting_normal_eq_of_quasisimple_or_three hcore
    (hLF ▸ hshape) N A (IsElementaryAbelian.isPGroup 2 A) hAe.1 hAN
  exact hf.trans hLF.symm

omit [Finite H] in
/-- A normal Sylow subgroup of the centralizer supplies the source's
relative equality `O₂(G) = C_R(V)`, with the Sylow image also retained. -/
theorem internalModule_relative_centralizer_of_normalSylow
    (V R : Subgroup G) [V.Normal]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G)
    (hQR : pCore 2 G ≤ R) (hRT : R ≤ (T : Subgroup G))
    (hsyl : ∃ P : Sylow 2 (centralizer (V : Set G)),
      (P : Subgroup (centralizer (V : Set G))).Normal) :
    pCore 2 G = R ⊓ centralizer (V : Set G) ∧
      ∃ P : Sylow 2 (centralizer (V : Set G)),
        (P : Subgroup (centralizer (V : Set G))).Normal ∧
        (P : Subgroup (centralizer (V : Set G))).map
          (centralizer (V : Set G)).subtype = pCore 2 G := by
  obtain ⟨hT, hP⟩ := normalSylow_structure_of_coreFree_image q hq hcore
    (centralizer (V : Set G)) hker T hsyl
  refine ⟨le_antisymm (le_inf hQR (hT.le.trans inf_le_right)) ?_, hP⟩
  exact (inf_le_inf_right _ hRT).trans hT.ge

/-- The source alternatives prove `O₂(G) = C_R(V)`, the normal Sylow
statement for `C_G(V)`, and `L* = F*(G*)`, without a structural premise. -/
theorem internalModule_relative_structure
    (V R L : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G)
    (hQR : pCore 2 G ≤ R) (hRT : R ≤ (T : Subgroup G))
    (hL : (L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3)))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g) :
    pCore 2 G = R ⊓ centralizer (V : Set G) ∧
    (∃ P : Sylow 2 (centralizer (V : Set G)),
      (P : Subgroup (centralizer (V : Set G))).Normal ∧
      (P : Subgroup (centralizer (V : Set G))).map
        (centralizer (V : Set G)).subtype = pCore 2 G) ∧
    L.map q = generalizedFitting H := by
  obtain ⟨hT, hP, hF, _⟩ :=
    internalModule_residual_structure V q hq hker hcore T L hL hcomm hprod
  refine ⟨le_antisymm (le_inf hQR (hT.le.trans inf_le_right)) ?_, hP, hF⟩
  exact (inf_le_inf_right _ hRT).trans hT.ge

/-- The noncentralizing branch of B.2.10(2), for the literal relative
offender family and quotient map. Its elementary generator is extracted
from that family; the image and Sylow structure are proved from the source
alternatives. Only `O₂(G) ≤ R` is needed for this deduction. -/
theorem relativeMaxOffenderImages_fitting_eq
    (V R L : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (V : Set G))
    (hcore : pCore 2 H = ⊥) (T : Sylow 2 G)
    (hQR : pCore 2 G ≤ R)
    (hL : (L.IsCComponent ∧ IsQuasisimple (L ⧸ pCore 2 L)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Multiplicative (ZMod 3)))
    (hcomm : ⁅V, L⁆ ≠ ⊥)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l * t = g)
    (hJ : ¬ elementaryAbelianMaxJ R ≤ q.ker) :
    let N := generatedBy (relativeMaxOffenderImages R V q) ⊤
    (generalizedFitting N).map N.subtype = L.map q := by
  have hVR : V ≤ R := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩).trans hQR
  let N := generatedBy (relativeMaxOffenderImages R V q) ⊤
  let : N.Normal :=
    (relativeMaxOffenderImages_generated_facts V R hVR q hq hker hJ).1
  obtain ⟨A, _, hAe, hAN⟩ :=
    relativeMaxOffenderImages_exists_elementary_generator V R hVR q hq hker hJ
  let : IsElementaryAbelian 2 A := hAe.2
  exact internalModule_normal_generalizedFitting V q hq hker hcore T L hL
    hcomm hprod N A (IsElementaryAbelian.isPGroup 2 A) hAe.1 hAN

end CFSG.Quasithin.ChapterB
