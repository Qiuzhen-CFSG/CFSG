module

public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.OriginalConstituentSource
public import CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components.NonabelianBinaryFixed

/-!
# Original CaseFive binary geometry from the actual module rows

The selected center constituent is proved natural by the local deleted-eight
obstruction. The existing pointwise residual and fixed-space lemmas then give
the original binary plane extension directly, with both fixed four-groups,
the same parabolic and the complete action kernel retained. No independent
NaturalReduction4 hypothesis or replacement constituent is used.
Source: Aschbacher--Smith 12.9.4, printed pp.859--860.
-/

public noncomputable section
open Subgroup Module Theory.GroupTheory Representation
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
open Section02 Section08 Section08.InvariantFlag Section08.InvariantFlag.Symplectic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual original CaseFive configuration supplies its full binary
geometry after the local naturality proof, with the same component and seed. -/
theorem nonabelian_caseFive_binary_geometry_of_original_rows
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 4)
    (preferred : PreferredDimension KnownSimple.IsKnownSimple T 4)
    (earlier : EarlierSetupResults.{u} KnownSimple.IsKnownSimple)
    (F : InvariantFlag T V 4) (hne : ¬ IsMulCommutative F.U)
    [IsElementaryAbelian 2 F.Uhat] (g : G) (hgP : g ∈ F.P L) (hgH : g ∉ F.H)
    (B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat))
    (h5 : ChapterG.Section11.CaseFive F.terminalRepresentation B) :
    ∃ (v : Additive F.Uhat) (C : ComponentGeometry F L) (I : Subgroup G)
      (c : ChosenModule T C.K1 I),
      v ≠ 0 ∧ hatSpace F (F.Vi 2) = Submodule.span (ZMod 2) {v} ∧
      NaturalModule c 4 ∧ I ≤ F.ZU ∧ I = ⁅F.ZU,C.K1⁆ ∧
      let D := I ⊓ centralizer (conjugate F.ZU g : Set G)
      let E := F.Vi 2 ⊔ D
      let A := E ⊓ Section08.centerIn (F.I₂ L)
      let P := componentPlanePreimage F C v
      Nat.card D = 4 ∧ IsElementaryAbelian 2 E ∧ Nat.card E = 16 ∧
      Disjoint (F.Vi 2) D ∧ P ≤ normalizer (D : Set G) ∧
      ⁅E,componentPlaneResidual F C v⁆ = D ∧
      (∀ J : Subgroup G, J ≤ D → componentPlaneResidual F C v ≤ normalizer (J : Set G) →
        J = ⊥ ∨ J = D) ∧
      E = F.Vi 2 ⊔ A ∧ Disjoint (F.Vi 2) A ∧ Nat.card A = 4 ∧
      E ⊓ centralizer (F.I₂ L : Set G) = A ∧ A ≤ F.ZU ∧ D ≤ A ⊔ F.Vi 1 ∧
      ⁅E,F.I₂ L⁆ = F.Vi 2 ∧
      F.I₂ L ⊓ centralizer (E : Set G) = (F.I₂ L).pCoreIn 2 ∧
      P ⊔ F.I₂ L ≤ normalizer (E : Set G) ∧
      (T : Subgroup G) ≤ P ⊔ F.I₂ L ∧
      (T : Subgroup G) ≤ normalizer (F.Vi 2 : Set G) ⊓ normalizer (D : Set G) ∧
      (centralizer (E : Set G)).relIndex (T : Subgroup G) ≤ 4 ∧
      (∀ t ∈ (T : Subgroup G), t ^ 2 ∈ centralizer (E : Set G)) ∧
      (∀ y ∈ P ⊔ F.I₂ L, y ^ 4 ∈ centralizer (E : Set G) →
        y ^ 2 ∈ centralizer (E : Set G)) ∧
      ¬ P ≤ F.Gi 2 := by
  obtain ⟨C,I,c,hnat,_,hiZ,_,hi,_,_,_⟩ :=
    nonabelian_caseFive_natural_constituent_of_original_rows modules h preferred earlier
      F hne g hgP hgH B h5
  obtain ⟨_,_,v,_,_,_,hv,hline,_⟩ :=
    nonabelian_transvection_geometry h earlier F hne g hgP hgH
  obtain ⟨_,hPD,hPE⟩ := nonabelian_caseFive_component_plane_fixed_nontrivial
    h earlier F hne g hgP hgH B h5 C v hv hline c hiZ hi
  obtain ⟨he,hcD,hRD⟩ := nonabelian_caseFive_planeResidual_fixed_eq_returning
    h earlier F hne g hgP hgH B h5 C v hv hline c hnat hiZ hi
  rw [he] at hcD hPD hPE
  obtain ⟨hE,hcE⟩ := nonabelian_caseFive_plane_extension_card h F hne C c hnat hiZ
    (show I ⊓ centralizer (conjugate F.ZU g : Set G) ≤ I from inf_le_left)
  rw [hcD] at hcE
  have hd := (nonabelian_caseFive_chosen_disjoint_seed h F hne C c hnat hiZ).symm.mono
    (F.le_seed 2) (show I ⊓ centralizer (conjugate F.ZU g : Set G) ≤ I from inf_le_left)
  have hirr := nonabelian_caseFive_returning_fixed_irreducible
    h earlier F hne g hgP hgH B h5 C v hv hline c hnat hiZ hi
  have hIE := (nonabelian_caseFive_returning_fixed_extension h (.inl rfl) earlier
    F hne g hgP hgH B h5 hiZ).2
  have hnot := nonabelian_caseFive_componentPlanePreimage_not_le_plane
    h earlier F hne g hgP hgH B h5 C v hv hline
  obtain ⟨hsplit,hdis,hcA,hfix,hmove⟩ := nonabelian_caseFive_binary_fixed_complement
    h earlier F hne g hgP hgH B h5 C c hnat hiZ hcD
  obtain ⟨hAZ,hDA⟩ := nonabelian_caseFive_binary_fixed_placement
    h earlier F hne g hgP hgH B h5 hiZ
  have hTP : (T : Subgroup G) ≤ componentPlanePreimage F C v :=
    le_sup_right.trans (componentPlanePreimage_contains F C v hv hline)
  have hsmall := two_group_four_factors_action (T : Subgroup G) (F.Vi 2)
    (I ⊓ centralizer (conjugate F.ZU g : Set G)) T.isPGroup'
    (by simpa using F.card 2 (by decide)) hcD (F.invariant 2) (hTP.trans hPD)
  refine ⟨v,C,I,c,hv,hline,hnat,hiZ,hi,hcD,hE,hcE,hd,hPD,hRD,hirr,
    hsplit,hdis,hcA,hfix,hAZ,hDA,hmove,?_,sup_le hPE hIE,hTP.trans le_sup_left,
    le_inf (F.invariant 2) (hTP.trans hPD),hsmall.1,hsmall.2,?_,hnot⟩
  · exact (nonabelian_binary_extension_kernel h earlier F hne g hgP hgH hsplit).1
  · exact fourth_power_centralizes_implies_square T _ _
      (hTP.trans le_sup_left) (sup_le hPE hIE) hsmall.2

end CFSG.Quasithin.Chapter12.Section09.NaturalSource.Components
