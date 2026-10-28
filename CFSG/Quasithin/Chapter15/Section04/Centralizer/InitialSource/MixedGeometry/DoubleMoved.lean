module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.DoubleCenter
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.ActionConstruction.SourceFactors

/-!
# The actual double-factor commutator lines

Apply the checked fixed-space decomposition to the same residual pair and its
original moved modules. Baumann's source action gives the elementary ambient
module and both fixed lines; the cardinal-four saturation argument identifies
these lines with the literal commutator intersections used in the mixed branch.

Source: Aschbacher--Smith, 15.4.12 and 15.4.18, pp.1160--1163.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
open FamilySource FamilySource.ModuleStructure TwoFactors TwoFactors.SourceFactors
variable {G : Type*} [Group G] [Finite G]
variable {κ : GroupClass} {T : Sylow 2 G} {M X : Subgroup G}

theorem Pair.source_double_fixed_geometry (p : Pair T M X) (h : Input κ T M X 2) :
    let E := ChapterB.thompsonAlpha (T : Subgroup G)
    let L := p.quotient.factor
    (∀ i, (E ⊓ centralizer (L i : Set G)) ⊔ (⁅E,L i⁆ ⊓ E) = E ∧
      Disjoint (E ⊓ centralizer (L i : Set G)) (⁅E,L i⁆ ⊓ E) ∧
      Nat.card (⁅E,L i⁆ ⊓ E : Subgroup G) = 2) ∧
      (E ⊓ centralizer (X : Set G)) ⊔ ((⁅E,L false⁆ ⊓ E) ⊔ (⁅E,L true⁆ ⊓ E)) = E ∧
      Disjoint (E ⊓ centralizer (X : Set G)) ((⁅E,L false⁆ ⊓ E) ⊔ (⁅E,L true⁆ ⊓ E)) ∧
      Disjoint (⁅E,L false⁆ ⊓ E) (⁅E,L true⁆ ⊓ E) := by
  let E := ChapterB.thompsonAlpha (T : Subgroup G)
  let S := ChapterB.baumann (T : Subgroup G)
  let C := E ⊓ centralizer (X : Set G)
  let W := movedModule (T : Subgroup G) M X
  let V := p.quotient.moduleFactor
  let : IsElementaryAbelian 2 E := Stellmacher.omegaOneCenterAmbient_elementaryAbelian _
  have hg := source_thompsonGeometry h
  have ha := p.factor_actions_thompson h hg (show S ≤ T from inf_le_left) (p.baumann false)
  dsimp only at ha
  rw [p.quotient.factor_generate h] at ha
  obtain ⟨hVS, hnV, hVne, hcomm, hdis, hCdis, hdecomp, hindex, hcross, hfree⟩ := ha
  have hcards := fixed_lines_of_index_four (T.isPGroup'.to_le (show S ≤ T from inf_le_left))
    (hVS false) (hVS true) (hnV false) (hnV true) (hVne false) (hVne true)
    hcomm hdis hCdis hdecomp hindex
  let U := E ⊔ W
  let : IsElementaryAbelian 2 U := (MarkedProduct.source_baumann_module h).1
  have hVU : V false ⊔ V true ≤ U := p.module_join ▸ le_sup_right
  have hCU : C ≤ U := inf_le_left.trans le_sup_left
  have hUC : C ⊔ W = U := by
    calc
      C ⊔ W = (C ⊔ (W ⊓ centralizer (S : Set G))) ⊔ W := by
        exact ((sup_assoc C _ W).trans (congrArg (C ⊔ ·)
          (sup_eq_right.mpr (show W ⊓ centralizer (S : Set G) ≤ W from inf_le_left)))).symm
      _ = U := by rw [hg.decomposition]
  have hCW : C ≤ centralizer (W : Set G) := by
    intro c hc w hw
    exact setLike_mul_comm (mem_sup_right hw : w ∈ U) (hCU hc)
  have hCeq : C = U ⊓ centralizer ((p.quotient.factor false ⊔ p.quotient.factor true : Subgroup G) : Set G) := by
    rw [p.quotient.factor_generate h]
    exact (fixed_summand_eq_centralizer hUC hCW inf_le_right hg.moved_fixed).symm
  have hsplit := fixed_subgroup_split_of_internal_factors hdis hcomm (hnV false) (hnV true)
  rw [hsplit] at hdecomp
  have hn₁ : p.quotient.factor false ≤ normalizer (V false : Set G) :=
    normalizer_commutator_ge_right (localV (T : Subgroup G) M) (p.quotient.factor false)
  have hn₂ : p.quotient.factor true ≤ normalizer (V true : Set G) :=
    normalizer_commutator_ge_right (localV (T : Subgroup G) M) (p.quotient.factor true)
  have hcross₁ : V false ≤ centralizer (p.quotient.factor true : Set G) := hcross true
  have hcross₂ : V true ≤ centralizer (p.quotient.factor false : Set G) := hcross false
  have hcard₁ : Nat.card (V false) = 4 := p.module_card false
  have hcard₂ : Nat.card (V true) = 4 := p.module_card true
  let commU : IsMulCommutative U := inferInstance
  have hd := @double_factor_fixed_decomposition G _ _ E C (V false) (V true)
    (V false ⊓ centralizer (S : Set G)) (V true ⊓ centralizer (S : Set G))
    (p.quotient.factor false) (p.quotient.factor true) U commU
    hCeq hVU hdecomp inf_le_left inf_le_left hCdis hdis hcross₁ hcross₂ hn₁ hn₂
    hcard₁ hcard₂ hcards.1 hcards.2
  rw [p.quotient.factor_generate h] at hd
  obtain ⟨hf,hdf,hcf,ht,hdt,hct,hw,hdw,hdtwo,_⟩ := hd
  refine ⟨?_,hw,hdw,hdtwo⟩
  intro i
  cases i
  · exact ⟨hf,hdf,hcf⟩
  · exact ⟨ht,hdt,hct⟩

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.SourceWitnesses
