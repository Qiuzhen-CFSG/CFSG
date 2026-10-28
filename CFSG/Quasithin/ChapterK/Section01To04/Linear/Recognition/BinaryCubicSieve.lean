module

public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.Setup
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.Support
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FourDisplacement
public import CFSG.Quasithin.ChapterK.Section01To04.Linear.Recognition.BinaryCubicSieve.FiveDisplacement
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FourSmallModules
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition.FiveDegreeGap

/-!
# Binary cubic degree sieves for K.3.2

The original ambient cubic actor maps into the marked component normalizer.
A multiple-support displacement estimate excludes every local highest vector
with two or more active roots. Faithfulness excludes empty support, while the
existing singleton calculations give the required small degree. We then apply
the actual small-module theorems through the canonical SL-to-PSL maps.

The SL₄ and SL₅ displacement theorems discharge both multiple-support
estimates using only finite dimension, faithfulness and irreducibility of the
marked component action. The resulting degree bounds and small-module
applications retain the original ambient cubic-ratio hypothesis. No degree
cutoff, cubic bound on the component restriction, or module catalogue is
assumed. The earlier conditional interfaces remain available.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), printed
pp.451,454–455/PDF pp.462,465–466, citing GM04 Proposition 4.6 and Table 7.
-/

public section
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve

open Representation Representation.BinaryOffender Representation.BinaryLinearRecognition

open ChapterG.Section09
open ChapterG.Section09.DefiningCharacteristic.BinaryLinearRecognition

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {L : Subgroup G}

/-- A root displacement estimate forces the degree-four small-module window
from the original ambient cubic hypothesis. -/
theorem four_finrank_le_ten_of_displacement {K : GroupClass}
    (h : SourceHypothesis K ρ L)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hmove : FourMultipleSupportDisplacement (modelAction ρ e)) :
    Module.finrank (ZMod 2) V ≤ 10 := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  let σ := modelAction ρ e
  let : IsIrreducible σ := modelAction_irreducible ρ h.irreducible e
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  have hf := modelAction_injective ρ h.faithful e
  obtain ⟨A, hA, hc, hr, hd, _⟩ := source_four_actor h e
  obtain ⟨J, v, hv, hJ⟩ := FourSmallModules.exists_localHighestVector σ
  have hpos := Finset.card_pos.mpr (hJ.nonempty_of_faithful hf hv)
  have hone : J.card = 1 := by
    by_contra hn
    exact (not_lt_of_ge hd) (hmove J v hv hJ (by omega) A hA hc hr)
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
  fin_cases i
  · exact (hJ.finrank_le_four_of_endpoint hv (Or.inl rfl)).trans (by decide)
  · obtain ⟨_, f, _⟩ := hJ.quasiequivalent_orthogonalEight_of_middle hv
    have hh := f.finrank_eq.trans finrank_orthogonalEight
    omega
  · exact (hJ.finrank_le_four_of_endpoint hv (Or.inr rfl)).trans (by decide)

/-- Actual application of `FourSmallModules.small_modules`, retaining the
literal canonical quotient and the resulting intertwiner on the original L. -/
theorem four_small_modules_of_displacement {K : GroupClass}
    (h : SourceHypothesis K ρ L)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    (hmove : FourMultipleSupportDisplacement (modelAction ρ e)) :
    Module.finrank (ZMod 2) V = 4 ∨
      Quasiequivalent (ρ.comp L.subtype) orthogonalEightAction := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  let q := Atlas.Order20160A8.sl4TwoEquivPSL
  let τ := modelAction ρ (e.trans q)
  have hf := modelAction_injective ρ h.faithful (e.trans q)
  have hi := modelAction_irreducible ρ h.irreducible (e.trans q)
  have hd := four_finrank_le_ten_of_displacement h e hmove
  rcases FourSmallModules.small_modules τ hf hi hd with hfour | hortho
  · exact Or.inl hfour
  · obtain ⟨E, f, hinter⟩ := hortho
    refine Or.inr ⟨(e.trans q).trans E, f, ?_⟩
    intro g v
    have hh := hinter ((e.trans q) g) v
    simpa [τ, modelAction] using hh

/-- A multiple-support displacement estimate gives the degree-five window;
the singleton-support calculation uses no prior degree assumption. -/
theorem five_finrank_le_fourteen_of_displacement {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group)
    (hmove : FiveMultipleSupportDisplacement (modelAction ρ e)) :
    Module.finrank (ZMod 2) V ≤ 14 := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  let σ := modelAction ρ e
  let : IsIrreducible σ := modelAction_irreducible ρ h.irreducible e
  let : Nontrivial V := Subrepresentation.irreducible_module_nontrivial σ
  have hf := modelAction_injective ρ h.faithful e
  obtain ⟨A, hA, hc, hr, hd, _⟩ := source_five_actor h e
  obtain ⟨J, v, hv, hJ⟩ := FiveDegreeGap.exists_localHighestVector σ
  have hpos := Finset.card_pos.mpr (FiveDegreeGap.support_nonempty hf hv hJ)
  have hone : J.card = 1 := by
    by_contra hn
    exact (not_lt_of_ge hd) (hmove J v hv hJ (by omega) A hA hc hr)
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hone
  rcases FiveDegreeGap.finrank_eq_five_or_ten_of_singleton hJ hv with hh | hh <;> omega

/-- Actual application of `FiveDegreeGap.finrank_eq_five_or_ten` to the
projective model inflated along the canonical SL₅-to-PSL₅ quotient. -/
theorem five_degrees_of_displacement {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group)
    (hmove : FiveMultipleSupportDisplacement (modelAction ρ e)) :
    Module.finrank (ZMod 2) V = 5 ∨ Module.finrank (ZMod 2) V = 10 := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  let q := SL5TenDimensional.projectiveEquiv
  let τ := modelAction ρ (e.trans q)
  have he : τ.comp q.toMonoidHom = modelAction ρ e := modelAction_trans_comp ρ e q
  have hf : Function.Injective (τ.comp q.toMonoidHom) := by
    rw [he]
    exact modelAction_injective ρ h.faithful e
  have hi : IsIrreducible (τ.comp q.toMonoidHom) := by
    rw [he]
    exact modelAction_irreducible ρ h.irreducible e
  exact FiveDegreeGap.finrank_eq_five_or_ten (τ.comp q.toMonoidHom) hf hi
    (five_finrank_le_fourteen_of_displacement h e hmove)

/-- The binary SL₄ degree window follows from the original ambient cubic
bound. The full-normalizer multiple-support estimate is discharged on the
actual marked component, retaining actors outside L. -/
theorem four_finrank_le_ten {K : GroupClass}
    (h : SourceHypothesis K ρ L)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Module.finrank (ZMod 2) V ≤ 10 := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  exact four_finrank_le_ten_of_displacement h e
    (FourDisplacement.multiple_support_displacement (modelAction ρ e)
      (modelAction_injective ρ h.faithful e)
      (modelAction_irreducible ρ h.irreducible e))

/-- Apply the SL₄ small-module theorem with the degree cutoff proved from
the source hypotheses. The canonical SL-to-PSL transport yields the actual
orthogonal intertwiner on the original component L. -/
theorem four_small_modules {K : GroupClass}
    (h : SourceHypothesis K ρ L)
    (e : L ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) :
    Module.finrank (ZMod 2) V = 4 ∨
      Quasiequivalent (ρ.comp L.subtype) orthogonalEightAction := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  exact four_small_modules_of_displacement h e
    (FourDisplacement.multiple_support_displacement (modelAction ρ e)
      (modelAction_injective ρ h.faithful e)
      (modelAction_irreducible ρ h.irreducible e))

/-- The binary SL₅ degree window follows from the original ambient cubic
bound. Both the inner and graph displacement estimates are discharged on
the actual marked component. -/
theorem five_finrank_le_fourteen {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group) :
    Module.finrank (ZMod 2) V ≤ 14 := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  exact five_finrank_le_fourteen_of_displacement h e
    (FiveDisplacement.multiple_support_displacement (modelAction ρ e)
      (modelAction_injective ρ h.faithful e)
      (modelAction_irreducible ρ h.irreducible e))

/-- Apply the SL₅ degree-gap theorem to the projective action inflated by
the canonical SL-to-PSL map, with its cutoff supplied by the ambient cubic
hypothesis and no remaining displacement premise. -/
theorem five_degrees {K : GroupClass}
    (h : SourceHypothesis K ρ L) (e : L ≃* SL5TenDimensional.Group) :
    Module.finrank (ZMod 2) V = 5 ∨ Module.finrank (ZMod 2) V = 10 := by
  let : FiniteDimensional (ZMod 2) V := h.finite_module
  exact five_degrees_of_displacement h e
    (FiveDisplacement.multiple_support_displacement (modelAction ρ e)
      (modelAction_injective ρ h.faithful e)
      (modelAction_irreducible ρ h.irreducible e))

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve
