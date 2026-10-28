module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic.Natural
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount.NaturalParabolic.Parabolic

/-!
# The natural and parabolic-core contributions in 13.5.22(2)

The original NaturalLayer supplies s natural planes on the literal residual
section. Sylow conjugacy adjusts its matrix marking and coordinates together.
Each natural plane has an invariant F4-line; this line and its quotient are
irreducible noncentral binary planes. Their flags give exactly 2s chief factors, including
s = 0. The interval above S intersect L1 has the actual conjugation action on
the Borel two-core and contributes one more noncentral two-chief factor.

The exports give actual refinements and the count for every chief series with
the specified endpoints. The chapter13Setup applications identify the original
embedded residual and preserve the original right conjugator, c and s.
Complete-series concatenation, the lower orthogonal contribution, both order
formulas and the contradiction remain with the 13.5.22 assembly owner.

Source: Aschbacher--Smith, 13.5.22(2), printed p.924/PDF p.941, using G.2.4.
-/

@[expose] public section
open Subgroup NoncentralChiefRefinement
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
open ChapterG.Section02 ChapterG.Section02.Setup
open ChapterG.Section02.AlternatingFive
open ChapterG.Section02.AlternatingFive.Recognition.ProjectiveGeometry
universe u
variable {G : Type u} [Group G] [Finite G] {D : Setup G} {g : G}

/-- The actual natural section has an actual chief refinement, also for s = 0. -/
theorem exists_natural_upper_refinement (d : Hypothesis D g) (hgen : D.I g = D.L)
    [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]
    {s : ℕ} (c : NaturalLayer D g F4 s d.L_le_I) :
    ∃ t : ChiefSeries D.L₁, t.head = second d ∧ t.last = core d ∧
      t.length = 2 * s ∧ t.noncentralTwoCount = 2 * s :=
  NaturalParabolic.exists_natural_refinement d hgen c

/-- Every series on the natural upper interval has twice the original multiplicity. -/
theorem natural_upper_count (d : Hypothesis D g) (hgen : D.I g = D.L)
    [((AlternatingFive.S₂ D g).subgroupOf (D.S g)).Normal]
    {s : ℕ} (c : NaturalLayer D g F4 s d.L_le_I)
    (t : ChiefSeries D.L₁) (ht0 : t.head = second d) (ht1 : t.last = core d) :
    t.noncentralTwoCount = 2 * s := NaturalParabolic.natural_count d hgen c t ht0 ht1

/-- The parabolic interval is itself one noncentral binary chief interval. -/
theorem parabolic_core_chief (d : Hypothesis D g) :
    core d ⋖ localCore D ∧ IsNoncentralTwo (core d) (localCore D) :=
  NaturalParabolic.parabolic_chief d

theorem exists_parabolic_core_refinement (d : Hypothesis D g) :
    ∃ t : ChiefSeries D.L₁, t.head = core d ∧ t.last = localCore D ∧
      t.length = 1 ∧ t.noncentralTwoCount = 1 :=
  NaturalParabolic.exists_parabolic_refinement d

theorem parabolic_core_count (d : Hypothesis D g) (t : ChiefSeries D.L₁)
    (ht0 : t.head = core d) (ht1 : t.last = localCore D) :
    t.noncentralTwoCount = 1 := NaturalParabolic.parabolic_count d t ht0 ht1

/-- Original-L1 natural count, preserving the original right conjugator and c. -/
theorem source_natural_count
    (V₁ V₃ V Lminus T H L₁ U_H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    [((AlternatingFive.S₂ (chapter13Setup V₁ V₃ Lminus T H) g).subgroupOf
      ((chapter13Setup V₁ V₃ Lminus T H).S g)).Normal]
    {s : ℕ} (c : NaturalLayer (chapter13Setup V₁ V₃ Lminus T H) g F4 s d.L_le_I)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hU : U_H = conjugateSpanBy V₃ H)
    (hgen : Lminus = U_H ⊔ conjugate U_H g)
    (t : ChiefSeries L₁)
    (h0 : t.head.val = (V ⊔ (U_H ⊓ conjugate U_H g)).subgroupOf L₁)
    (h1 : t.last.val = (Lminus.pCoreIn 2).subgroupOf L₁) :
    t.noncentralTwoCount = 2 * s := by
  subst L₁
  have hI : (chapter13Setup V₁ V₃ Lminus T H).I g =
      (chapter13Setup V₁ V₃ Lminus T H).L := by
    simpa only [Setup.I, Setup.U, chapter13Setup, ← hU] using hgen.symm
  have hS : (chapter13Setup V₁ V₃ Lminus T H).S g = Lminus.pCoreIn 2 := by
    change ((chapter13Setup V₁ V₃ Lminus T H).I g).pCoreIn 2 = _
    rw [hI]
    rfl
  apply natural_upper_count d hI c t
  · apply Subtype.ext
    simpa only [second, AlternatingFive.S₂, Setup.VL, Setup.U, chapter13Setup,
      hspan, ← hU] using h0
  · apply Subtype.ext
    simpa only [core, hS] using h1

/-- Original-L1 parabolic count uses the intrinsic two-core, not an ambient-normal core. -/
theorem source_parabolic_count
    (V₁ V₃ Lminus T H L₁ U_H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hU : U_H = conjugateSpanBy V₃ H)
    (hgen : Lminus = U_H ⊔ conjugate U_H g)
    (t : ChiefSeries L₁)
    (h0 : t.head.val = (Lminus.pCoreIn 2).subgroupOf L₁)
    (h1 : t.last.val = pCore 2 L₁) : t.noncentralTwoCount = 1 := by
  subst L₁
  have hI : (chapter13Setup V₁ V₃ Lminus T H).I g =
      (chapter13Setup V₁ V₃ Lminus T H).L := by
    simpa only [Setup.I, Setup.U, chapter13Setup, ← hU] using hgen.symm
  have hS : (chapter13Setup V₁ V₃ Lminus T H).S g = Lminus.pCoreIn 2 := by
    change ((chapter13Setup V₁ V₃ Lminus T H).I g).pCoreIn 2 = _
    rw [hI]
    rfl
  apply parabolic_core_count d t
  · apply Subtype.ext
    simpa only [core, hS] using h0
  · exact Subtype.ext h1

/-- Actual refinements on the original L1, with synchronized endpoints and the same s. -/
theorem source_natural_parabolic_refinements
    (V₁ V₃ V Lminus T H L₁ U_H : Subgroup G) (g : G)
    (d : Hypothesis (chapter13Setup V₁ V₃ Lminus T H) g)
    [((AlternatingFive.S₂ (chapter13Setup V₁ V₃ Lminus T H) g).subgroupOf
      ((chapter13Setup V₁ V₃ Lminus T H).S g)).Normal]
    {s : ℕ} (c : NaturalLayer (chapter13Setup V₁ V₃ Lminus T H) g F4 s d.L_le_I)
    (hspan : conjugateSpanBy V₁ Lminus = V)
    (hresidual : L₁ = (chapter13Setup V₁ V₃ Lminus T H).L₁)
    (hU : U_H = conjugateSpanBy V₃ H)
    (hgen : Lminus = U_H ⊔ conjugate U_H g) :
    ∃ t u : ChiefSeries L₁,
      t.head.val = (V ⊔ (U_H ⊓ conjugate U_H g)).subgroupOf L₁ ∧
      t.last.val = (Lminus.pCoreIn 2).subgroupOf L₁ ∧
      t.length = 2 * s ∧ t.noncentralTwoCount = 2 * s ∧
      u.head = t.last ∧ u.last.val = pCore 2 L₁ ∧
      u.length = 1 ∧ u.noncentralTwoCount = 1 := by
  subst L₁
  have hI : (chapter13Setup V₁ V₃ Lminus T H).I g =
      (chapter13Setup V₁ V₃ Lminus T H).L := by
    simpa only [Setup.I, Setup.U, chapter13Setup, ← hU] using hgen.symm
  have hS : (chapter13Setup V₁ V₃ Lminus T H).S g = Lminus.pCoreIn 2 := by
    change ((chapter13Setup V₁ V₃ Lminus T H).I g).pCoreIn 2 = _
    rw [hI]
    rfl
  obtain ⟨t, ht0, ht1, htl, htc⟩ := exists_natural_upper_refinement d hI c
  obtain ⟨u, hu0, hu1, hul, huc⟩ := exists_parabolic_core_refinement d
  refine ⟨t, u, ?_, ?_, htl, htc, hu0.trans ht1.symm, ?_, hul, huc⟩
  · rw [ht0]
    simp only [second, AlternatingFive.S₂, Setup.VL, Setup.U, chapter13Setup, hspan, ← hU]
    rfl
  · rw [ht1]
    change ((chapter13Setup V₁ V₃ Lminus T H).S g).subgroupOf _ = _
    rw [hS]
  · rw [hu1]
    rfl

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.ChiefCount
