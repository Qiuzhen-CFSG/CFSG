module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourApartment
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveApartment

/-!
# Closed unitary apartments in the original normalizer completion

Apply the native split-torus fixed-neighbor calculation to the actual full
extension supplied by the parent. The literal original normalizers yield
an apartment whose rotation has fourth power in the whole middle and eighth
power one. This keeps both orientations, the degree-two U₄ comparison, the
strict exponent m > 1, and the actual projective PSU₅(4) quotient.

The possible outer involutory fourth power remains to be eliminated before
recognition and GlobalExit. Source: Aschbacher–Smith 5.3.1–4 and F.4.10,16–17,
printed pp.658–659,279,282–283 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

/-- Native defect control with both original U₄ comparison orientations,
including the degree-two comparison and the strict unitary exponent. -/
theorem Preparation.unitary_closed_apartment
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (m : ℕ) (hm : 1 ≤ m)
    (hc : FourLocalComparison L (residual H) (sourceS L H) m hm)
    (E : FourExtension m hm) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    1 < m ∧ n = 2*m ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := G),
      c.left.range ⊓ c.right.range = c.middle.range ∧ E.innerGenerated c = ⊤ ∧
      FourWeyl.rotation m hm E c ^ 4∈c.middle.range ∧
      FourWeyl.rotation m hm E c ^ 8=1 := by
  obtain ⟨hmgt,hn,c,ho,hN,_⟩ := d.unitary_native_ambient_completion h hH hp m hm hc E he horder
  exact ⟨hmgt,hn,c,ho,hN,FourWeyl.fourth_mem_middle m hm hmgt E c ho horder,
    FourWeyl.eighth_eq_one m hm hmgt E c ho horder⟩

/-- The actual parameter-four projective model supplies a hyperbolic
coordinate choice, with scalar kernel five and original n = 4 retained. -/
theorem Preparation.unitaryFive_closed_apartment
    {G : Type*} [Group G] [Finite G]
    {T : Sylow 2 G} {L W H A C : Subgroup G} {n : ℕ}
    (d : Preparation T L H A C (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (U : ChapterF.GreenBook.UnitaryFive.Model 4)
    (hc : FiveLocalComparison L (residual H) (sourceS L H) U)
    (E : FiveExtension U) (he : Compatible L (residual H) E)
    (horder : Nat.card G ≤ Nat.card E.carrier) :
    n = 4 ∧ ∃ c : RankTwoAmalgam.FaithfulCompletion E.amalgam (G := G),
      c.left.range ⊓ c.right.range = c.middle.range ∧ E.innerGenerated c = ⊤ ∧
      ∃ t : U.F, ∃ ht : t + U.form.conj t = 1,
        FiveWeyl.rotation U t ht E c ^ 4∈c.middle.range ∧
        FiveWeyl.rotation U t ht E c ^ 8=1 := by
  obtain ⟨hn,c,ho,hN,_⟩ := d.unitaryFive_native_ambient_completion h hH hp U hc E he horder
  obtain ⟨t,ht⟩ := Theory.SpecificGroups.UnitaryFive.RadicalCentralizers.exists_trace_one
    U.form U.conjugation U.card
  exact ⟨hn,c,ho,hN,t,ht,FiveWeyl.fourth_mem_middle U t ht E c ho horder,
    FiveWeyl.eighth_eq_one U t ht E c ho horder⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
