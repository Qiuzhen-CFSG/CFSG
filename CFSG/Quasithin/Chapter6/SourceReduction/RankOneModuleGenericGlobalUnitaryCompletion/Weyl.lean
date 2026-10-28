module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourWeyl
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveWeyl

/-!
# Native Weyl defects in the original unitary normalizer completion

The marked full extension and the ambient order bound give the same
faithful completion in the original simple group. For its literal native
reflections, a power in the native overlap is trivial; a power in the full
overlap has square one. Both parameter conventions and the complete
extension factor are retained. The possible outer involution and apartment
closure remain unresolved, so these assertions are not PSU recognition.

Source: Aschbacher–Smith 5.3.1–4 and F.4.10,16–17,
printed pp.658–659,279,282–283 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

/-- Native defect control with both original U₄ comparison orientations,
including the degree-two comparison and the strict unitary exponent. -/
theorem Preparation.unitary_native_rotation_defects
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
      ∀ k : ℕ,
        (FourWeyl.rotation m hm E c ^ k = 1 ↔
          FourWeyl.rotation m hm E c ^ k ∈ (E.innerMiddle c).range) ∧
        (FourWeyl.rotation m hm E c ^ k ∈ c.middle.range →
          (FourWeyl.rotation m hm E c ^ k)^2 = 1) := by
  obtain ⟨hmgt,hn,c,ho,hN,_⟩ := d.unitary_native_ambient_completion h hH hp m hm hc E he horder
  exact ⟨hmgt,hn,c,ho,hN,fun k => ⟨FourWeyl.power_eq_one_iff_nativeOverlap m hm E c k,
    FourWeyl.power_sq_eq_one_of_middle m hm E c k⟩⟩

/-- The actual parameter-four projective model supplies a hyperbolic
coordinate choice, with scalar kernel five and original n = 4 retained. -/
theorem Preparation.unitaryFive_native_rotation_defects
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
      ∃ t : U.F, ∃ ht : t + U.form.conj t = 1, ∀ k : ℕ,
        (FiveWeyl.rotation U t ht E c ^ k = 1 ↔
          FiveWeyl.rotation U t ht E c ^ k ∈ (E.innerMiddle c).range) ∧
        (FiveWeyl.rotation U t ht E c ^ k ∈ c.middle.range →
          (FiveWeyl.rotation U t ht E c ^ k)^2 = 1) := by
  obtain ⟨hn,c,ho,hN,_⟩ := d.unitaryFive_native_ambient_completion h hH hp U hc E he horder
  obtain ⟨t,ht⟩ := Theory.SpecificGroups.UnitaryFive.RadicalCentralizers.exists_trace_one
    U.form U.conjugation U.card
  exact ⟨hn,c,ho,hN,t,ht,fun k => ⟨FiveWeyl.power_eq_one_iff_nativeOverlap U t ht E c k,
    FiveWeyl.power_sq_eq_one_of_middle U t ht E c k⟩⟩
end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
