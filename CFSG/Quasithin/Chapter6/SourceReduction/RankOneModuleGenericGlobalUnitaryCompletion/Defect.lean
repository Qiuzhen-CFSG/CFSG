module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalUnitaryCompletion.FiveGeometry
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FourRootDefect
public import CFSG.Quasithin.ChapterF.Section04.SourceCompletion.UnitaryNonbinary.FiveDefect

/-!
# Full Cartan defects in the original normalizer completion

The parent-supplied compatible DGS realization and ambient order bound
produce the literal original normalizer completion. Its native quarter-turn
has a fourth-power defect represented in the full overlap by an involution
fixing the full native Cartan and both reflections and preserving the native
parabolics. This retains both orientations and the degree-two U₄ comparison,
with m > 1 and n = 2*m; the actual PSU₅(4) branch retains n = 4.

These are proved local constraints, not an assumed rigidity input or a
GlobalExit theorem. Source: Aschbacher–Smith 5.3.1–4 and F.4.10,16–17,
printed pp.658–659,279,282–283 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open Subgroup Theory.GroupTheory
open ChapterF.SourceCompletion.UnitaryNonbinary UnitaryCompletion

/-- Native defect control with both original U₄ comparison orientations,
including the degree-two comparison and the strict unitary exponent. -/
theorem Preparation.unitary_cartan_defect
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
      ∃ a : E.middle, c.middle a=FourWeyl.rotation m hm E c ^ 4 ∧
        SourceExtension.CartanFixedInvolution (FourWeyl.point m hm) (FourWeyl.plane m hm)
          (FourWeyl.diagonalCartan m hm) a.val := by
  obtain ⟨hmgt,hn,c,ho,hN,_⟩ := d.unitary_native_ambient_completion h hH hp m hm hc E he horder
  exact ⟨hmgt,hn,c,ho,hN,FourWeyl.fourth_defect m hm hmgt E c ho horder⟩

/-- Actual simple-root invariance with both original U₄ comparison orientations,
including the degree-two comparison and the strict unitary exponent. -/
theorem Preparation.unitary_simple_root_defect
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
      ∃ a : E.middle, c.middle a=FourWeyl.rotation m hm E c ^ 4 ∧
        SourceExtension.CartanFixedInvolution (FourWeyl.point m hm) (FourWeyl.plane m hm)
          (FourWeyl.diagonalCartan m hm) a.val ∧ FourWeyl.SimpleRootsInvariant m hm a.val := by
  obtain ⟨hmgt,hn,c,ho,hN,_⟩ := d.unitary_native_ambient_completion h hH hp m hm hc E he horder
  exact ⟨hmgt,hn,c,ho,hN,FourWeyl.fourth_root_defect m hm hmgt E c ho horder⟩

/-- The actual parameter-four projective model supplies a hyperbolic
coordinate choice, with scalar kernel five and original n = 4 retained. -/
theorem Preparation.unitaryFive_cartan_defect
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
        ∃ a : E.middle, c.middle a=FiveWeyl.rotation U t ht E c ^ 4 ∧
          SourceExtension.CartanFixedInvolution (FiveWeyl.point U t ht) (FiveWeyl.plane U t ht)
            (FiveWeyl.diagonalCartan U t) a.val := by
  obtain ⟨hn,c,ho,hN,_⟩ := d.unitaryFive_native_ambient_completion h hH hp U hc E he horder
  obtain ⟨t,ht⟩ := Theory.SpecificGroups.UnitaryFive.RadicalCentralizers.exists_trace_one
    U.form U.conjugation U.card
  exact ⟨hn,c,ho,hN,t,ht,FiveWeyl.fourth_defect U t ht E c ho horder⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
