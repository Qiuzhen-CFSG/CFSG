module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.Seed
public import Theory.Mathieu.M12.SylowOvergroups.RankTwoCoverage

/-!
# Exclusion of M₁₂ from the rank-two component configuration

The actual image D of Y₊ in L/O₂(L) is solvable, has order divisible by nine,
and is normalized by a Sylow two-subgroup of the component. Exhaustive native
Sylow-overgroup coverage forces N(D) to be all of M₁₂: every proper such
overgroup has order dividing 192. Simplicity, inherited from the source's
component image, contradicts the nontrivial solvable normal subgroup D.

This argument takes place inside the component and therefore covers both
inner and outer component actions. It imposes no splitting convention on the
automorphism extension and retains the entire `ComponentSetup` interface,
including all `LocalConfiguration` clauses and its literal Frattini quotient.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), 1.1.5(3f)
and 15.3.41--42, printed pp.502 and 1138; GLS3 Table 5.3b.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion

/-- The actual M₁₂ component is impossible, for every inner or outer action. -/
theorem not_m12 {G : Type*} [Group G] [Finite G]
    {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* M12) : False := by
  let D := seed (Y := Y) e
  have h9 : 9 ∣ Nat.card D := seed_nine_dvd d e
  have hN : normalizer (D : Set M12) = ⊤ :=
    M12SmallPair.SylowOvergroups.eq_top_of_nine_dvd _
      (h9.trans (card_dvd_of_le D.le_normalizer)) (seed_sylow d e)
  have hn : D.Normal := normalizer_eq_top_iff.mp hN
  let : IsSimpleGroup (componentImage I L L) := d.simple_image
  let : IsSimpleGroup M12 := (componentModel d e).symm.isSimpleGroup
  rcases hn.eq_bot_or_eq_top with hbot | htop
  · rw [hbot, Subgroup.card_bot] at h9
    norm_num at h9
  · let : Group.IsSolvable D := seed_solvable d e
    let f := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    let : Group.IsSolvable M12 :=
      Group.isSolvable_of_surjective (f := f.toMonoidHom) f.surjective
    have hc := IsSimpleGroup.comm_iff_isSolvable.mpr
      (inferInstance : Group.IsSolvable M12)
    have h := congrArg Subtype.val (hc
      (M12SmallPair.SylowOvergroups.standardGenerator 0)
      (M12SmallPair.SylowOvergroups.standardGenerator 1))
    exact (by decide +kernel : m12GeneratorA * m12GeneratorB ≠
      m12GeneratorB * m12GeneratorA) h

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
