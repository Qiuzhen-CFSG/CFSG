module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.Placement.LocalOrbit
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups
public import Theory.GroupTheory.SylowNormalizerCommutingFamily

/-!
# Placement of the actual Suzuki Borel

A nonidentity root element has centralizer inside the root group. Since the
root group is the two-core of its normalizer, the standard Borel has
characteristic two. Sylow conjugacy and the supplied matrix equivalence
transport this property to the prescribed ambient Borel.

The Suzuki group has order prime to three. Its Borel is solvable, so every
finite power is solvable and has order prime to three. No subgroup of such
a power is short: a quasisimple quotient is incompatible with solvability,
and a quotient of order three is incompatible with the order. The common
component-orbit argument therefore excludes every relative chi-zero block
in ⟨B,Q⟩, including when Q permutes components. The exact E.6.7 input then
places B in M. No tailored block-exclusion or placement premise remains.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.7–8,
printed pp.246–248 (PDF pp.257–259); the concrete Suzuki facts are
Huppert–Blackburn III, XI.3.3 and XI.3.6.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
open CFSG.Quasithin.ChapterF.Source BenderSuzuki.MatrixGroups
open InvariantSubspaces.BlockSelection
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem not_short_of_solvable_three_free {X : Type*} [Group X] [Finite X]
    [Group.IsSolvable X] (hthree : ¬ 3 ∣ Nat.card X) : ¬ ChapterC.IsShort X := by
  intro hx
  rcases hx.quotient with hq | hq
  · let _ := hq
    let _ : IsSimpleGroup ((X ⧸ pCore 2 X) ⧸ center (X ⧸ pCore 2 X)) := IsQuasisimple.simple
    let _ : Nontrivial (X ⧸ pCore 2 X) :=
      (QuotientGroup.mk'_surjective (center (X ⧸ pCore 2 X))).nontrivial
    exact Group.IsPerfect.not_isSolvable (X ⧸ pCore 2 X) inferInstance
  · exact hthree (hq ▸ (pCore 2 X).card_quotient_dvd_card)

/-- The genuine Suzuki Borel has no short subnormal subgroup in any finite
power. Its order is prime to three, and the power remains solvable. -/
theorem suzuki_borel_power_noShort {m : ℕ} (hm : 1 ≤ m)
    (e : L ≃* SuzukiMatrixGroup m) (S : Sylow 2 L)
    (k : ℕ) (X : Subgroup (Fin k → sylowBorel S)) : ¬ ChapterC.IsShort X := by
  have hmodel : Model L (2 * m + 1) := .suzuki m hm rfl ⟨e⟩
  let _ := (hmodel.sylowFacts S).solvable
  let eB := (normalizer (S : Set L)).equivMapOfInjective L.subtype L.subtype_injective
  let _ : Group.IsSolvable (sylowBorel S) :=
    Group.isSolvable_of_isSolvable_injective (f := eB.symm.toMonoidHom) eB.symm.injective
  let _ := Group.isSolvable_finite_pi (fun _ : Fin k => sylowBorel S)
  have hthreeL : ¬ 3 ∣ Nat.card L := by
    rw [Nat.card_congr e.toEquiv]
    exact (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).2
  have hthreeB : ¬ 3 ∣ Nat.card (sylowBorel S) :=
    fun hd => hthreeL (hd.trans (card_dvd_of_le (sylowBorel_le S)))
  apply not_short_of_solvable_three_free
  intro hd
  have hp := hd.trans X.card_subgroup_dvd_card
  rw [Nat.card_fun] at hp
  exact hthreeB (Nat.prime_three.dvd_of_dvd_pow hp)

private theorem root_centralizer_le {m : ℕ} (hm : 1 ≤ m) :
    centralizer (SuzukiRootSubgroup m : Set (SuzukiMatrixGroup m)) ≤ SuzukiRootSubgroup m := by
  have hne : SuzukiRootSubgroup m ≠ ⊥ := by
    intro he
    have hc := suzukiRootSubgroup_card m hm
    rw [he, card_bot] at hc
    have hq : 1 < 2 ^ (2 * m + 1) := one_lt_pow₀ (by decide) (by omega)
    nlinarith
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr x.property)).trans
    (suzukiRootSubgroup_centralizer_le m hm x.property
      (fun he => hx1 (Subtype.ext he)))

private theorem suzuki_borel_characteristicTwo {m : ℕ} (hm : 1 ≤ m) :
    HasCharacteristicTwo (SuzukiBorelSubgroup m) := by
  obtain ⟨S, hS⟩ := suzukiRootSubgroup_isSylow m hm
  have hcore : (SuzukiBorelSubgroup m).pCoreIn 2 = SuzukiRootSubgroup m := by
    have he := twoCore_sylow_normalizer S
    change (normalizer (S : Set (SuzukiMatrixGroup m))).pCoreIn 2 = (S : Subgroup _) at he
    change (normalizer ((S : Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m))).pCoreIn 2 = _ at he
    rw [hS, suzukiRootSubgroup_normalizer m hm] at he
    exact he
  apply (inf_centralizer_pCoreIn_le_iff 2 _).mp
  rw [hcore]
  exact inf_le_right.trans (root_centralizer_le hm)

/-- Characteristic two of the actual embedded Suzuki Sylow normalizer. -/
theorem suzuki_sylowBorel_characteristicTwo {m : ℕ} (hm : 1 ≤ m)
    (e : L ≃* SuzukiMatrixGroup m) (S : Sylow 2 L) :
    HasCharacteristicTwo (sylowBorel S) := by
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨g, hg⟩ := suzuki_sylow_normalizer_eq_conjugate_borel m R
  have hn : (normalizer (S : Set L)).map e.toMonoidHom =
      normalizer (R : Set (SuzukiMatrixGroup m)) :=
    map_normalizer_eq_of_bijective _ e.bijective
  let eb := ((normalizer (S : Set L)).equivMapOfInjective L.subtype L.subtype_injective).symm
  let ee := ((normalizer (S : Set L)).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr hn)
  let eg := ((SuzukiBorelSubgroup m).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hg.symm)
  exact (Theory.Quasithin.centralizer_pCore_le_iff 2 (eb.trans (ee.trans eg.symm))).mpr
    (suzuki_borel_characteristicTwo hm)

/-- Suzuki placement, with every intrinsic premise discharged and only the
exact universally quantified earlier E.6.7 statement explicit. -/
theorem suzuki_sylowBorel_le
    (h67 : E67Input T M V) (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ≃* SuzukiMatrixGroup m) (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype = L ⊓ sylowCentralizer (T : Subgroup G) V) :
    sylowBorel S ≤ M := by
  let _ : IsSimpleGroup L := e.isSimpleGroup_congr.mpr
    (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
  let _ := hL.2.2
  let _ : IsQuasisimple L := IsQuasisimple.of_mulEquiv (subgroupOfEquivOfLe hL.1)
  have hz : center L = ⊥ := by
    rcases (inferInstance : (center L).Normal).eq_bot_or_eq_top with hz | hz
    · exact hz
    · exact (Group.IsPerfect.not_isMulCommutative L (center_eq_top_iff.mp hz)).elim
  exact sylowBorel_le_of_intrinsic h67 hU hL hz S hS
    (suzuki_sylowBorel_characteristicTwo hm e S)
    (fun k X _ => suzuki_borel_power_noShort hm e S k X)

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
