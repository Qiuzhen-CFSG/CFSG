module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.Kernel
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.OddConfinement.SuzukiParabolic.Core
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.RadicalIntersection

/-!
# The Suzuki-parabolic root-rank calculation

Use the genuine full-parabolic projection to Suzuki matrices times the field
torus. Its kernel is the root radical and is a two-group. If the image of K
has nontrivial two-core, the Suzuki ovoid geometry puts every two-subgroup in
that core. Otherwise the intrinsic two-core of K is precisely the projection
kernel. Root-radical saturation therefore makes the literal root quotient
image either trivial or isomorphic to the whole root member, whose rank is
at least the odd field degree.

The matrix-root saturation theorem in
`EvenInvolutionGeometry.RadicalIntersection` discharges the geometric premise
for every literal conjugate defining `rootFamily`. This gives the unconditional
Suzuki-parabolic rank-one exclusion, including q = 8. The final E.1.14(1)
assembly also needs the separate linear-parabolic and component branches.

Source: Aschbacher--Smith E.1.14(1), printed p.214 of `refs/quasithin.pdf`,
citing Aschbacher (1982), Lemma 4.7, DOI 10.2307/2374202. The projection uses
the full parabolics of GLS3 §§2.3--2.6, with the complementary torus retained.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
open Subgroup ReeF4
open ReeF4.MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry

private theorem rank_image_core_eq_zero {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hB : B ≤ pCore 2 G) :
    Group.rank (B.map (QuotientGroup.mk' (pCore 2 G))) = 0 := by
  have hz : B.map (QuotientGroup.mk' (pCore 2 G)) = ⊥ := by
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  rw [hz]
  exact Group.rank_eq_zero _

private theorem rank_image_core_eq_rank {G : Type*} [Group G] [Finite G]
    (B : Subgroup G) (hB : Disjoint B (pCore 2 G)) :
    Group.rank (B.map (QuotientGroup.mk' (pCore 2 G))) = Group.rank B := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hinj : Function.Injective (q.subgroupMap B) := by
    apply (injective_iff_map_eq_one _).mpr
    intro x hx
    have hxcore : (x : G) ∈ pCore 2 G :=
      (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
    exact Subtype.ext ((Subgroup.disjoint_def.mp hB) x.property hxcore)
  exact (Group.rank_congr (MulEquiv.ofBijective (q.subgroupMap B)
    ⟨hinj, q.subgroupMap_surjective B⟩)).symm

/-- The intrinsic core quotient either kills the full root member or preserves
its entire rank, provided its intersection with the actual radical is saturated.
The hypothesis here is geometric; it asserts no quotient-rank conclusion. -/
theorem suzuki_parabolic_root_rank_alternatives_of_radical_dichotomy
    {m : ℕ} (hm : 0 < m) {A K : Subgroup (Model m)}
    (hA : A ∈ rootFamily m) (hAK : A ≤ K)
    (hKP : K ≤ Parabolics.parabolic m .suzuki)
    (hroot : A ≤ Parabolics.radical m .suzuki ∨
      Disjoint A (Parabolics.radical m .suzuki)) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = 0 ∨
      Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) =
        Group.rank A := by
  let B := A.subgroupOf K
  have hKP' : K ≤ ConverseParabolics.parabolic m .suzuki := by
    rwa [parabolic_eq_rootParabolic]
  let f := (ConverseParabolics.suzukiProjection (show 1 ≤ m by omega)).comp
    (inclusion hKP')
  have hk : IsPGroup 2 f.ker :=
    (ConverseParabolics.suzukiProjection_ker_isPGroup (show 1 ≤ m by omega)).comap_of_injective
      (inclusion hKP') (inclusion_injective hKP')
  have hker : f.ker = (Parabolics.radical m .suzuki).subgroupOf K := by
    ext x
    change inclusion hKP' x ∈ (ConverseParabolics.suzukiProjection (show 1 ≤ m by omega)).ker ↔ _
    rw [ConverseParabolics.suzukiProjection_ker]
    change (x : Model m) ∈ ConverseParabolics.radical m .suzuki ↔ _
    rw [ConverseParabolics.suzuki_radical_eq_rootRadical]
    rfl
  have hkc : f.ker ≤ pCore 2 K := le_sSup ⟨inferInstance, hk⟩
  rcases hroot with hroot | hroot
  · left
    apply rank_image_core_eq_zero
    exact (show B ≤ f.ker by rw [hker]; exact fun x hx => hroot hx).trans hkc
  have hk' : IsPGroup 2 f.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  have hc := f.rangeRestrict.comap_pCore_of_ker_isPGroup f.rangeRestrict_surjective hk'
  by_cases hz : pCore 2 f.range = ⊥
  · right
    have hcore : f.ker = pCore 2 K := by
      simpa only [hz, MonoidHom.comap_bot, MonoidHom.ker_rangeRestrict] using hc
    have hdis : Disjoint B (pCore 2 K) := by
      rw [← hcore, hker]
      apply Subgroup.disjoint_def.mpr
      intro x hx hr
      exact Subtype.ext (Subgroup.disjoint_def.mp hroot hx hr)
    exact (rank_image_core_eq_rank B hdis).trans
      (Group.rank_congr (subgroupOfEquivOfLe hAK))
  · left
    let := (rootFamily_elementary m).1 A hA
    have hB : IsPGroup 2 B := (IsElementaryAbelian.isPGroup 2 A).comap_subtype
    have himage := suzukiLevi_twoSubgroup_le_core hm f.range hz
      (B.map f.rangeRestrict) (hB.map f.rangeRestrict)
    apply rank_image_core_eq_zero
    rw [← hc]
    exact map_le_iff_le_comap.mp himage

/-- The local Suzuki rank-one exclusion follows from root-radical saturation.
All intrinsic-core and complementary-torus calculations are discharged here. -/
theorem suzuki_parabolic_root_rank_ne_one_of_radical_saturation
    {m : ℕ} (hm : 0 < m) {A K : Subgroup (Model m)}
    (hA : A ∈ rootFamily m) (hAK : A ≤ K)
    (hKP : K ≤ Parabolics.parabolic m .suzuki)
    (hroot : A ⊓ Parabolics.radical m .suzuki ≠ ⊥ →
      A ≤ Parabolics.radical m .suzuki) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1 := by
  have hd : A ≤ Parabolics.radical m .suzuki ∨
      Disjoint A (Parabolics.radical m .suzuki) := by
    by_cases hz : A ⊓ Parabolics.radical m .suzuki = ⊥
    · exact Or.inr (disjoint_iff.mpr hz)
    · exact Or.inl (hroot hz)
  have hr := suzuki_parabolic_root_rank_alternatives_of_radical_dichotomy hm hA hAK hKP hd
  have hl := fieldDegree_le_rank hA
  omega

/-- A full long-root conjugate inside the actual Suzuki parabolic cannot have
rank one in the intrinsic two-core quotient of any intermediate subgroup.
The literal matrix-root saturation theorem supplies the geometric premise;
no simplicity or E-member hypothesis is required. This discharges the Suzuki
premise of `not_odd_of_parabolic_rank_exclusions` in `OddConfinement`. -/
theorem suzuki_parabolic_root_rank_ne_one
    {m : ℕ} (hm : 0 < m) {A K : Subgroup (Model m)}
    (hA : A ∈ rootFamily m) (hAK : A ≤ K)
    (hKP : K ≤ Parabolics.parabolic m .suzuki) :
    Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) ≠ 1 := by
  apply suzuki_parabolic_root_rank_ne_one_of_radical_saturation hm hA hAK hKP
  obtain ⟨g, rfl⟩ := hA
  exact EvenInvolutionGeometry.RadicalIntersection.longRootGroup_conj_le_radical_of_inf_ne_bot
    m g .suzuki

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
