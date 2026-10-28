module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.Kernel
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.LowerObstructions.Sp4.ECaseReduction
public import Theory.GroupTheory.SolvableRadical.TwoClosedKernel
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.LocalNormalizerUniqueness
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.Coverage
public import Theory.SpecificGroups.ReeF4.SectionGeometry.CoreFree.LinearRadical.Normality
public import Theory.SpecificGroups.ReeF4.EvenInvolutionGeometry.RadicalIntersection
public import Theory.SpecificGroups.ReeF4.ParabolicSubgroupCores
public import Theory.GroupTheory.GeneralizedFitting.ComponentExclusion


/-!
# Confinement of Ree E2 members

The E2 radical is two-closed. Thus its intersection with the elementary
subgroup equals the intersection with the intrinsic two-core. If this
intersection is nontrivial, the actual Ree octagon theorem puts a conjugate
of K in one of the two proper full root parabolics. The component in the
radical quotient also proves that K is nonsolvable.

The concrete long-root saturation theorem puts a conjugate long-root group
in a root radical whenever their intersection is nontrivial. The full Levi
projections also put the two-core of a nonsolvable parabolic subgroup in
that radical. Together these force the elementary subgroup into O₂(K),
contradicting the E-member commutator clauses. The final application uses
the literal quotient-rank producer in `Kernel`, with no change to the family
or prospective normalizer.

The conditional reductions are retained, and the final theorems discharge
both geometric premises. Both E2 alternatives, the local tau orbit, and
the intrinsic solvable-radical quotient remain in the hypotheses. The
two-residual is never identified with the two-core. The proof needs no
additional SQTK or model-simplicity premise.

Source: Aschbacher--Smith E.1.2 and E.1.14(1), `refs/quasithin.pdf`,
printed pp.209--210 and 214 / PDF pp.220--221 and 225. E.1.14 cites
Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.7,
DOI 10.2307/2374202. The normalizer coverage uses the genuine Ree octagon
and the finite Borel--Tits argument, GLS3 Theorem 3.1.3.
-/

public section

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
open Subgroup ReeF4 ReeF4.Parabolics

/-- The E2 radical and the two-core have the same kernel on the elementary
subgroup. This uses two-closedness of the intrinsic solvable radical. -/
theorem component_inf_radical_eq_inf_core {m : ℕ}
    {A K : Subgroup (Model m)} (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K) :
    A.subgroupOf K ⊓ solvableRadical K = A.subgroupOf K ⊓ pCore 2 K := by
  let := hK.1
  exact inf_solvableRadical_eq_inf_pCore _
    ((IsElementaryAbelian.isPGroup 2 A).comap_of_injective
      K.subtype K.subtype_injective) hc.1

/-- Transfer the literal radical intersection to the intrinsic two-core. -/
theorem component_core_meets_root {m : ℕ}
    {A K : Subgroup (Model m)} (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K)
    (hi : A.subgroupOf K ⊓ solvableRadical K ≠ ⊥) :
    A.subgroupOf K ⊓ pCore 2 K ≠ ⊥ := by
  rwa [← component_inf_radical_eq_inf_core hK hc]

/-- Either E2 alternative supplies a component in the radical quotient,
which excludes solvability of the original subgroup. -/
theorem component_not_solvable {m : ℕ} {A K : Subgroup (Model m)}
    (hc : ECaseComponent (unipotent m) A K) : ¬ Group.IsSolvable K := by
  intro hs
  let := hs
  obtain ⟨_, _, _, L, hL, _⟩ := hc
  exact Theory.GroupTheory.not_isComponent_of_solvable L hL

/-- The genuine octagon normalizer theorem places a conjugate of the E2
member in a proper full root parabolic. No model simplicity is needed. -/
theorem component_parabolic_cover {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K)
    (hi : A.subgroupOf K ⊓ solvableRadical K ≠ ⊥) :
    ∃ (g : Model m) (s : LargeLocalSeeds.Side), parabolic m s ≠ ⊤ ∧
      K.map (MulAut.conj g).toMonoidHom ≤ parabolic m s := by
  have hcore : pCore 2 K ≠ ⊥ := by
    intro hz
    exact component_core_meets_root hK hc hi (by rw [hz, inf_bot_eq])
  have hne : K.pCoreIn 2 ≠ ⊥ := by
    exact fun hz => hcore ((map_eq_bot_iff_of_injective _ K.subtype_injective).mp hz)
  have hn : K ≤ normalizer (K.pCoreIn 2 : Set (Model m)) :=
    K.le_normalizer.trans (normalizer_le_normalizer_characteristic_image K (pCore 2 K))
  obtain ⟨g, s, hp, hcover⟩ := ConverseParabolics.normalizer_cover_proper hm
    (K.pCoreIn 2) hne (isPGroup_pCoreIn 2 K)
  rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic]
    at hp hcover
  exact ⟨g, s, hp, (map_mono hn).trans hcover⟩

private theorem le_core_of_le_radical {m : ℕ} {B J : Subgroup (Model m)}
    (s : LargeLocalSeeds.Side) (hJ : J ≤ parabolic m s)
    (hB : B ≤ radical m s) : B.subgroupOf J ≤ pCore 2 J := by
  let R := (radical m s).subgroupOf J
  have hn : J ≤ normalizer (radical m s : Set (Model m)) :=
    hJ.trans (SectionGeometry.LinearRadical.parabolic_le_radical_normalizer m s)
  let : R.Normal := normal_subgroupOf_of_le_normalizer hn
  have hp : IsPGroup 2 R := (radical_isPGroup m s).comap_of_injective
    J.subtype J.subtype_injective
  exact (subgroupOf_mono J hB).trans (le_sSup ⟨inferInstance, hp⟩)

/-- Reduction to two independent concrete facts: saturation of long-root
intersections with root radicals, and containment of the two-core of a
nonsolvable parabolic subgroup in that radical. These exclude the kernel
intersection, retaining both E2
alternatives and their local tau in the input. -/
theorem component_kernel_false_of_parabolic_geometry {m : ℕ} (hm : 0 < m)
    (hroot : ∀ (B : Subgroup (Model m)), B ∈ rootFamily m →
      ∀ s : LargeLocalSeeds.Side, B ⊓ radical m s ≠ ⊥ → B ≤ radical m s)
    (hcore : ∀ (s : LargeLocalSeeds.Side) (J : Subgroup (Model m)),
      J ≤ parabolic m s → ¬ Group.IsSolvable J → J.pCoreIn 2 ≤ radical m s)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K)
    (hi : A.subgroupOf K ⊓ solvableRadical K ≠ ⊥) : False := by
  obtain ⟨g, s, _, hJ⟩ := component_parabolic_cover hm hK hc hi
  let f := MulAut.conj g
  let B := A.map f.toMonoidHom
  let J := K.map f.toMonoidHom
  have hns : ¬ Group.IsSolvable J := by
    intro hs
    let : Group.IsSolvable (K.map (f : Model m →* Model m)) := hs
    exact component_not_solvable hc
      (Group.isSolvable_of_isSolvable_injective
        (f := (f.subgroupMap K).toMonoidHom) (f.subgroupMap K).injective)
  have hJR : J.pCoreIn 2 ≤ radical m s := hcore s J hJ hns
  have hBR : B ⊓ radical m s ≠ ⊥ := by
    intro hz
    apply component_core_meets_root hK hc hi
    apply (eq_bot_iff_forall _).mpr
    intro x hx
    have hxC : (x : Model m) ∈ K.pCoreIn 2 := ⟨x, hx.2, rfl⟩
    have hxJ : f x.val ∈ J.pCoreIn 2 := by
      rw [← map_pCoreIn_of_injective 2 K f.toMonoidHom f.injective]
      exact mem_map_of_mem _ hxC
    have hxB : f x.val ∈ B := mem_map_of_mem _ hx.1
    have he : f x.val = 1 := mem_bot.mp (hz ▸ (show f x.val ∈ B ⊓ radical m s from
      ⟨hxB, hJR hxJ⟩))
    apply Subtype.ext
    exact f.injective (he.trans (map_one f).symm)
  have hB : B ∈ rootFamily m := rootFamily_conjugationInvariant m A hA g
  have hBC := le_core_of_le_radical s hJ (hroot B hB s hBR)
  exact ValuesEvenClassical.Sp4Lower.member_not_le_core (hK.map_equiv f) hBC

/-- Conditional application to the literal weak-closure normalizer. The
geometric premises are discharged in `component_confined` below. -/
theorem component_confined_of_parabolic_geometry {m : ℕ} (hm : 0 < m)
    (hroot : ∀ (B : Subgroup (Model m)), B ∈ rootFamily m →
      ∀ s : LargeLocalSeeds.Side, B ⊓ radical m s ≠ ⊥ → B ≤ radical m s)
    (hcore : ∀ (s : LargeLocalSeeds.Side) (J : Subgroup (Model m)),
      J ≤ parabolic m s → ¬ Group.IsSolvable J → J.pCoreIn 2 ≤ radical m s)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K)
    (hi : A.subgroupOf K ⊓ solvableRadical K ≠ ⊥) : K ≤ modelNormalizer m :=
  (component_kernel_false_of_parabolic_geometry hm hroot hcore hA hK hc hi).elim

/-- The actual predecessor-rank consumer: `component_kernel_meets_root`
supplies precisely the intersection needed by the conditional geometry. -/
theorem component_predecessor_confined_of_parabolic_geometry {m : ℕ} (hm : 0 < m)
    (hroot : ∀ (B : Subgroup (Model m)), B ∈ rootFamily m →
      ∀ s : LargeLocalSeeds.Side, B ⊓ radical m s ≠ ⊥ → B ≤ radical m s)
    (hcore : ∀ (s : LargeLocalSeeds.Side) (J : Subgroup (Model m)),
      J ≤ parabolic m s → ¬ Group.IsSolvable J → J.pCoreIn 2 ≤ radical m s)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K)
    (hrank : Group.rank ((A.subgroupOf K).map
      (QuotientGroup.mk' (solvableRadical K))) ≤ 2 * m) : K ≤ modelNormalizer m :=
  component_confined_of_parabolic_geometry hm hroot hcore hA hK hc
    (component_kernel_meets_root hA hK.2.2.1 hrank)

/-- No E2 member containing a conjugate long-root group has a nontrivial
root intersection with its intrinsic solvable radical. The concrete radical
saturation and subgroup two-core theorems discharge both geometric premises. -/
theorem component_kernel_false {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K)
    (hi : A.subgroupOf K ⊓ solvableRadical K ≠ ⊥) : False := by
  refine component_kernel_false_of_parabolic_geometry hm ?_
    (ParabolicSubgroupCores.pCoreIn_le_radical hm) hA hK hc hi
  rintro B ⟨g, rfl⟩ s hB
  exact EvenInvolutionGeometry.RadicalIntersection.longRootGroup_conj_le_radical_of_inf_ne_bot
    m g s hB

/-- E2 kernel confinement for the actual long-root family and weak-closure
normalizer. This supplies the component branch of the positive Ree lower
obstruction with no remaining geometric premise. -/
theorem component_confined {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K)
    (hi : A.subgroupOf K ⊓ solvableRadical K ≠ ⊥) : K ≤ modelNormalizer m :=
  (component_kernel_false hm hA hK hc hi).elim

/-- The literal quotient-rank bound supplies the radical intersection via
`component_kernel_meets_root`, completing the E2 predecessor application. -/
theorem component_predecessor_confined {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMember (unipotent m) A K)
    (hc : ECaseComponent (unipotent m) A K)
    (hrank : Group.rank ((A.subgroupOf K).map
      (QuotientGroup.mk' (solvableRadical K))) ≤ 2 * m) : K ≤ modelNormalizer m :=
  component_confined hm hA hK hc (component_kernel_meets_root hA hK.2.2.1 hrank)

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
