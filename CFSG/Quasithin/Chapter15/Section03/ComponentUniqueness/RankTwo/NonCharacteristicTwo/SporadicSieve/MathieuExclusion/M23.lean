module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion.Seed
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankTwo.Parabolics.BinaryRecognition.InnerGeometry
public import CFSG.Quasithin.MainConverse.MathieuLocal.M23Even
public import Theory.Mathieu.M23.Properties.Automorphisms
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.Coverage
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.HeptadSolvable
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.TripleSolvable

/-!
# The M₂₃ rank-two exclusion

Every automorphism of the native M₂₃ is inner, so the full component
centralizer quotient is M₂₃. Even characteristic and the source's maximality
subject to F*=O₂ make its local subgroup maximal two-local. The full
S₃ × S₃ Frattini shadow supplies a solvable normal seed with order divisible
by nine. Exhaustive coverage places the local subgroup in the actual heptad
or triple stabilizer, neither of which admits such a seed.

The conditional reductions expose these two local calculations. The final
`not_m23` theorem supplies both from the native permutation geometry, with
no additional hypotheses on the component setup.

Source: Aschbacher--Smith, 1.1.5(3f), printed pp.501--503, and 15.3.41--42,
printed p.1138; GLS3, Table 5.3d, printed p.265.
-/

public section
open Subgroup Theory.GroupTheory Sporadic.Mathieu
namespace CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
open Parabolics.BinaryRecognition.InnerGeometry
open Sporadic.Mathieu.M23Geometry.SylowTwoLocals

private theorem normal_solvable_nine_of_local_equiv
    {H A : Type*} [Group H] [Finite H] [Group A]
    {M Y S : Subgroup H} (d : LocalConfiguration (⊤ : Subgroup H) M Y S)
    (e : M ≃* A) :
    ∃ D : Subgroup A, D.Normal ∧ Group.IsSolvable D ∧ 9 ∣ Nat.card D := by
  have hYM : Y ≤ M := d.yplus_le.trans inf_le_left
  let : Group.IsSolvable (Y ⊔ S : Subgroup H) := shadow_join_solvable d.shadow
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := inclusion (show Y ≤ Y ⊔ S from le_sup_left)) (inclusion_injective _)
  let a := subgroupOfEquivOfLe hYM
  let : Group.IsSolvable (Y.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective (f := a.toMonoidHom) a.injective
  let D := (Y.subgroupOf M).map e.toMonoidHom
  refine ⟨D, (normal_y_subgroupOf d).map e.toMonoidHom e.surjective,
    Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective _), ?_⟩
  have hc : Nat.card D = Nat.card Y := by
    rw [card_map_of_injective e.injective]
    exact Nat.card_congr a.toEquiv
  rw [hc]
  exact nine_dvd_card_y d

/-- Once the two native local calculations are supplied, the entire local
configuration is impossible. Relative normality, the Frattini shadow and
maximality subject to F*=O₂ are used with their source meanings. -/
theorem m23_no_localConfiguration_of_cover
    (hcover : ∀ (T : Sylow 2 M23) (N : Subgroup M23),
      IsMaximalTwoLocal N → (T : Subgroup M23) ≤ N →
      ∃ i : Fin 2, Nonempty (N ≃* candidate i))
    (htriple : ∀ D : Subgroup tripleStabilizer,
      D.Normal → Group.IsSolvable D → ¬ 9 ∣ Nat.card D)
    {H : Type*} [Group H] [Finite H]
    (e : H ≃* M23) {M Y S : Subgroup H}
    (d : LocalConfiguration (⊤ : Subgroup H) M Y S) : False := by
  obtain ⟨P, hP⟩ := d.sylow
  let T := P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨J, hMJ, hJ⟩ := Finite.exists_le_maximal d.twoLocal
  have hcJ : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    apply (Theory.Quasithin.centralizer_pCore_le_iff 2 (e.subgroupMap J)).mpr
    exact MainConverse.m23_twoLocal_characteristicTwo T (J.map e.toMonoidHom)
      (Theory.Quasithin.isTwoLocal_map e hJ.1)
      (map_mono ((hP.symm ▸ d.sylow_le).trans hMJ))
  have hM : IsMaximalTwoLocal M :=
    (d.maximal J hMJ (generalizedFitting_eq_pCore_of_selfCentralizing 2 hcJ)) ▸ hJ
  obtain ⟨i, ⟨a⟩⟩ := hcover T (M.map e.toMonoidHom)
    (Theory.Quasithin.isMaximalTwoLocal_map e hM)
    (map_mono (hP.symm ▸ d.sylow_le))
  obtain ⟨D, hD, hsD, h9⟩ :=
    normal_solvable_nine_of_local_equiv d ((e.subgroupMap M).trans a)
  fin_cases i
  · exact @heptad_normal_solvable_not_nine D hD hsD h9
  · exact htriple D hD hsD h9

/-- Conditional assembly for the actual component quotient. Innerness is
discharged here; only exhaustive local coverage and the triple-stabilizer
normal-seed calculation are outstanding. -/
theorem not_m23_of_local_cover
    (hcover : ∀ (T : Sylow 2 M23) (N : Subgroup M23),
      IsMaximalTwoLocal N → (T : Subgroup M23) ≤ N →
      ∃ i : Fin 2, Nonempty (N ≃* candidate i))
    (htriple : ∀ D : Subgroup tripleStabilizer,
      D.Normal → Group.IsSolvable D → ¬ 9 ∣ Nat.card D)
    {G : Type*} [Group G] [Finite G]
    {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* M23) : False := by
  have ht : componentImage I L L = ⊤ := by
    rw [← modelAction_comap_inner d e]
    have hi : MulAut.innerSubgroup M23 = ⊤ :=
      MonoidHom.range_eq_top.mpr m23_conj_surjective
    rw [hi, comap_top]
  have dc := d.quotient_local
  rw [ht] at dc
  exact m23_no_localConfiguration_of_cover hcover htriple
    (wholeModelOfInner d e m23_conj_surjective) dc

/-- The native M₂₃ cannot occur as the component quotient in 15.3.42.
The exhaustive local coverage and both solvable-normal-seed obstructions
discharge the M₂₃ case of the inspection in 15.3.41(2). -/
theorem not_m23 {G : Type*} [Group G] [Finite G]
    {I L M Y S : Subgroup G} [(L.subgroupOf I).Normal]
    (d : ComponentSetup I L M Y S) (e : L ⧸ pCore 2 L ≃* M23) : False := by
  exact not_m23_of_local_cover sylow_maximal_twoLocal_coverage
    (fun D hD hsD => @triple_normal_solvable_not_nine D hD hsD) d e

end CFSG.Quasithin.Chapter15.Section03.RankTwo.NonCharacteristicTwo.SporadicSieve.MathieuExclusion
