module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors.Model
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors.Conjugacy
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors.Transport
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors.Reference
public import Theory.SpecificGroups.OddThreeRank

/-!
# Inner-actor placement in the PSL₃(3) graph extension

An inner elementary actor of rank greater than one lifts faithfully to
SL₃(3). The degree-three rank bound makes its order four. All such matrix
four-groups are conjugate, and Sylow conjugacy transports one reference
configuration to every requested Sylow subgroup, preserving the whole actor
and all six geometric clauses.

`InnerActors.exists_inner_reference` constructs the finite reference
configuration. Applying the transport reduction to this configuration proves
`centralizerPlacement_of_inner` with every geometric premise discharged.
This supplies the inner branch of
`ConcreteGeometry.exists_localGeometry_of_inner_outer`.

Source: Aschbacher–Smith E.1.2, E.1.5 and E.1.14(7), printed pp.209–210,
214, and Asc82a Lemma 4.11.
-/

public section
open Subgroup Theory.GroupTheory
open Matrix.PSL3Three Matrix.PSL3Three.GraphLocalQuotients
open Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
namespace InnerActors

/-- The whole inner actor lifts faithfully to an elementary four-subgroup
of the actual determinant-one matrix group. -/
theorem inner_actor_lift (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hrank : 1 < Group.rank A) (hinner : A ≤ innerPart (ZMod 3)) :
    ∃ D : Subgroup SL, IsElementaryAbelian 2 D ∧ Nat.card D = 4 ∧ D.map inner = A := by
  let D := A.comap inner
  have hmap : D.map inner = A := map_comap_eq_self (range_inner ▸ hinner)
  let e : D ≃* A := (D.equivMapOfInjective inner inner_injective).trans
    (MulEquiv.subgroupCongr hmap)
  let _ : IsElementaryAbelian 2 A := hA
  let _ : IsElementaryAbelian 2 D := {
    toIsMulCommutative := A.comap_injective_isMulCommutative inner_injective
    exponent_dvd_p := by
      apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
      intro x
      apply Subtype.ext
      apply inner_injective
      change inner ((x : SL) ^ 2) = inner 1
      rw [map_pow, map_one]
      exact elemPow_eq_one_of_isElementaryAbelian (inner x.val) x.property }
  have hbound : Nat.card D ≤ 4 :=
    Theory.SpecificGroups.OddThreeRank.elementary_card_le_four
      (Matrix.SpecialLinearGroup.toGL.comp D.subtype)
      (Matrix.SpecialLinearGroup.toGL_injective.comp D.subtype_injective)
      (by decide)
      (fun x => Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 D) x)
      (fun x => Matrix.SpecialLinearGroup.coeToGL_det x.val)
  have hlarge : ¬ Nat.card D ≤ 2 := by
    intro h
    have hr : Group.rank D ≤ 1 := IsElementaryAbelian.rank_le_of_card_le
      (p := 2) D (by simpa using h)
    rw [Group.rank_congr e] at hr
    omega
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 D).exists_card_eq
  have hnle : n ≤ 2 := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp
    (by simpa only [hn] using hbound)
  have hnge : 2 ≤ n := by
    by_contra h
    have hh : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by decide) (by omega)
    exact hlarge (by simpa only [hn, pow_one] using hh)
  refine ⟨D, inferInstance, ?_, hmap⟩
  rw [hn, show n = 2 by omega]
  norm_num

/-- Every qualifying inner actor is conjugate to any chosen matrix four-group.
The conjugator is an actual element of the graph extension. -/
theorem inner_actor_conjugate (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hrank : 1 < Group.rank A) (hinner : A ≤ innerPart (ZMod 3))
    (D : Subgroup SL) (hD : IsElementaryAbelian 2 D) (hcard : Nat.card D = 4) :
    ∃ g : G, A.map (MulAut.conj g).toMonoidHom = D.map inner := by
  obtain ⟨E, hE, hEc, hEA⟩ := inner_actor_lift A hA hrank hinner
  let _ : IsElementaryAbelian 2 E := hE
  let _ : IsElementaryAbelian 2 D := hD
  obtain ⟨s, hs⟩ := four_conjugate E D hEc hcard
  refine ⟨inner s, ?_⟩
  rw [← hEA, ← hs, map_map, map_map]
  apply congrArg (fun f : SL →* G => E.map f)
  apply MonoidHom.ext
  intro x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    map_mul, map_inv]

end InnerActors
open InnerActors

/-- One concrete matrix four-group configuration discharges the inner-actor
branch for every Sylow subgroup. The reference configuration is an explicit
input to this transport reduction. -/
theorem centralizerPlacement_of_inner_seed
    (R : Sylow 2 G) (D : Subgroup SL) (c : G)
    (hD : IsElementaryAbelian 2 D) (hDc : Nat.card D = 4)
    (hDR : D.map inner ≤ (R : Subgroup G))
    (hDK : D.map inner ≤ localSubgroup c)
    (hcent : (R : Subgroup G) ⊓ centralizer (D.map inner : Set G) ≤ localSubgroup c)
    (hcard : Nat.card ((R : Subgroup G).subgroupOf (localSubgroup c)) = 16)
    (hcore : ¬ (D.map inner).subgroupOf (localSubgroup c) ≤ pCore 2 (localSubgroup c))
    (hgen : (R : Subgroup G) ⊔ localSubgroup c = ⊤)
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hrank : 1 < Group.rank A) (hinner : A ≤ innerPart (ZMod 3)) :
    CentralizerPlacement T A := by
  have hseed : CentralizerPlacement R (D.map inner) := by
    refine ⟨1, c, ?_⟩
    have h1 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    simpa only [h1, Subgroup.map_id] using And.intro hDR (And.intro hDK (And.intro hcent
      (And.intro hcard (And.intro hcore hgen))))
  apply placement_at_any_sylow R (D.map inner) hseed T A
  intro s
  obtain ⟨g, hg⟩ := inner_actor_conjugate A hA hrank hinner D hD hDc
  refine ⟨s * g, ?_⟩
  rw [← hg, map_map]
  apply congrArg (fun f : G →* G => A.map f)
  apply MonoidHom.ext
  intro x
  change (s * g) * x * (s * g)⁻¹ = s * (g * x * g⁻¹) * s⁻¹
  group

/-- Every inner elementary actor of rank greater than one has a concrete
graph-centralizer placement. This discharges the inner-actor premise of
`ConcreteGeometry.exists_localGeometry_of_inner_outer`, retaining the whole
actor and every intrinsic local-group clause. -/
theorem centralizerPlacement_of_inner
    (T : Sylow 2 G) (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (_hAT : A ≤ (T : Subgroup G)) (hrank : 1 < Group.rank A)
    (hinner : A ≤ innerPart (ZMod 3)) : CentralizerPlacement T A := by
  obtain ⟨R, D, c, hD, hDc, hDR, hDK, hcent, hcard, hcore, hgen⟩ :=
    exists_inner_reference
  exact centralizerPlacement_of_inner_seed R D c hD hDc hDR hDK hcent hcard
    hcore hgen T A hA hrank hinner

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry
