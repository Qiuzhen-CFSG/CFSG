module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Basic
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.CentralHall.Nonlinear.HallGeometry.Product
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.Borel
public import Theory.SpecificGroups.SL2.ExchangedPairBorel
public import Theory.GroupTheory.SylowLocalCore

/-!
# Borel placement for the original nonlinear SL₂ Hall rows

A proper Sylow overgroup in the exchanged component pair is solvable. Apply
this to the actual HStar intersection with the local join and project to the
original quotient SL₂ × SL₂. Both solvable projections lie in the original
Sylow normalizers, so H intersect L₀ normalizes T intersect L₀. This normal
Sylow is characteristic in H intersect L₀; consequently H intersect M and
the prescribed Hall subgroup normalize it as well.

The odd part of the original Hall subgroup lying in L₀ therefore lies in
the two-residual of N_{L₀}(T intersect L₀), the literal source B₀. This
supplies the common Borel placement for both the natural and orthogonal
rows. Removal of the outer field factor is a separate source obligation.

Source: Aschbacher--Smith, the centralizing-Z branch of 10.2.3, printed p.745,
using the rank-one Sylow-normalizer calculation. The component marking and
all two-cores remain those of the original fundamental setup.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  {F : Type*} [Field F] [Finite F] [CharP F 2]
include D

/-- The literal intersection with the original Sylow is Sylow in the orbit. -/
theorem source_orbit_sylow_intersection :
    ∃ S : Sylow 2 (localOrbit T L),
      (S : Subgroup (localOrbit T L)) = (T : Subgroup G).subgroupOf (localOrbit T L) := by
  let R := localOrbit T L
  let M := D.maximalLocal
  let : (R.subgroupOf M).Normal := normal_subgroupOf_of_le_normalizer le_rfl
  obtain ⟨P,hP⟩ := (T.subtype (le_normalizer_componentOrbit L T)).exists_subgroupOf_eq_of_normal
    (R.subgroupOf M)
  let a := subgroupOfEquivOfLe R.le_normalizer
  refine ⟨P.mapSurjective (f := a.toMonoidHom) a.surjective,?_⟩
  change (P : Subgroup (R.subgroupOf M)).map a.toMonoidHom = _
  rw [hP]
  ext r
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact hx
  · intro hr
    exact ⟨⟨⟨r,R.le_normalizer r.property⟩,r.property⟩,hr,rfl⟩

/-- Proper Sylow overgroups in the actual local join are solvable. -/
theorem source_sl2_proper_overgroup_solvable
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (P : Subgroup G) (hTP : (T : Subgroup G) ≤ P) (hP : P < localJoin T L) :
    Group.IsSolvable P := by
  let := D.quasisimple
  let : IsQuasisimple SL(2,F) := IsQuasisimple.of_mulEquiv e
  let J := localJoin T L
  have hLJ : L ≤ J := (le_componentOrbit L T).trans le_sup_left
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  let S := T.subtype hTJ
  let A := L.subgroupOf J
  have hA : A.IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a := subgroupOfEquivOfLe hLJ
  let eA := (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans e
  have hgen : A ⊔ (S : Subgroup J) = ⊤ := by
    change L.subgroupOf J ⊔ (T : Subgroup G).subgroupOf J = ⊤
    rw [←subgroupOf_sup hLJ hTJ]
    have hh : L ⊔ (T : Subgroup G) = J := (componentOrbit_sup L (T : Subgroup G)).symm
    rw [hh,subgroupOf_self]
  have hi : (normalizer (A : Set J)).index = 2 := by
    change (normalizer (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔
      (T : Subgroup G)) : Set (componentOrbit L (T : Subgroup G) ⊔
      (T : Subgroup G) : Subgroup G))).index = 2
    rw [componentOrbit_sup]
    exact source_nonnormal_normalizer_index D.simpleQTKE D.maximal.1 hn
  have hSP : (S : Subgroup J) ≤ P.subgroupOf J := fun _ hx => hTP hx
  have hPne : P.subgroupOf J ≠ ⊤ := fun he => hP.not_ge (subgroupOf_eq_top.mp he)
  let : Group.IsSolvable (P.subgroupOf J) :=
    Matrix.SpecialLinearGroup.ExchangedPair.component_pair_proper_overgroup_solvable
      S A hA eA hi hgen (P.subgroupOf J) hSP hPne
  exact Group.isSolvable_of_surjective
    (f := (subgroupOfEquivOfLe hP.le).toMonoidHom) (subgroupOfEquivOfLe hP.le).surjective

/-- The original orbit intersection normalizes its actual Sylow subgroup. -/
theorem source_sl2_hstar_orbit_intersection_normalizes_sylow
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ localOrbit T L ≤ normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G) := by
  let := D.quasisimple
  let : IsQuasisimple SL(2,F) := IsQuasisimple.of_mulEquiv e
  let : IsSimpleGroup (SL(2,F) ⧸ center SL(2,F)) := IsQuasisimple.simple
  let : IsSimpleGroup SL(2,F) :=
    ((QuotientGroup.quotientMulEquivOfEq
      (Atlas.RankOneFieldAutomorphisms.sl_center_eq_bot (F := F))).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup
  let R := localOrbit T L
  let P := H ⊓ localJoin T L
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  obtain ⟨q,hq,hk,_,_⟩ := marked_pair_projection D e hn ht htn
  let : Group.IsSolvable P := source_sl2_proper_overgroup_solvable D e hn P
    (le_inf hH.1.1.2 le_sup_right) (source_hstar_inf_localJoin_lt D hH)
  let U := P.subgroupOf R
  let i : U →* P := R.subtype.subgroupComap P
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : P => (z : G)) h
  let : Group.IsSolvable U := Group.isSolvable_of_isSolvable_injective hi
  let : Group.IsSolvable (U.map q) := Group.isSolvable_of_surjective (q.subgroupMap_surjective U)
  have hSU : (S : Subgroup R) ≤ U := by
    rw [hS]
    intro s hs
    exact ⟨hH.1.1.2 hs,(show (T : Subgroup G) ≤ localJoin T L from le_sup_right) hs⟩
  have hquot := Matrix.SpecialLinearGroup.ExchangedPair.pair_solvable_overgroup_le_sylow_normalizer
    (S.mapSurjective hq) (U.map q) (map_mono hSU)
  have hcore : q.ker ≤ (S : Subgroup R) := hk ▸ pCore_isPGroup.le_sylow_of_normal S
  have hUN : U ≤ normalizer (S : Set R) := by
    have hh := map_le_iff_le_comap.mp hquot
    change U ≤ (normalizer ((S : Subgroup R).map q : Set _)).comap q at hh
    rwa [comap_normalizer_eq_of_surjective _ hq,comap_map_eq_self hcore] at hh
  have hnmap : U.map R.subtype ≤ normalizer ((S : Subgroup R).map R.subtype : Set G) :=
    (map_mono hUN).trans (le_normalizer_map _)
  have hsmap : (S : Subgroup R).map R.subtype = (T : Subgroup G) ⊓ R := by
    rw [hS]
    exact subgroupOf_map_subtype _ _
  rw [hsmap] at hnmap
  intro x hx
  apply hnmap
  exact ⟨⟨x,hx.2⟩,⟨hx.1,(show R ≤ localJoin T L from le_sup_left) hx.2⟩,rfl⟩

/-- The full HStar overlap normalizes the same original orbit Sylow. -/
theorem source_sl2_hstar_overlap_normalizes_sylow
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal) :
    H ⊓ D.maximalLocal ≤ normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G) := by
  let R := localOrbit T L
  let K := H ⊓ R
  let T0 := (T : Subgroup G) ⊓ R
  have hT0K : T0 ≤ K := le_inf (inf_le_left.trans hH.1.1.2) inf_le_right
  have hKN : K ≤ normalizer (T0 : Set G) :=
    source_sl2_hstar_orbit_intersection_normalizes_sylow D e hn hH
  obtain ⟨S,hS⟩ := source_orbit_sylow_intersection D
  have hsmap : (S : Subgroup R).map R.subtype = T0 := by
    rw [hS]
    exact subgroupOf_map_subtype _ _
  obtain ⟨Q,hQ⟩ := S.exists_map_subtype_eq_of_le (show K ≤ R from inf_le_right)
    (hsmap.le.trans hT0K)
  have hQT0 : (Q : Subgroup K).map K.subtype = T0 := hQ.trans hsmap
  have hQeq : (Q : Subgroup K) = T0.subgroupOf K := by
    apply map_injective K.subtype_injective
    rw [hQT0,map_subgroupOf_eq_of_le hT0K]
  have hnormal : (Q : Subgroup K).Normal := hQeq.symm ▸
    normal_subgroupOf_of_le_normalizer hKN
  let : (Q : Subgroup K).Characteristic := Sylow.characteristic_of_normal Q hnormal
  have hN := normalizer_le_normalizer_characteristic_image K (Q : Subgroup K)
  rw [hQT0] at hN
  exact ((le_inf (inf_le_left.trans H.le_normalizer)
    (show H ⊓ D.maximalLocal ≤ normalizer (R : Set G) from inf_le_right)).trans
      inf_normalizer_le_normalizer_inf).trans hN

/-- The actual Hall subgroup in either SL₂ row normalizes T intersect L₀. -/
theorem hall_normalizes_orbit_sylow {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    B.map H.subtype ≤ normalizer ((T : Subgroup G) ⊓ localOrbit T L : Set G) :=
  (le_inf (map_subtype_le B) (map_le_iff_le_comap.mpr c.hall_le)).trans
    (source_sl2_hstar_overlap_normalizes_sylow D e c.nonnormal c.hstar)


omit D in
private theorem odd_twoPerfect {A : Type*} [Group A] [Finite A]
    (hodd : Odd (Nat.card A)) : IsPPerfect 2 A := by
  intro N hN hp
  let := hN
  have ho : Odd (Nat.card (A ⧸ N)) := hodd.of_dvd_nat N.index_dvd_card
  have hc : Nat.card (A ⧸ N) = 1 := hp.card_eq_or_dvd.resolve_right ho.not_two_dvd_nat
  exact N.index_eq_one.mp hc

/-- An odd subgroup of the original HStar intersection with the orbit lies in
its actual two-residual Borel. -/
theorem source_sl2_hstar_odd_subgroup_le_borel_of_le_orbit
    (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (C : Subgroup G) (hCH : C ≤ H) (hCR : C ≤ localOrbit T L)
    (hodd : Odd (Nat.card C)) : C ≤ sourceOrbitBorel T L := by
  let N := sourceOrbitSylowNormalizer T L
  have hCN : C ≤ N := le_inf hCR ((le_inf hCH hCR).trans
    (source_sl2_hstar_orbit_intersection_normalizes_sylow D e hn hH))
  have hCodd : Odd (Nat.card (C.subgroupOf N)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hCN).toEquiv]
  have hp := le_pResidual_of_isPPerfect (C.subgroupOf N) (odd_twoPerfect hCodd)
  have hh := map_mono (f := N.subtype) hp
  rwa [map_subgroupOf_eq_of_le hCN] at hh

/-- The original Hall subgroup's orbit part is in the source B₀, before
quotienting. The field-automorphism part is not removed by this statement. -/
theorem hall_orbit_intersection_le_borel {H : Subgroup G} {B : Subgroup H}
    (c : Context D H B) (e : (L ⧸ pCore 2 L) ≃* SL(2,F)) :
    B.map H.subtype ⊓ localOrbit T L ≤ sourceOrbitBorel T L := by
  apply source_sl2_hstar_odd_subgroup_le_borel_of_le_orbit D e c.nonnormal c.hstar
    _ (inf_le_left.trans (map_subtype_le B)) inf_le_right
  have ho : Odd (Nat.card (B.map H.subtype)) := by
    rw [card_map_of_injective H.subtype_injective]
    exact hall_odd D c
  exact ho.of_dvd_nat (card_dvd_of_le inf_le_left)

end CFSG.Quasithin.Chapter10.CentralHall.Nonlinear.HallGeometry
