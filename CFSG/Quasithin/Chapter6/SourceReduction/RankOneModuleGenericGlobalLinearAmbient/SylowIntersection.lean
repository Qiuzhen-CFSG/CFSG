module
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.SylowIntersection
public import Theory.GroupTheory.NormalizedSupCard
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.TorusParity

/-!
# The nontrivial Sylow intersections in the prepared linear row

For each involution j, every two-subgroup of its centralizer lies in the
ambient Sylow T(j) already proved to be its two-core. If two distinct Sylows
have commuting central involutions, this identifies their intersection with
one original root plane; the two disjoint central lines span that plane.
If they do not commute, choose j in the center of their nontrivial intersection.
Both involutions and the whole intersection lie in T(j). The UT₃ common
centralizer calculation identifies that intersection with Z(T(j)), and the
product has order four. This proves all three clauses of F.4.48.

The same core argument and weak closure give the unique conjugate root plane
of each original type through a conjugate central line. These are the exact
intersection and incidence inputs to F.4.49. No Hall-normalizer bound or cube
membership in the full overlap is assumed or concluded here.

Source: Aschbacher–Smith F.4.46(2), F.4.48–49, printed pp.297–299
(`refs/quasithin.pdf`). All statements use the original ambient group, both
comparison orientations, and every original degree n>1, including field four.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Matrix.PSL3Even.UnipotentGeometry Matrix.PSL3.LinearAmbientGeometry
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- Every two-subgroup of an involution centralizer lies in its literal core. -/
theorem Preparation.linear_two_subgroup_le_involution_core
    (x : G) (hx : orderOf x=2) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (hQC : Q ≤ centralizer ({x} : Set G)) :
    Q ≤ (centralizer ({x} : Set G)).pCoreIn 2 := by
  obtain ⟨P,hP,hN⟩ := d.linear_involution_centralizer_sylow h hH hp F hm hF he hmax x hx
  rw [hP]
  exact fun a ha => ((hQ.inf_normalizer_sylow P).le ⟨ha,hN (hQC ha)⟩).2

/-- The core attached to a central involution is its original ambient Sylow. -/
theorem Preparation.linear_central_involution_core
    (P : Sylow 2 G) (x : G) (hx : orderOf x=2) (hxP : x ∈ centerIn (P : Subgroup G)) :
    (centralizer ({x} : Set G)).pCoreIn 2=(P : Subgroup G) := by
  obtain ⟨Q,hQ,_⟩ := d.linear_involution_centralizer_sylow h hH hp F hm hF he hmax x hx
  have hPQ : (P : Subgroup G) ≤ (Q : Subgroup G) := by
    rw [←hQ]
    apply d.linear_two_subgroup_le_involution_core h hH hp F hm hF he hmax x hx _ P.isPGroup'
    exact fun a ha => mem_centralizer_singleton_iff.mpr (hxP.2 a ha)
  exact hQ.trans (P.is_maximal' Q.isPGroup' hPQ)

/-- The commuting nonidentical central involutions give exactly a root-plane
intersection, and their two whole central lines span that same plane. -/
theorem Preparation.linear_commuting_sylow_intersection
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G))
    (hcomm : Commute z (g*z*g⁻¹)) :
    ∃ i : Fin 2,
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g = (![L,residual H] i).pCoreIn 2 ∧
      centerIn (sourceS L H) ⊔ (centerIn (sourceS L H)).conjBy g =
        (![L,residual H] i).pCoreIn 2 ∧ orderOf (z*(g*z*g⁻¹))=2 := by
  let y := g*z*g⁻¹
  let P : Sylow 2 G := g • T
  let Z := centerIn (sourceS L H)
  have hST := d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax
  have hy : orderOf y=2 := (MulAut.conj g).orderOf_eq z |>.trans hz
  have hzT : z ∈ centerIn (T : Subgroup G) := hST ▸ hzZ
  have hyP : y ∈ centerIn (P : Subgroup G) := by
    change y ∈ centerIn ((T : Subgroup G).map (MulAut.conj g).toMonoidHom)
    rw [←centerIn_map_equiv]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hzT
  have hcZ := d.linear_central_involution_core h hH hp F hm hF he hmax T z hz hzT
  have hcY := d.linear_central_involution_core h hH hp F hm hF he hmax P y hy hyP
  have hyT : y ∈ (T : Subgroup G) := hcZ ▸
    d.linear_commuting_involution_mem_core h hH hp F hm hF he hmax y z hy hz hcomm.symm
  have hyZ : y ∉ (center (sourceS L H)).map (sourceS L H).subtype := by
    intro hyZ
    rw [←centerIn_eq_map_center,hST] at hyZ
    have hh := d.linear_central_involution_core h hH hp F hm hF he hmax T y hy hyZ
    apply hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact hcY.symm.trans hh
  have hcent : (T : Subgroup G) ⊓ (P : Subgroup G) =
      (T : Subgroup G) ⊓ centralizer ({y} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left _ (fun a ha => mem_centralizer_singleton_iff.mpr (hyP.2 a ha))
    · refine le_inf inf_le_left ?_
      rw [←hcY]
      exact d.linear_two_subgroup_le_involution_core h hH hp F hm hF he hmax y hy _
        T.isPGroup'.to_inf_left inf_le_right
  obtain ⟨i,hi⟩ : ∃ i : Fin 2,
      (T : Subgroup G) ⊓ (P : Subgroup G) = (![L,residual H] i).pCoreIn 2 := by
    rcases (d.linear_involution_geometry h hH hp F hm hF he hmax).2.2.2.2 y
      (hST.symm ▸ hyT) (hy ▸ pow_orderOf_eq_one y) hyZ with hh | hh
    · exact ⟨0,hcent.trans (hST ▸ hh)⟩
    · exact ⟨1,hcent.trans (hST ▸ hh)⟩
  have hZP : Z ≤ (P : Subgroup G) := by
    rw [←hcY]
    apply d.linear_two_subgroup_le_involution_core h hH hp F hm hF he hmax y hy _
      (T.isPGroup'.to_le (hST ▸ (show Z ≤ sourceS L H from inf_le_left)))
    exact fun a ha => mem_centralizer_singleton_iff.mpr (ha.2 y (hST.symm ▸ hyT)).symm
  have hZgT : Z.conjBy g ≤ (T : Subgroup G) := by
    rw [←hcZ]
    have hzP : z ∈ (P : Subgroup G) := hcY ▸
      d.linear_commuting_involution_mem_core h hH hp F hm hF he hmax z y hz hy hcomm
    have hZg : Z.conjBy g = centerIn (P : Subgroup G) := by
      change Z.map (MulAut.conj g).toMonoidHom = _
      rw [show Z=centerIn (T : Subgroup G) from congrArg centerIn hST,
        centerIn_map_equiv]
      rfl
    rw [hZg]
    apply d.linear_two_subgroup_le_involution_core h hH hp F hm hF he hmax z hz _
      (P.isPGroup'.to_le inf_le_left)
    exact fun a ha => mem_centralizer_singleton_iff.mpr (ha.2 z hzP).symm
  have hZgP : Z.conjBy g ≤ (P : Subgroup G) :=
    map_mono (hST ▸ (show Z ≤ sourceS L H from inf_le_left))
  have hle : Z ⊔ Z.conjBy g ≤ (![L,residual H] i).pCoreIn 2 := by
    rw [←hi]
    exact sup_le (le_inf (hST ▸ (show Z ≤ sourceS L H from inf_le_left)) hZP)
      (le_inf hZgT hZgP)
  have hdis : Disjoint Z (Z.conjBy g) := by
    rcases d.linear_center_TI h hH hp F hm hF he hmax g with hh | hh
    · apply (hg ?_).elim
      rw [d.linear_sylow_normalizer_eq_inter h hH hp F hm hF he hmax,
        ←d.linear_center_normalizer h hH hp F hm hF he hmax]
      exact mem_normalizer_iff_map_conj_eq.mpr hh
    · exact hh
  have hcardZ : Nat.card Z=Nat.card F := by
    rw [show Z=centerIn (sourceS L H) from rfl,centerIn_eq_map_center,
      card_map_of_injective (sourceS L H).subtype_injective]
    exact (d.linear_involution_geometry h hH hp F hm hF he hmax).2.1
  have hnorm : Z.conjBy g ≤ normalizer (Z : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    exact hZgT.trans (fun a ha b hb => (hb.2 a (hST.symm ▸ ha)).symm)
  have hsup : Z ⊔ Z.conjBy g = (![L,residual H] i).pCoreIn 2 := by
    apply eq_of_le_of_card_ge hle
    rw [card_sup_eq_mul_of_normalizes_of_disjoint Z (Z.conjBy g) hnorm hdis]
    change Nat.card ((![L,residual H] i).pCoreIn 2) ≤ Nat.card Z * Nat.card (Z.map (MulAut.conj g).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj g).injective,hcardZ,
      ((d.linear_core_structure h hH hp F hm hF he).2.2 i).2.1,pow_two]
  have hprod1 : z*y≠1 := by
    intro hh
    have hz1 : z≠1 := by intro hh; simp [hh] at hz
    apply hz1
    apply disjoint_def.mp hdis hzZ
    have hzy : z=y := by
      calc
        z = z*(z*y) := by rw [hh,mul_one]
        _ = y := by rw [←mul_assoc,←pow_two,←hz,pow_orderOf_eq_one,one_mul]
    exact hzy.symm ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hzZ
  refine ⟨i,hi,hsup,orderOf_eq_prime ?_ hprod1⟩
  rw [hcomm.mul_pow,show z^2=1 from hz ▸ pow_orderOf_eq_one z,
    show (g*z*g⁻¹)^2=1 from hy ▸ pow_orderOf_eq_one y,one_mul]

/-- Noncommuting central involutions in nondisjoint Sylows have product of
order four; their original Sylows intersect in a third conjugate central line. -/
theorem Preparation.linear_noncommuting_sylow_intersection
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (sourceS L H))
    (g : G) (hne : (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≠ ⊥)
    (hcomm : ¬ Commute z (g*z*g⁻¹)) :
    (∃ a : G, (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g =
      (centerIn (sourceS L H)).conjBy a) ∧
    (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≠ centerIn (sourceS L H) ∧
    (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≠ (centerIn (sourceS L H)).conjBy g ∧
    orderOf (z*(g*z*g⁻¹))=4 := by
  let y := g*z*g⁻¹
  let Q : Sylow 2 G := g • T
  let I := (T : Subgroup G) ⊓ (Q : Subgroup G)
  have hST := d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax
  have hy : orderOf y=2 := (MulAut.conj g).orderOf_eq z |>.trans hz
  have hzT : z ∈ centerIn (T : Subgroup G) := hST ▸ hzZ
  have hyQ : y ∈ centerIn (Q : Subgroup G) := by
    change y ∈ centerIn ((T : Subgroup G).map (MulAut.conj g).toMonoidHom)
    rw [←centerIn_map_equiv]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom hzT
  have hI : IsPGroup 2 I := T.isPGroup'.to_inf_left
  obtain ⟨v,hv1⟩ := ne_bot_iff_exists_ne_one.mp
    (inf_centerIn_ne_bot hI hne le_rfl I.le_normalizer)
  have hv2 : 2 ∣ orderOf (v:G) := by
    have hh := (hI.to_le (show I ⊓ centerIn I ≤ I from inf_le_left)).dvd_orderOf hv1
    exact (orderOf_injective (I ⊓ centerIn I).subtype (I ⊓ centerIn I).subtype_injective v) ▸ hh
  let j : G := (v:G)^(orderOf (v:G)/2)
  have hj : orderOf j=2 := orderOf_pow_orderOf_div (orderOf_pos _).ne' hv2
  have hjZ : j ∈ centerIn I := (centerIn I).pow_mem v.property.2 _
  obtain ⟨P,hP,_⟩ := d.linear_involution_centralizer_sylow h hH hp F hm hF he hmax j hj
  have hIP : I ≤ (P : Subgroup G) := by
    rw [←hP]
    apply d.linear_two_subgroup_le_involution_core h hH hp F hm hF he hmax j hj I hI
    exact fun a ha => mem_centralizer_singleton_iff.mpr (hjZ.2 a ha)
  have hzP : z ∈ (P : Subgroup G) := hP ▸
    d.linear_commuting_involution_mem_core h hH hp F hm hF he hmax z j hz hj
      (hzT.2 j hjZ.1.1).symm
  have hyP : y ∈ (P : Subgroup G) := hP ▸
    d.linear_commuting_involution_mem_core h hH hp F hm hF he hmax y j hy hj
      (hyQ.2 j hjZ.1.2).symm
  obtain ⟨e⟩ := (d.linear_core_structure h hH hp F hm hF he).2.1
  let eP : U F ≃* P := (e.trans (MulEquiv.subgroupCongr hST)).trans (T.equiv P)
  have hpair := marked_noncommuting_centralizers F (P : Subgroup G) eP z y hzP hyP
    (hz ▸ pow_orderOf_eq_one z) (hy ▸ pow_orderOf_eq_one y) hcomm
  have hiP : I=centerIn (P : Subgroup G) := by
    apply le_antisymm
    · intro a ha
      rw [←hpair]
      exact ⟨⟨hIP ha,mem_centralizer_singleton_iff.mpr (hzT.2 a ha.1)⟩,
        ⟨hIP ha,mem_centralizer_singleton_iff.mpr (hyQ.2 a ha.2)⟩⟩
    · have hcZ := d.linear_central_involution_core h hH hp F hm hF he hmax T z hz hzT
      have hcY := d.linear_central_involution_core h hH hp F hm hF he hmax Q y hy hyQ
      apply le_inf
      · rw [←hcZ]
        apply d.linear_two_subgroup_le_involution_core h hH hp F hm hF he hmax z hz _
          (P.isPGroup'.to_le inf_le_left)
        exact fun a ha => mem_centralizer_singleton_iff.mpr (ha.2 z hzP).symm
      · rw [←hcY]
        apply d.linear_two_subgroup_le_involution_core h hH hp F hm hF he hmax y hy _
          (P.isPGroup'.to_le inf_le_left)
        exact fun a ha => mem_centralizer_singleton_iff.mpr (ha.2 y hyP).symm
  have hline : ∃ a : G, I=(centerIn (sourceS L H)).conjBy a := by
    obtain ⟨a,ha⟩ := MulAction.exists_smul_eq G T P
    refine ⟨a,?_⟩
    rw [hiP,hST]
    change centerIn (P : Subgroup G) = (centerIn (T : Subgroup G)).map (MulAut.conj a).toMonoidHom
    rw [centerIn_map_equiv,←ha]
    rfl
  have hiZ : I≠centerIn (sourceS L H) := by
    intro hh
    apply hcomm
    have hzI : z ∈ I := hh.symm ▸ hzZ
    exact (hyQ.2 z hzI.2)
  have hiZg : I≠(centerIn (sourceS L H)).conjBy g := by
    intro hh
    apply hcomm
    have hyI : y ∈ I := hh.symm ▸ mem_map_of_mem (MulAut.conj g).toMonoidHom hzZ
    exact (hzT.2 y hyI.1).symm
  refine ⟨hline,hiZ,hiZg,?_⟩
  have h4 := marked_pow_four F (P : Subgroup G) eP (z*y) ((P : Subgroup G).mul_mem hzP hyP)
  have h2 : (z*y)^2≠1 := by
    intro hh
    apply hcomm
    have hz2 : z*z=1 := by rw [←pow_two,←hz,pow_orderOf_eq_one]
    have hy2 : y*y=1 := by rw [←pow_two,←hy,pow_orderOf_eq_one]
    have hzy : z*y = (z*y)⁻¹ := (eq_inv_iff_mul_eq_one).mpr (by simpa only [pow_two] using hh)
    have hzi : z⁻¹=z := (inv_eq_of_mul_eq_one_right hz2)
    have hyi : y⁻¹=y := (inv_eq_of_mul_eq_one_right hy2)
    change z*y=y*z
    simpa only [mul_inv_rev,hzi,hyi] using hzy
  exact orderOf_eq_prime_pow (p := 2) (n := 1) h2 h4

/-- Every conjugate central line lying in the original Sylow is contained
in one of its two original root planes. -/
theorem Preparation.linear_central_line_in_sylow (g : G)
    (hg : (centerIn (sourceS L H)).conjBy g ≤ (T : Subgroup G)) :
    ∃ i : Fin 2, (centerIn (sourceS L H)).conjBy g ≤ (![L,residual H] i).pCoreIn 2 := by
  let Z := centerIn (sourceS L H)
  have hZQ : Z ≤ L.pCoreIn 2 := by
    have hh := (d.linear_involution_geometry h hH hp F hm hF he hmax).1
    rw [←centerIn_eq_map_center] at hh
    exact hh.le.trans inf_le_left
  let : IsElementaryAbelian 2 (L.pCoreIn 2) :=
    ((d.linear_core_structure h hH hp F hm hF he).2.2 0).1
  let : IsElementaryAbelian 2 Z := IsElementaryAbelian.of_injective
    (inclusion hZQ) (inclusion_injective hZQ)
  let : IsElementaryAbelian 2 (Z.conjBy g) :=
    IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  obtain ⟨e,hplanes⟩ := d.linear_root_coordinates h hH hp F hm hF he hmax
  have hS : Z.conjBy g ≤ sourceS L H := by
    rwa [d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax]
  rcases marked_elementary_le_plane F (sourceS L H) e (Z.conjBy g) hS with h₁ | h₂
  · rcases hplanes with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨0,ha ▸ h₁⟩
    · exact ⟨1,ha ▸ h₁⟩
  · rcases hplanes with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · exact ⟨1,hb ▸ h₂⟩
    · exact ⟨0,hb ▸ h₂⟩

/-- Every ambient conjugate root plane through the original central line is
the original plane of its type. This is the uniqueness used in F.4.49. -/
theorem Preparation.linear_root_plane_through_center (i : Fin 2) (g : G)
    (hg : centerIn (sourceS L H) ≤ ((![L,residual H] i).pCoreIn 2).conjBy g) :
    ((![L,residual H] i).pCoreIn 2).conjBy g = (![L,residual H] i).pCoreIn 2 := by
  let Q := (![L,residual H] i).pCoreIn 2
  let : IsElementaryAbelian 2 Q := ((d.linear_core_structure h hH hp F hm hF he).2.2 i).1
  let : IsElementaryAbelian 2 (Q.conjBy g) := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hc : Q.conjBy g ≤ centralizer (Q.conjBy g : Set G) :=
    le_centralizer_iff_isMulCommutative.mpr inferInstance
  obtain ⟨z,hz,hz2,_⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  have hcore := (d.linear_centralizer_core_eq_sourceS h hH hp F hm hF he hmax z hz2 hz).trans
    (d.linear_sourceS_eq_sylow h hH hp F hm hF he hmax)
  have hle : Q.conjBy g ≤ (T : Subgroup G) := by
    rw [←hcore]
    apply d.linear_two_subgroup_le_involution_core h hH hp F hm hF he hmax z hz2 _
      ((isPGroup_pCoreIn 2 (![L,residual H] i)).map (MulAut.conj g).toMonoidHom)
    exact fun a ha => mem_centralizer_singleton_iff.mpr ((hc ha) z (hg hz)).symm
  apply d.linear_root_planes_weakly_closed h hH hp F hm hF he hmax Q _ g hle
  fin_cases i <;> simp [Q]

/-- The same uniqueness holds at every conjugate of the original central line,
retaining the two distinct original root-plane orbits. -/
theorem Preparation.linear_root_plane_through_conjugate_center (i : Fin 2) (a b : G)
    (hab : (centerIn (sourceS L H)).conjBy a ≤ ((![L,residual H] i).pCoreIn 2).conjBy b) :
    ((![L,residual H] i).pCoreIn 2).conjBy a = ((![L,residual H] i).pCoreIn 2).conjBy b := by
  have hh := map_mono (f := (MulAut.conj a⁻¹).toMonoidHom) hab
  change ((centerIn (sourceS L H)).conjBy a).conjBy a⁻¹ ≤
    (((![L,residual H] i).pCoreIn 2).conjBy b).conjBy a⁻¹ at hh
  rw [conjBy_conjBy,inv_mul_cancel,conjBy_one,conjBy_conjBy] at hh
  have heq := d.linear_root_plane_through_center h hH hp F hm hF he hmax i (a⁻¹*b) hh
  have hm := congrArg (fun U : Subgroup G => U.conjBy a) heq
  rw [conjBy_conjBy,mul_inv_cancel_left] at hm
  exact hm.symm

/-- All three clauses of source F.4.48 for the original Sylow and central
involution. The two central lines and the actual Sylow intersection are
retained, including their noncoincidence in the order-four case. -/
theorem Preparation.linear_sylow_intersection_trichotomy
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G)) :
    (Disjoint (T : Subgroup G) ((T : Subgroup G).conjBy g) ∧
      Odd (orderOf (z*(g*z*g⁻¹)))) ∨
    (∃ i : Fin 2,
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g = (![L,residual H] i).pCoreIn 2 ∧
      centerIn (sourceS L H) ⊔ (centerIn (sourceS L H)).conjBy g =
        (![L,residual H] i).pCoreIn 2 ∧ orderOf (z*(g*z*g⁻¹))=2) ∨
    ((∃ a : G, (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g =
      (centerIn (sourceS L H)).conjBy a) ∧
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≠ centerIn (sourceS L H) ∧
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g ≠ (centerIn (sourceS L H)).conjBy g ∧
      orderOf (z*(g*z*g⁻¹))=4) := by
  by_cases hd : Disjoint (T : Subgroup G) ((T : Subgroup G).conjBy g)
  · exact Or.inl ⟨hd,
      (d.linear_odd_product_iff_disjoint_sylows h hH hp F hm hF he hmax z hz hzZ g hg).mpr hd⟩
  right
  by_cases hc : Commute z (g*z*g⁻¹)
  · exact Or.inl (d.linear_commuting_sylow_intersection h hH hp F hm hF he hmax z hz hzZ g hg hc)
  · exact Or.inr (d.linear_noncommuting_sylow_intersection h hH hp F hm hF he hmax z hz hzZ g
      (fun hh => hd (disjoint_iff.mpr hh)) hc)

/-- A conjugator whose Sylow intersection contains an original root plane
lies in that plane's original full factor normalizer. This localizes the
root-plane case of F.4.49 without replacing either Sylow or normalizer. -/
theorem Preparation.linear_root_plane_intersection_normalizer (i : Fin 2) (g : G)
    (hg : (![L,residual H] i).pCoreIn 2 ≤ (T : Subgroup G).conjBy g) :
    g ∈ normalizer (![L,residual H] i : Set G) := by
  let Q := (![L,residual H] i).pCoreIn 2
  have hle := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hg
  change Q.conjBy g⁻¹ ≤ ((T : Subgroup G).conjBy g).conjBy g⁻¹ at hle
  rw [conjBy_conjBy,inv_mul_cancel,conjBy_one] at hle
  have hQ : Q ∈ ({L.pCoreIn 2,(residual H).pCoreIn 2} : Set (Subgroup G)) := by
    fin_cases i <;> simp [Q]
  have hfix := d.linear_root_planes_weakly_closed h hH hp F hm hF he hmax Q hQ g⁻¹ hle
  have hginv : g⁻¹ ∈ normalizer (Q : Set G) := mem_normalizer_iff_map_conj_eq.mpr hfix
  have hgQ : g ∈ normalizer (Q : Set G) := by
    simpa only [inv_inv] using (normalizer (Q : Set G)).inv_mem hginv
  have hn := d.linear_root_normalizers h hH hp F hm hF he hmax
  fin_cases i
  · exact hn.1 ▸ hgQ
  · exact hn.2.1 ▸ hgQ

/-- The complete commuting case is local to one of the two original full
normalizers; its actual two central lines span the original root plane. -/
theorem Preparation.linear_commuting_sylow_intersection_local
    (z : G) (hz : orderOf z=2) (hzZ : z ∈ centerIn (sourceS L H))
    (g : G) (hg : g ∉ normalizer (T : Set G))
    (hcomm : Commute z (g*z*g⁻¹)) :
    ∃ i : Fin 2, g ∈ normalizer (![L,residual H] i : Set G) ∧
      (T : Subgroup G) ⊓ (T : Subgroup G).conjBy g = (![L,residual H] i).pCoreIn 2 ∧
      centerIn (sourceS L H) ⊔ (centerIn (sourceS L H)).conjBy g =
        (![L,residual H] i).pCoreIn 2 ∧ orderOf (z*(g*z*g⁻¹))=2 := by
  obtain ⟨i,hi,hspan,ho⟩ := d.linear_commuting_sylow_intersection
    h hH hp F hm hF he hmax z hz hzZ g hg hcomm
  exact ⟨i,d.linear_root_plane_intersection_normalizer h hH hp F hm hF he hmax i g
    (hi ▸ inf_le_right),hi,hspan,ho⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
