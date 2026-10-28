module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Basic
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedProduct
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.TranslationCommutator
public import Theory.GroupTheory.Commutator.CentralizingComplement


/-!
# Cubic movement on the original marked edge quotient

An arbitrary subgroup of order three in the selected flag residual moves
all of `Q_beta/Q_alpha`. The original projection identifies this quotient
with the intrinsic two-core of the marked model parabolic. Its restriction
to the supplied cubic subgroup is injective because the projection kernel
is a two-group.

In the point model, the four-group and any cubic subgroup generate the
order-twelve residual by divisibility of subgroup orders. The four-group
centralizes itself, so its known full-residual commutator equals its
commutator with that cubic subgroup. The diagram automorphism and the
original flag conjugation transfer this calculation to either marked
parabolic. Pulling back through the original projection adds precisely
its kernel, and the original amalgam embedding gives the literal equality.
No finiteness of the free amalgam is used.

This supplies the edge-movement premise of
`cubic_fixedPreimage_le_of_edge_movement` and
`secondRepresentation_invariants_eq_bot_of_edge_movement` in
`FromFrame.Second.FixedSpace`; their section assembly remains with that
module's owner.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(2), printed p.910, with the selected flag on p.905 and
(4.6.9) on p.908. The concrete translation calculation is reused from
`PSL3Two.Parabolics.MarkedAutomorphisms.TranslationCommutator`.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
open Matrix.PSL3Two Matrix.PSL3Two.MarkedAutomorphisms

private theorem point_cubic_movement (T : Subgroup SL) (hTA : T ≤ pointA)
    (hT : Nat.card T = 3) : ⁅pointV, T⁆ = pointV := by
  have hsup : pointV ⊔ T = pointA := by
    apply eq_of_le_of_card_ge (sup_le pointV_le hTA)
    have h4 : 4 ∣ Nat.card (pointV ⊔ T : Subgroup SL) := by
      simpa only [card_pointV] using (card_dvd_of_le (show pointV ≤ pointV ⊔ T from le_sup_left))
    have h3 : 3 ∣ Nat.card (pointV ⊔ T : Subgroup SL) := by
      simpa only [hT] using (card_dvd_of_le (show T ≤ pointV ⊔ T from le_sup_right))
    rw [card_pointA]
    exact Nat.le_of_dvd Nat.card_pos ((by decide : Nat.Coprime 4 3).mul_dvd_of_dvd_of_dvd h4 h3)
  have hcomm : IsMulCommutative pointV :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) card_pointV
  have hcentral : pointV ≤ centralizer (pointV : Set SL) := by
    intro x hx y hy
    exact congrArg Subtype.val (hcomm.is_comm.comm (⟨y, hy⟩ : pointV) ⟨x,hx⟩)
  have hnorm : T ≤ normalizer pointV :=
    hTA.trans (le_normalizer_iff.mpr pointV_conj)
  rw [commutator_eq_of_centralizing_sup hsup hcentral hnorm,
    ← point_residual, ← pointV_eq_commutator_residual]

private theorem cubic_movement_map (P : Subgroup SL) (e : SL ≃* SL)
    (hP : ∀ T : Subgroup SL, T ≤ residual P → Nat.card T = 3 →
      ⁅P.pCoreIn 2, T⁆ = P.pCoreIn 2)
    (T : Subgroup SL) (hT : T ≤ residual (P.map e.toMonoidHom))
    (hcard : Nat.card T = 3) :
    ⁅(P.map e.toMonoidHom).pCoreIn 2, T⁆ = (P.map e.toMonoidHom).pCoreIn 2 := by
  have hinv : (T.map e.symm.toMonoidHom).map e.toMonoidHom = T := by
    rw [map_map]
    simp
  have hle : T.map e.symm.toMonoidHom ≤ residual P := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hinv]
    change T ≤ ((pResidual 2 P).map P.subtype).map e.toMonoidHom
    rwa [map_embedded_pResidual]
  have hc : Nat.card (T.map e.symm.toMonoidHom) = 3 := by
    rw [card_map_of_injective e.symm.injective, hcard]
  have he := congrArg (fun U : Subgroup SL => U.map e.toMonoidHom) (hP _ hle hc)
  rwa [map_commutator, hinv, map_pCoreIn_of_injective 2 P e.toMonoidHom e.injective] at he

private theorem model_cubic_movement (g : SL) (i : Bool) (T : Subgroup SL)
    (hT : T ≤ residual (modelParabolic g i)) (hcard : Nat.card T = 3) :
    ⁅(modelParabolic g i).pCoreIn 2, T⁆ = (modelParabolic g i).pCoreIn 2 := by
  have hp : ∀ T : Subgroup SL, T ≤ residual pointParabolicSL → Nat.card T = 3 →
      ⁅pointParabolicSL.pCoreIn 2, T⁆ = pointParabolicSL.pCoreIn 2 := by
    intro T hT hc
    rw [MarkedProduct.pointParabolic_core]
    exact point_cubic_movement T (point_residual ▸ hT) hc
  have hl : ∀ T : Subgroup SL, T ≤ residual lineParabolicSL → Nat.card T = 3 →
      ⁅lineParabolicSL.pCoreIn 2, T⁆ = lineParabolicSL.pCoreIn 2 := by
    rw [← pointParabolic_map_diagram]
    exact cubic_movement_map pointParabolicSL diagram hp
  cases i
  · exact cubic_movement_map pointParabolicSL (MulAut.conj g) hp T hT hcard
  · exact cubic_movement_map lineParabolicSL (MulAut.conj g) hl T hT hcard

open Stellmacher.PushingUp.AmalgamGraph Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

omit [Finite M] in
private theorem projection_injective_on_cubic (source : LocalSource L R)
    (S : Subgroup M) (hS : Nat.card S = 3) :
    Function.Injective (source.projection.comp S.subtype) := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  have hxker : (x : M) ∈ pCore 2 M := by
    rw [← source.projection_kernel]
    exact hx
  obtain ⟨n, hn⟩ := pCore_isPGroup (p := 2) (G := M) ⟨x, hxker⟩
  have htwo : (x : M) ^ (2 ^ n) = 1 :=
    congrArg (fun z : pCore 2 M => (z : M)) hn
  have hthree : (x : M) ^ 3 = 1 := by
    have hh : x ^ Nat.card S = 1 := pow_card_eq_one'
    rw [hS] at hh
    exact congrArg Subtype.val hh
  apply Subtype.ext
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 3).pow_left n)
    (orderOf_dvd_of_pow_eq_one htwo) (orderOf_dvd_of_pow_eq_one hthree))

private theorem local_cubic_movement (source : LocalSource L R) (i : Bool)
    (S : Subgroup M) (hS : S ≤ rankOne (parabolic source.projection source.flag i))
    (hcard : Nat.card S = 3) :
    ⁅(parabolic source.projection source.flag i).pCoreIn 2, S⁆ ⊔ pCore 2 M =
      (parabolic source.projection source.flag i).pCoreIn 2 := by
  let P := parabolic source.projection source.flag i
  have hk : IsPGroup 2 source.projection.ker := by
    rw [source.projection_kernel]
    exact pCore_isPGroup
  have hP : P.map source.projection = modelParabolic source.flag i :=
    map_comap_eq_self_of_surjective source.projection_surjective _
  have hcore : (P.pCoreIn 2).map source.projection =
      (modelParabolic source.flag i).pCoreIn 2 := by
    rw [map_pCoreIn_of_ker_isPGroup source.projection hk P, hP]
  have himage : S.map source.projection ≤ residual (modelParabolic source.flag i) := by
    have hh := map_mono (f := source.projection) hS
    rw [rankOne_parabolic_eq source.projection source.projection_surjective hk,
      map_embedded_pResidual] at hh
    exact hP ▸ hh
  have hthree : Nat.card (S.map source.projection) = 3 := by
    let e := MulEquiv.ofBijective (source.projection.subgroupMap S)
      ⟨fun x y h => projection_injective_on_cubic source S hcard (congrArg Subtype.val h),
        source.projection.subgroupMap_surjective S⟩
    exact (Nat.card_congr e.toEquiv).symm.trans hcard
  have hmove : (⁅P.pCoreIn 2, S⁆).map source.projection =
      (P.pCoreIn 2).map source.projection := by
    rw [map_commutator, hcore]
    exact model_cubic_movement source.flag i _ himage hthree
  have hEP : pCore 2 M ≤ P := by
    intro x hx
    change source.projection x ∈ modelParabolic source.flag i
    have he : source.projection x = 1 := by
      exact (show x ∈ source.projection.ker from source.projection_kernel ▸ hx)
    rw [he]
    exact one_mem _
  have hEK : pCore 2 M ≤ P.pCoreIn 2 :=
    le_pCoreIn_of_normalizes pCore_isPGroup hEP le_normalizer_of_normal
  have hSP : S ≤ P := hS.trans (map_subtype_le _)
  have hnorm : S ≤ normalizer (P.pCoreIn 2) :=
    hSP.trans (P.le_normalizer.trans (normalizer_le_normalizer_characteristic_image _ _))
  apply le_antisymm
  · exact sup_le (le_normalizer_iff_commutator_le_left.mp hnorm) hEK
  · change P.pCoreIn 2 ≤ ⁅P.pCoreIn 2, S⁆ ⊔ pCore 2 M
    rw [← source.projection_kernel, ← comap_map_eq]
    exact map_le_iff_le_comap.mp hmove.ge

/-- Every supplied cubic subgroup moves the entire literal marked edge quotient. -/
theorem cubic_edge_movement (source : LocalSource L R) (f : Frame source)
    (T : Subgroup (flagResidual source f.orientation)) (hT : Nat.card T = 3) :
    ⁅Q R (beta R), T.map (flagResidual source f.orientation).subtype⁆ ⊔
      Q R (alpha R) = Q R (beta R) := by
  let P := parabolic source.projection source.flag f.orientation
  let j : flagResidual source f.orientation →* M :=
    (rankOne P).subtype.comp (residualEquiv source f.orientation).symm.toMonoidHom
  have hj : Function.Injective j :=
    (rankOne P).subtype_injective.comp (residualEquiv source f.orientation).symm.injective
  have hS : T.map j ≤ rankOne P := by
    rintro _ ⟨x, hx, rfl⟩
    exact ((residualEquiv source f.orientation).symm x).property
  have hc : Nat.card (T.map j) = 3 := by rw [card_map_of_injective hj, hT]
  have he : (T.map j).map (embedM R) = T.map (flagResidual source f.orientation).subtype := by
    rw [map_map]
    congr 1
    ext x
    exact residualEquiv_symm_apply source f.orientation x
  have hm := congrArg (fun D : Subgroup M => D.map (embedM R))
    (local_cubic_movement source f.orientation (T.map j) hS hc)
  rw [Subgroup.map_sup, map_commutator, he,
    ← Q_alpha R source.two_group source.core_le] at hm
  change ⁅flagKernel source f.orientation, _⁆ ⊔ _ = flagKernel source f.orientation at hm
  rwa [f.edge_kernel] at hm

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
