module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.CubicOrbit.Movement
public import Theory.Representation.BinaryOffender.SectionOffender

/-!
# Fixed-quotient recognition for the cubic distance-two orbit

An order-eight actor of fixed codimension two is a best offender. If the
later orbit action had kernel Q, the full B.5.1 classifier would select
its faithful triple-cover row. That row has quadratic ratio one, whereas
the same actor remains strict on the moved quotient. This contradiction
proves that the later kernel is the full cubic extension E.

Descend the original orbit action through its marked map onto S₆. The
proved full movement and exact actor indices then give the natural fixed
quotient and movement of its entire fixed preimage. No central line or
odd covering kernel is discarded. DistanceTwoComplete applies recognition
to the original whole core and the literal rank-two consumer.

Source: Meierfrankenfeld--Stellmacher (1993), (3.6), printed p.871,
using Aschbacher--Smith B.5.1 and C.1.31--32, pp.99--103,135--136.
-/

public noncomputable section
open CFSG.Quasithin
open Subgroup Theory.GroupTheory Representation BinaryPermutation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.CoveredSixModels

namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction

private theorem eight_codim_two_best
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (hf : Function.Injective ρ)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 8) (hc : fixedCodim ρ A = 2) : IsBestOffender ρ A := by
  have hne : A ≠ ⊥ := by intro he; rw [he,card_bot] at hA; omega
  have hr : rank A = 3 := by simp [rank,hA]; decide
  have hd := fixedCodim_add_finrank ρ A
  refine ⟨⟨hne,inferInstance⟩,fun B hBA => ?_⟩
  by_cases he : B = A
  · exact he ▸ le_rfl
  have hbcard : Nat.card B < 8 := by
    have hb := Nat.card_le_card_of_injective (inclusion hBA) (inclusion_injective hBA)
    have hn : Nat.card B ≠ Nat.card A := fun hh => he (eq_of_le_of_card_ge hBA hh.ge)
    omega
  have hrB : rank B ≤ 2 := by
    have hh := Nat.log_lt_of_lt_pow (b := 2) (x := 3) ((Nat.card_pos (α := B)).ne') hbcard
    exact Nat.le_of_lt_succ hh
  by_cases hB : B = ⊥
  · rw [hB,weight_bot]
    unfold weight
    omega
  have hbpos := fixedCodim_pos_of_faithful ρ hf hB
  have hbdim := fixedCodim_add_finrank ρ B
  unfold weight
  omega

/-- A faithful covering-six FF action cannot have an order-eight strict offender. -/
theorem no_hexEven_strict_eight
    {H V : Type*} [Group H] [Finite H] [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V]
    (ρ : Representation (ZMod 2) H V) (C : Subgroup H)
    [C.Normal] [IsQuasisimple C]
    (hq : IsPGroup 2 (H ⧸ C)) (hcore : pCore 2 H = ⊥)
    (hsq : IsSQTK CFSG.KnownSimple.IsKnownSimple C)
    (hf : Function.Injective ρ) (e : C ≃* Atlas.Codes.HexEvenAutomorphisms)
    (A : Subgroup H) [IsElementaryAbelian 2 A]
    (hA : Nat.card A = 8) (hc : fixedCodim ρ A = 2) : False := by
  have hb := eight_codim_two_best ρ hf A hA hc
  obtain ⟨hCJ,⟨c⟩⟩ := SourceCompletion.ff_quasisimple_source_conclusion
    ρ C hq hcore hsq hf ⟨A,hb.isOffender ρ⟩
  let J := offenderSubgroup ρ
  let B := A.subgroupOf J
  have hAJ := hb.le_offenderSubgroup ρ
  have hB := (hb.isOffender ρ).subgroupOf ρ hAJ
  have hratio := (source_tripleSix _ c ((subgroupOfEquivOfLe hCJ).trans e)).2.2.2.2.2
  have hbound : fixedCodim c.sectionData.action B ≤ 2 := by
    have hquot := fixedCodim_le_of_equivariant_surjection
      c.sectionData.space.toRepresentation c.sectionData.action
      c.sectionData.central.toSubmodule.mkQ c.sectionData.central.toSubmodule.mkQ_surjective
      (fun _ _ => rfl) B
    have hsub := fixedCodim_subrepresentation_le (ρ.comp J.subtype) c.sectionData.space B
    have heq : fixedCodim (ρ.comp J.subtype) B = 2 := (fixedCodim_subgroupOf ρ hAJ).trans hc
    omega
  have hr : rank B = 3 := by rw [rank_subgroupOf hAJ]; simp [rank,hA]; decide
  have hB' : IsOffender c.sectionData.action B := ⟨hB.1,by omega⟩
  have heq := (hB'.best_and_codim_eq_of_quadraticRatio_eq_one _ hratio).2
  omega

open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "K" => L.subgroupOf (L ⊔ R)
local notation "T" => edge L R
local notation "π" => projection h e hz hk

include h e hz hk in
/-- The strict orbit offender rules out a faithful triple-cover action.
Thus the full cubic kernel survives on the later orbit quotient as well. -/
theorem orbitQuotientAction_kernel
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) :
    (orbitQuotientAction h o).ker = extensionKernel h := by
  rcases orbitQuotientAction_kernel_cases h e hz hk o with hf | hf
  · exfalso
    let := o.quotient_elementary
    let := h.relative_normal
    let := h.relative_core_quasisimple e
    let Q := pCore 2 M
    let q := QuotientGroup.mk' Q
    let C := componentImage L R
    let β := orbitQuotientAction h o
    let f := (QuotientGroup.kerLift β).comp
      (QuotientGroup.quotientMulEquivOfEq hf.symm).toMonoidHom
    have hfi : Function.Injective f := (QuotientGroup.kerLift_injective β).comp
      (QuotientGroup.quotientMulEquivOfEq hf.symm).injective
    have hfq : f.comp q = β := by ext x; simp [f,q]
    let σ := orbitAutomorphismRepresentation h o
    let ρ := σ.comp f
    let B := o.opposite.comap (embedM T)
    let A := B.map q
    have hAf : A.map f = B.map β := by rw [map_map,hfq]
    let := orbit_actor_elementary h o
    let : IsElementaryAbelian 2 (A.map f) := hAf ▸ inferInstance
    let : IsElementaryAbelian 2 A := IsElementaryAbelian.of_injective
      (A.equivMapOfInjective f hfi).toMonoidHom (A.equivMapOfInjective f hfi).injective
    have hA : Nat.card A = 8 := by
      rw [←card_map_of_injective hfi,hAf,orbitQuotientAction_opposite_card h e hz hk o]
      exact (preliminary_orbit_indices h e hz hk o).1
    have hcod : fixedCodim ρ A = 2 := by
      have hh := orbit_actor_fixed_index h o
      rw [(preliminary_orbit_indices h e hz hk o).2.2] at hh
      have he : 2 ^ fixedCodim σ (B.map β) = 2 ^ 2 := hh.symm
      have heq := (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
      unfold fixedCodim
      rw [fixedSpace_comp_map,hAf]
      exact heq
    let : C.Normal := (inferInstance : (K).Normal).map q (QuotientGroup.mk'_surjective _)
    let : IsQuasisimple C := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv h.component)
    let l := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
    obtain ⟨a,_⟩ := exists_quotient_hexacode_equiv h e hz
    let ec : C ≃* Atlas.Codes.HexEvenAutomorphisms :=
      (cComponentTwoCoreQuotientEquiv h.component).symm.trans
        ((QuotientGroup.congr _ _ l (pCore_map_iso 2 l)).trans a)
    have hsup : C ⊔ (T).map q = ⊤ := by
      rw [←Subgroup.map_sup,(codisjoint_subgroupOf_sup L R).eq_top]
      exact map_top_of_surjective q (QuotientGroup.mk'_surjective _)
    have hquot := isPGroup_quotient_of_sup_eq_top C ((T).map q)
      (h.relative_radical.isPGroup.map q) hsup
    have hsq : IsSQTK KnownSimple.IsKnownSimple (M ⧸ Q) := by
      refine ⟨?_,h.sqtk.isKGroup.quotient _⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho Q pCore_isPGroup).trans
        (h.sqtk.stronglyQuasithin p hp ho)
    exact no_hexEven_strict_eight ρ C hquot (pCore_quotient_pCore_eq_bot 2)
      (hsq.subgroup C) ((orbitAutomorphismRepresentation_injective h o).comp hfi) ec A hA hcod
  · exact hf

include h e hz hk in
/-- The original cubic distance-two orbit has the required natural fixed
quotient and its entire fixed preimage lies in the paired commutator layer. -/
theorem preliminary_recognized
    (o : BeforePlane.PreliminaryPair T (sourceGeometry h)) : o.Recognized := by
  let := o.quotient_elementary
  let β := orbitQuotientAction h o
  let π0 := π
  have honto := projection_surjective_of_distanceTwo h e hz hk o.distance_two
  have hker : π0.ker = β.ker :=
    (projection_kernel h e hz hk).trans (orbitQuotientAction_kernel h e hz hk o).symm
  let f : Equiv.Perm (Fin 6) →* MulAut (OrbitQuotient T o.c o.b) :=
    π0.liftOfSurjective honto ⟨β,hker.le⟩
  have hfp : f.comp π0 = β :=
    MonoidHom.liftOfRightInverse_comp _ _ (Function.rightInverse_surjInv honto) _
  have hfi : Function.Injective f := by
    apply f.ker_eq_bot_iff.mp
    apply le_bot_iff.mp
    intro y hy
    obtain ⟨x,rfl⟩ := honto y
    apply mem_bot.mpr
    have hx : x ∈ β.ker := by
      change β x = 1
      rw [←hfp]
      exact hy
    exact hker.ge hx
  let ρ := (orbitAutomorphismRepresentation h o).comp f
  let q : (⊤ : Subgroup M) →* Equiv.Perm (Fin 6) := π0.comp (⊤ : Subgroup M).subtype
  have hqonto : Function.Surjective q := honto.comp Subgroup.topEquiv.surjective
  have hcomp : ρ.comp q = orbitRepresentation T o.c o.b := by
    ext m v
    change orbitAutomorphismRepresentation h o (f (π0 m)) v = _
    rw [show f (π0 m) = β m from DFunLike.congr_fun hfp m.val]
    rfl
  have hK : ((pResidual 2 M).subgroupOf ⊤).map q = alternatingGroup (Fin 6) := by
    rw [show q = π0.comp (⊤ : Subgroup M).subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le (show pResidual 2 M ≤ ⊤ from le_top),h.relative_residual]
    exact component_image h e hz hk
  let B := (o.opposite.comap (embedM T)).map π0
  have hB : ((o.opposite.comap (embedM T)).subgroupOf ⊤).map q = B := by
    rw [show q = π0.comp (⊤ : Subgroup M).subtype from rfl,←map_map,
      map_subgroupOf_eq_of_le (show o.opposite.comap (embedM T) ≤ ⊤ from le_top)]
  let := opposite_permutation_image_elementary h e hz hk o
  have hcard : Nat.card B = 8 :=
    (opposite_permutation_image_card h e hz hk o).trans (preliminary_orbit_indices h e hz hk o).1
  have hc : fixedCodim ρ B = 2 := by
    have hh := orbit_actor_fixed_index h o
    rw [(preliminary_orbit_indices h e hz hk o).2.2] at hh
    have he : 2 ^ fixedCodim (orbitAutomorphismRepresentation h o)
        ((o.opposite.comap (embedM T)).map β) = 2 ^ 2 := hh.symm
    have heq := (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_map,hfp]
    exact heq
  have hmove : subspaceCommutator ρ ⊤ (alternatingGroup (Fin 6)) = ⊤ := by
    have hh := (orbitSection T o.c o.b o.layer_le).subspaceCommutator_eq_top_of_movement
      (pResidual 2 M) le_top (preliminary_full_movement h e hz hk o)
    rw [←hcomp,subspaceCommutator_comp_map,hK] at hh
    exact hh
  obtain ⟨ec⟩ := layerComponent_equiv_alternating h e hk
  have hsqA := IsSQTK.knownSimple_of_equiv ec (layerComponent_sqtk h e hz)
  obtain ⟨a,p,_,hpk,he,hfix⟩ :=
    ChapterB.QuasisimpleSource.SourceCompletion.symmetricSix_natural_quotient_fixed_le_moved
      ρ ((orbitAutomorphismRepresentation_injective h o).comp hfi) hsqA B hcard hc
      (Natural.Exhaustion.DistanceTwo.Recognition.PermutationModel.elementary_eight_odd B hcard) hmove
  have hfixed : fixedSpace ρ (alternatingGroup (Fin 6)) =
      orbitFixedSpace (pResidual 2 M) T o.c o.b := by
    rw [←hK,←fixedSpace_comp_map,hcomp]
    ext v
    constructor
    · intro hv k
      exact hv ⟨⟨k,mem_top _⟩,k.property⟩
    · intro hv k
      exact hv ⟨k.val.val,k.property⟩
  apply o.recognized_of_clauses
  · rw [hfixed] at hpk
    intro u v hu hv
    obtain ⟨x,rfl⟩ := (orbitFixedSpace (pResidual 2 M) T o.c o.b).mkQ_surjective u
    obtain ⟨y,rfl⟩ := (orbitFixedSpace (pResidual 2 M) T o.c o.b).mkQ_surjective v
    have hx : p x ≠ 0 := by
      intro hh
      exact hu ((Submodule.Quotient.mk_eq_zero _).mpr (hpk ▸ hh))
    have hy : p y ≠ 0 := by
      intro hh
      exact hv ((Submodule.Quotient.mk_eq_zero _).mpr (hpk ▸ hh))
    obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
      (p x) (p y) hx hy
    obtain ⟨m,hm⟩ := hqonto (a.symm g.val)
    refine ⟨m,?_⟩
    change (orbitFixedSpace (pResidual 2 M) T o.c o.b).mkQ
      (orbitRepresentation T o.c o.b m x) =
      (orbitFixedSpace (pResidual 2 M) T o.c o.b).mkQ y
    apply (Submodule.Quotient.eq _).mpr
    rw [←hpk]
    change p (orbitRepresentation T o.c o.b m x-y) = 0
    have ha : orbitRepresentation T o.c o.b m x = ρ (q m) x :=
      congrArg (fun r : Representation (ZMod 2) (⊤ : Subgroup M)
        (Additive (OrbitQuotient T o.c o.b)) => r m x) hcomp.symm
    rw [map_sub,ha,hm,he,a.apply_symm_apply,hg,sub_self]
  · have hfix0 : fixedSpace (orbitRepresentation T o.c o.b)
        ((pResidual 2 M).subgroupOf ⊤) ≤
        subspaceCommutator (orbitRepresentation T o.c o.b) ⊤
          ((o.opposite.comap (embedM T)).subgroupOf ⊤) := by
      rw [←hcomp,fixedSpace_comp_map,subspaceCommutator_comp_map,hK,hB]
      exact hfix
    have hh := (orbitSection T o.c o.b o.layer_le).fixedPreimage_le_commutator_sup_of_fixed_le_moved
      (pResidual 2 M) (o.opposite.comap (embedM T)) le_top le_top
      (by rw [normalizer_eq_top];exact le_top) hfix0
    have hZm : (orbitLayer T).map (embedM T) = Z T (alpha T) := map_comap_eq_self
      ((Z_le_stabilizer T (alpha T)).trans_eq (stabilizer_m_base T))
    have hh' := map_mono (f := embedM T) hh
    rw [Subgroup.map_sup,map_commutator,o.opposite_map,hZm] at hh'
    exact hh'

end AlternatingSixReconstruction.Exceptional.Exhaustion.CubicAction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
