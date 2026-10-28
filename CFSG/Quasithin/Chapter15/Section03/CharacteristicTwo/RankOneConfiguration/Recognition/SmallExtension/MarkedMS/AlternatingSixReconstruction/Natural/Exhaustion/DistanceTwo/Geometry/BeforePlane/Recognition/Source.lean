module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Assembly.Noncentral.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.FromModel

/-!
# Recognition for the preliminary favorable pair

The faithful orbit quotient and its elementary order-eight actor give the
natural fixed quotient whenever the orbit has full component movement.
The kernel displacement and involution argument use no assertion that the
orbit image equals the whole radical image. The possible central line is
retained in the literal fixed-space preimage.

Source: MS93 (3.6), printed p.871. The actual source application is in
Assembly.Preliminary.Source; plane movement remains its explicit premise.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geo : Geometry R}
  (o : PreliminaryPair R geo)

namespace PreliminaryPair

def Recognized : Prop :=
  letI := o.quotient_elementary
  (∀ u v, u ≠ 0 → v ≠ 0 → ∃ m : (⊤ : Subgroup M),
    orbitFixedQuotientRepresentation (pResidual 2 M) R o.c o.b o.layer_le m u = v) ∧
    (orbitFixedKernel (pResidual 2 M) R o.c o.b).map (embedM R) ≤
      ⁅criticalOrbit R o.c o.b,o.opposite⁆ ⊔ Z R (alpha R)

/-- Construct recognition without exposing its implementation to the cubic
cover application. Both clauses refer to the original fixed quotient. -/
theorem recognized_of_clauses :
    letI := o.quotient_elementary
    (∀ u v, u ≠ 0 → v ≠ 0 → ∃ m : (⊤ : Subgroup M),
      orbitFixedQuotientRepresentation (pResidual 2 M) R o.c o.b o.layer_le m u = v) →
    (orbitFixedKernel (pResidual 2 M) R o.c o.b).map (embedM R) ≤
      ⁅criticalOrbit R o.c o.b,o.opposite⁆ ⊔ Z R (alpha R) → o.Recognized :=
  fun ht hf => ⟨ht,hf⟩

end PreliminaryPair
namespace ImageModel
variable {o} (s : ImageModel o)

include s in
theorem recognized_of_full_movement
    (hsq : IsSQTK KnownSimple.IsKnownSimple M)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hm : criticalOrbitNative R o.c o.b =
      ⁅pResidual 2 M,criticalOrbitNative R o.c o.b⁆ ⊔ orbitLayer R) :
    o.Recognized := by
  let := o.quotient_elementary
  let e := s.fullEquiv hp hQR
  let σ := s.action.comp e.symm.toMonoidHom
  let q : (⊤ : Subgroup M) →* Equiv.Perm (Fin 6) :=
    e.toMonoidHom.comp s.topProjection
  let B := s.actor.map e.toMonoidHom
  have hq : q = s.projection.comp (⊤ : Subgroup M).subtype := rfl
  have honto : Function.Surjective q := e.surjective.comp s.topProjection_onto
  have hcomp : σ.comp q = orbitRepresentation R o.c o.b := by
    apply MonoidHom.ext
    intro m
    change s.action (e.symm (e (s.topProjection m))) = _
    rw [e.symm_apply_apply]
    exact s.action_projection m
  have hK : ((pResidual 2 M).subgroupOf ⊤).map q = alternatingGroup (Fin 6) := by
    rw [hq,←map_map,map_subgroupOf_eq_of_le (show pResidual 2 M ≤ ⊤ from le_top)]
    exact s.component_image
  have hB : ((o.opposite.comap (embedM R)).subgroupOf ⊤).map q = B := by
    rw [show q = e.toMonoidHom.comp s.topProjection from rfl,←map_map,s.actor_map]
  have hcard : Nat.card B = 8 := by
    rw [show Nat.card B = Nat.card s.actor from card_map_of_injective e.injective,
      s.actor_card hp hQR]
    exact (s.strict_indices hp hQR).1
  let := s.actor_elementary hp hQR
  let : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hcod : fixedCodim σ B = fixedCodim s.action s.actor := by
    unfold fixedCodim
    rw [fixedSpace_comp_map,map_map]
    have he : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact e.symm_apply_apply x
    rw [he,map_id]
  have hc : fixedCodim σ B = 2 := by
    have hh := (s.strict_indices hp hQR).2.2
    rw [s.fixed_index,←hcod] at hh
    have he : 2 ^ fixedCodim σ B = 2 ^ 2 := hh
    exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
  have hmove : subspaceCommutator σ ⊤ (alternatingGroup (Fin 6)) = ⊤ := by
    have hh := (orbitSection R o.c o.b o.layer_le).subspaceCommutator_eq_top_of_movement
      (pResidual 2 M) le_top hm
    rw [←hcomp,subspaceCommutator_comp_map,hK] at hh
    exact hh
  have hquot : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hsq.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 M) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  let eq : M ⧸ pCore 2 M ≃* Equiv.Perm (Fin 6) :=
    (QuotientGroup.quotientMulEquivOfEq s.kernel.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective s.projection (s.onto hp hQR))
  have hsqA := (IsSQTK.knownSimple_of_equiv eq hquot).subgroup (alternatingGroup (Fin 6))
  obtain ⟨f,p,_,hk,he,hfix⟩ :=
    ChapterB.QuasisimpleSource.SourceCompletion.symmetricSix_natural_quotient_fixed_le_moved
      σ (s.action_injective.comp e.symm.injective) hsqA B hcard hc
      (Recognition.PermutationModel.elementary_eight_odd B hcard) hmove
  have hfixed : fixedSpace σ (alternatingGroup (Fin 6)) =
      orbitFixedSpace (pResidual 2 M) R o.c o.b := by
    rw [←hK,←fixedSpace_comp_map,hcomp]
    ext v
    constructor
    · intro hv k
      exact hv ⟨⟨k,mem_top _⟩,k.property⟩
    · intro hv k
      exact hv ⟨k.val.val,k.property⟩
  constructor
  · rw [hfixed] at hk
    intro u v hu hv
    obtain ⟨x,rfl⟩ := (orbitFixedSpace (pResidual 2 M) R o.c o.b).mkQ_surjective u
    obtain ⟨y,rfl⟩ := (orbitFixedSpace (pResidual 2 M) R o.c o.b).mkQ_surjective v
    have hx : p x ≠ 0 := by
      intro hh
      exact hu ((Submodule.Quotient.mk_eq_zero _).mpr (hk ▸ hh))
    have hy : p y ≠ 0 := by
      intro hh
      exact hv ((Submodule.Quotient.mk_eq_zero _).mpr (hk ▸ hh))
    obtain ⟨g,hg⟩ := Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport.transitive_nonzero
      (p x) (p y) hx hy
    obtain ⟨m,hm⟩ := honto (f.symm g.val)
    refine ⟨m,?_⟩
    change (orbitFixedSpace (pResidual 2 M) R o.c o.b).mkQ
      (orbitRepresentation R o.c o.b m x) =
      (orbitFixedSpace (pResidual 2 M) R o.c o.b).mkQ y
    apply (Submodule.Quotient.eq _).mpr
    rw [←hk]
    change p (orbitRepresentation R o.c o.b m x-y) = 0
    have ha : orbitRepresentation R o.c o.b m x = σ (q m) x :=
      congrArg (fun r : Representation (ZMod 2) (⊤ : Subgroup M)
        (Additive (OrbitQuotient R o.c o.b)) => r m x) hcomp.symm
    rw [map_sub,ha,hm,he,f.apply_symm_apply,hg,sub_self]
  · have hfix0 : fixedSpace (orbitRepresentation R o.c o.b)
        ((pResidual 2 M).subgroupOf ⊤) ≤
        subspaceCommutator (orbitRepresentation R o.c o.b) ⊤
          ((o.opposite.comap (embedM R)).subgroupOf ⊤) := by
      rw [←hcomp,fixedSpace_comp_map,subspaceCommutator_comp_map,hK,hB]
      exact hfix
    have hh := (orbitSection R o.c o.b o.layer_le).fixedPreimage_le_commutator_sup_of_fixed_le_moved
      (pResidual 2 M) (o.opposite.comap (embedM R)) le_top le_top
      (by rw [normalizer_eq_top];exact le_top) hfix0
    have hZm : (orbitLayer R).map (embedM R) = Z R (alpha R) := map_comap_eq_self
      ((Z_le_stabilizer R (alpha R)).trans_eq (stabilizer_m_base R))
    have hh' := map_mono (f := embedM R) hh
    rw [Subgroup.map_sup,map_commutator,o.opposite_map,hZm] at hh'
    exact hh'

end ImageModel
namespace PreliminaryPair
variable (o : PreliminaryPair R geo)

theorem fixed_elementary (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hel : IsElementaryAbelian 2 (⁅criticalOrbit R o.c o.b,o.opposite⁆ : Subgroup (FreeAmalgam R)))
    (hD : (orbitFixedKernel (pResidual 2 M) R o.c o.b).map (embedM R) ≤
      ⁅criticalOrbit R o.c o.b, o.opposite⁆ ⊔ Z R (alpha R)) :
    IsElementaryAbelian 2 (orbitFixedKernel (pResidual 2 M) R o.c o.b) := by
  let A := criticalOrbit R o.c o.b
  have hd : (cosetGraph R).dist (alpha R) o.c = 2 :=
    o.critical.1.trans ((geo.distance_constant _ rfl).trans o.distance_two)
  have hAQ : A ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact map_mono o.orbit_le_core
  have hBA : o.opposite ≤ normalizer (A : Set (FreeAmalgam R)) :=
    (o.opposite_le.trans (Q_le_stabilizer_of_dist_two R o.c (alpha R) (critical_endpoint_color R (alpha R) rfl _ o.critical)
      (by rwa [SimpleGraph.dist_comm]))).trans
      (ChapterC.NaturalSixControl.SymplecticSetup.Source.criticalOrbit_normalized o.c o.b)
  have hcomm : ⁅A, o.opposite⁆ ≤ A :=
    le_normalizer_iff_commutator_le_left.mp hBA
  let := hel
  let := Z_elementary_of_positive R geo (alpha R) rfl (by
    rw [geo.distance_constant (alpha R) rfl]
    change 0 < geo.b R
    rw [o.distance_two]
    decide)
  have hZC : Z R (alpha R) ≤ centralizer ((⁅A, o.opposite⁆ : Subgroup (FreeAmalgam R)) : Set _) :=
    (commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q R (alpha R) rfl)).trans
      (centralizer_le (hcomm.trans hAQ))
  let : IsElementaryAbelian 2 (⁅A, o.opposite⁆ ⊔ Z R (alpha R) : Subgroup (FreeAmalgam R)) :=
    IsElementaryAbelian.sup_of_le_centralizer hZC
  let : IsElementaryAbelian 2 ((orbitFixedKernel (pResidual 2 M) R o.c o.b).map (embedM R)) :=
    IsElementaryAbelian.of_le hD
  let e := (orbitFixedKernel (pResidual 2 M) R o.c o.b).equivMapOfInjective (embedM R) (embedM_injective R)
  exact IsElementaryAbelian.of_injective e.toMonoidHom e.injective

theorem elementary_of_recognized (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hel : IsElementaryAbelian 2 (⁅criticalOrbit R o.c o.b,o.opposite⁆ : Subgroup (FreeAmalgam R)))
    (hcentral : orbitFixedKernel (pResidual 2 M) R o.c o.b ≤
      centralizer (criticalOrbitNative R o.c o.b : Set M))
    (hr : o.Recognized) : IsElementaryAbelian 2 (criticalOrbitNative R o.c o.b) := by
  let := o.quotient_elementary
  obtain ⟨htrans, hD⟩ := hr
  let s := canonicalOrbitFixedSection (pResidual 2 M) R o.c o.b o.layer_le
  let := o.fixed_elementary hp hQR hel hD
  let := o.plane_elementary
  have hele : IsElementaryAbelian 2 (criticalOrbitNative R o.c o.b) := by
    apply s.elementary_of_transitive hcentral
    · exact fun y hy => elemPow_eq_one_of_isElementaryAbelian y hy
    · obtain ⟨y, hy, hny⟩ := Set.not_subset.mp o.plane_not_fixed
      have hyA : y ∈ criticalOrbitNative R o.c o.b := le_normalClosure hy
      refine ⟨⟨y, hyA⟩, ?_, ?_⟩
      · apply Subtype.ext
        change y ^ 2 = 1
        apply embedM_injective R
        rw [map_pow, map_one]
        exact elemPow_eq_one_of_isElementaryAbelian (A := criticalPlane R o.c o.b) _ hy
      · exact fun he => hny ((s.coordinates_eq_one_iff _).mp he)
    · exact htrans
  exact hele

/-- Recognition contradicts movement of the literal generating plane. -/
theorem false_of_recognized (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hel : IsElementaryAbelian 2 (⁅criticalOrbit R o.c o.b,o.opposite⁆ : Subgroup (FreeAmalgam R)))
    (hcentral : orbitFixedKernel (pResidual 2 M) R o.c o.b ≤
      centralizer (criticalOrbitNative R o.c o.b : Set M))
    (hm : ⁅criticalOrbit R o.c o.b,criticalPlane R o.c o.b⁆ ≠ ⊥)
    (hr : o.Recognized) : False := by
  let := o.elementary_of_recognized hp hQR hel hcentral hr
  apply hm
  apply le_bot_iff.mp
  apply (commutator_mono le_rfl (criticalPlane_le_orbit geo o.distance_two o.critical o.b)).trans
  change ⁅(criticalOrbitNative R o.c o.b).map (embedM R),
    (criticalOrbitNative R o.c o.b).map (embedM R)⁆ ≤ ⊥
  rw [←map_commutator,commutator_self_eq_bot_iff.mpr inferInstance,Subgroup.map_bot]

end PreliminaryPair
end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.BeforePlane
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
