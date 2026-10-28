module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualMovers
public import Theory.SpecificGroups.SymplecticFour.NeighborMoverCrossing

/-!
# Unequal neighboring movers cross a parabolic two-core

In the original replacement vertex marking, the actual edge image is
Sylow-normal and normalizes each neighboring mover. The full U-index of
an unequal mover is q cubed, and its quotient order is at least q squared.
The coordinate crossing alternative therefore applies. Its exceptional
point-radical edge is impossible: the complete small-mover family lifts
through the full Q-kernel and makes the original join equal the whole edge;
equal neighboring orders then contradict inequality of the movers.

Pulling back the resulting crossing uses the exact two-cores of the full
parabolic preimages. The Q-kernel and every central attachment are retained.
This supplies a different marked point of the same plane, not yet a point
compatible with the endpoint selection in ContainedPointProjection.
Source: MS93 (5.5), printed p.916. The compatible selector, individual/paired
generation, selected paths and terminal distance exclusions remain needed.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit CentralRootGeometry.SmallMovers
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
private theorem point_image_forces_edge_join
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hTf : ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent)
    (hindex : ∀ A : Subgroup (stabilizer d.radical a),
      (centralizer (A : Set (stabilizer d.radical a))).relIndex
        ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
        2 ^ fixedCodim (restrictScalars (k := ZMod 2)
          (symplecticNatural (k := B.Carrier) 2)) (A.map f))
    (hpoint : (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f).subgroupOf
      unipotent = CentralRootGeometry.wing false) :
    Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2) = Q d.radical t := by
  let S := stabilizer d.radical a
  let U₀ := (U d.radical a).subgroupOf S
  let T := (Q d.radical t).subgroupOf S
  let J := Subgroup.SmallMover.join U₀ f.ker T (Nat.card B.Carrier^2)
  let := finite_stabilizer d.radical a
  have hUS : U d.radical a ≤ S := (U_le_Z a).trans (Z_le_stabilizer d.radical a)
  have hTS : Q d.radical t ≤ S := fun _ hx => hx.2 a (adjacent_symm d.radical hat)
  have hBF : Nat.card B.Carrier = Nat.card F := by rw [B.card_eq,hB,h.field_card]
  have hjoin : J.map S.subtype = Subgroup.SmallMover.join (U d.radical a)
      (Q d.radical a) (Q d.radical t) (Nat.card F^2) := by
    rw [Subgroup.SmallMover.join_map S.subtype S.subtype_injective,
      map_subgroupOf_eq_of_le hUS,hfQ,map_subgroupOf_eq_of_le hTS,hBF]
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective _).symm
  obtain ⟨j,hj,hjr,hjR,hjQ,hjU⟩ := Sp4Four.LocalPackage.edge_coordinates d.radical
    (h.replacement_two_group d) (h.replacement_core_le d) ha hat
  have hQT : Q d.radical a ≤ Q d.radical t := by
    rw [←hjQ,←hjR]
    exact map_mono (h.replacement_core_le d)
  have hkT : f.ker ≤ T := by rw [hQeq]; exact comap_mono hQT
  have hUK : U₀ ≤ centralizer (f.ker : Set S) := by
    intro u hu k hk
    apply Subtype.val_injective
    have hkQ : k.val ∈ Q d.radical a := hfQ ▸ mem_map_of_mem S.subtype hk
    exact ((commutator_eq_bot_iff_le_centralizer.mp (Z_centralizes_Q d.radical a ha))
      (U_le_Z a hu) k.val hkQ)
  have hidx : ∀ A : Subgroup S, A ≤ T →
      (centralizer (A : Set S)).relIndex U₀ =
        movingIndex (Degree.Quotient.coordinates f unipotent.subtype A) := by
    intro A hAT
    rw [hindex,←binary_movingIndex]
    change _ = 2 ^ fixedCodim ((restrictScalars (k := ZMod 2)
      (symplecticNatural (k := B.Carrier) 2)).comp unipotent.subtype)
        (Degree.Quotient.coordinates f unipotent.subtype A)
    rw [fixedCodim,fixedCodim,fixedSpace_comp_map,Degree.Quotient.coordinates_map]
    simpa only [range_subtype] using (map_mono hAT).trans hTf
  have hTi : T.map f ≤ unipotent.subtype.range := by simpa only [range_subtype] using hTf
  have hc := Degree.Quotient.coordinates_join U₀ T f unipotent.subtype
    unipotent.subtype_injective hkT hUK hTi hidx
  change Degree.Quotient.coordinates f unipotent.subtype J =
    Degree.join ((T.map f).subgroupOf unipotent) at hc
  rw [hpoint,Degree.join_point_wing] at hc
  have he : Degree.Quotient.coordinates f unipotent.subtype J =
      Degree.Quotient.coordinates f unipotent.subtype T := hc.trans hpoint.symm
  have hm := congrArg (Subgroup.map unipotent.subtype) he
  rw [Degree.Quotient.coordinates_map f unipotent.subtype J
    ((map_mono (Subgroup.SmallMover.join_le _ _ _ _)).trans hTi),
    Degree.Quotient.coordinates_map f unipotent.subtype T hTi] at hm
  have hkJ : f.ker ≤ J := Subgroup.SmallMover.kernel_le_join U₀ f.ker T _
    (Nat.one_le_pow _ _ Nat.card_pos) hkT hUK
  have he' := congrArg (Subgroup.comap f) hm
  rw [comap_map_eq_self hkJ,comap_map_eq_self hkT] at he'
  rw [←hjoin,he',map_subgroupOf_eq_of_le hTS]

/-- Every actual unequal neighboring mover crosses the two-core at a
different marked point of the plane. The noncontainment is in the original
vertex stabilizer, between literal parabolic preimage two-cores. -/
theorem Input.replacement_unequal_mover_parabolic_crossing_normalized
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        unipotent ≤ normalizer
          (((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f : Set (Sp B.Carrier)) ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        ∀ c : Vertex d.radical, Adjacent d.radical c t →
          let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)
          let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
            (Q d.radical t) (Nat.card F^2)
          E ≠ J →
            ∃ s : Sp B.Carrier, s ∈ planeLocal ∧ s ∉ pointParabolic ∧
              ¬ E.subgroupOf (stabilizer d.radical a) ⊓
                (planeParabolic.comap f).pCoreIn 2 ≤
                ((pointParabolic.map (MulAut.conj s).toMonoidHom).comap f).pCoreIn 2 := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,hall⟩ :=
    h.replacement_unequal_individual_coordinates d geometry hb ha hat
  refine ⟨B,hB,f,hf,hfQ,hTf,hTn,hindex,?_⟩
  intro c hct
  dsimp only
  let S := stabilizer d.radical a
  let T := (Q d.radical t).subgroupOf S
  let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
    (Q d.radical t) (Nat.card F^2)
  let E₀ := E.subgroupOf S
  let T₁ := (T.map f).subgroupOf unipotent
  let E₁ := (E₀.map f).subgroupOf unipotent
  let := finite_stabilizer d.radical a
  intro hne
  obtain ⟨hc,hEf,hEn,_,hfix,hquad⟩ := hall c hct hne
  have hET : E ≤ Q d.radical t := Subgroup.SmallMover.join_le _ _ _ _
  have hET₁ : E₁ ≤ T₁ := comap_mono (map_mono (comap_mono hET))
  have hTE₁ : T₁ ≤ normalizer (E₁ : Set (unipotent (F := B.Carrier))) :=
    (comap_mono hEn).trans ((E₀.map f).le_normalizer_comap unipotent.subtype)
  let : T₁.Normal := (normal_subgroupOf_iff_le_normalizer hTf).mpr hTn
  have hEc : Nat.card B.Carrier^2 ≤ Nat.card E₁ := by
    rw [←card_map_of_injective unipotent.subtype_injective,
      map_subgroupOf_eq_of_le hEf]
    exact hc
  have hout : ¬ E₁ ≤ CentralRootGeometry.wing true := by
    intro he
    have hi := movingIndex_le_field_sq_of_le_wing E₁ he
    rw [movingIndex,hfix] at hi
    have hdim := (point B.Carrier).finrank_quotient_add_finrank
    rw [finrank_point] at hdim
    have hv : Module.finrank B.Carrier
        (Theory.SpecificGroups.SymplecticFour.Vector B.Carrier) = 4 := by
      simp [Theory.SpecificGroups.SymplecticFour.Vector]
    rw [hv] at hdim
    have hd : Module.finrank B.Carrier
        (Theory.SpecificGroups.SymplecticFour.Vector B.Carrier ⧸ point B.Carrier) = 3 := by omega
    rw [hd] at hi
    have hq : 1 < Nat.card B.Carrier := Finite.one_lt_card
    have hlt : Nat.card B.Carrier^2 < Nat.card B.Carrier^3 := (pow_lt_pow_iff_right₀ hq).mpr (by decide)
    exact hlt.not_ge hi
  rcases NeighborMoverCrossing.parabolic_crossing_or_point B.card_eq
    (by rw [hB]; exact h.nonbinary) T₁ E₁ hET₁ hTE₁ hEc hout with
      ⟨s,hs,hsp,hcross⟩ | hpoint
  · refine ⟨s,hs,hsp,?_⟩
    have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
      rw [←hfQ]
      exact (comap_map_eq_self_of_injective S.subtype_injective _).symm
    have hk : IsPGroup 2 f.ker := by
      rw [hQeq]
      exact (Q_isPGroup d.radical (h.replacement_two_group d)
        (h.replacement_core_le d) a ha).comap_subtype
    have hcore (P : Subgroup (Sp B.Carrier)) :
        (P.comap f).pCoreIn 2 = (P.pCoreIn 2).comap f := by
      have hh := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 f (P.comap f) hk
      rw [map_comap_eq_self_of_surjective hf] at hh
      exact hh.symm.trans (inf_eq_right.mpr (comap_mono (pCoreIn_le 2 P)))
    rw [hcore,hcore]
    intro hle
    apply hcross
    rw [map_subgroupOf_eq_of_le hEf]
    rintro y ⟨hy,hyp⟩
    obtain ⟨x,hx,rfl⟩ := hy
    exact hle ⟨hx,hyp⟩
  · have hJT := point_image_forces_edge_join h d ha hat B hB f hfQ hTf hindex hpoint
    let := finite_stabilizer d.radical t
    let : Finite (Q d.radical t) := Finite.of_injective
      (inclusion (show Q d.radical t ≤ stabilizer d.radical t from fun _ hx => hx.1))
      (inclusion_injective _)
    have hcard := small_mover_neighbor_card_eq d.radical hat hct (Nat.card F^2)
    rw [hJT] at hcard
    have hEq : E=Q d.radical t := eq_of_le_of_card_ge hET hcard.le
    exact (hne (hEq.trans hJT.symm)).elim

/-- The original interface, with its quotient marking and all conclusions preserved. -/
theorem Input.replacement_unequal_mover_parabolic_crossing
    (geometry : Geometry d.radical) (hb : 4 ≤ geometry.b d.radical)
    {a t : Vertex d.radical} (ha : color d.radical a = false)
    (hat : Adjacent d.radical a t) :
    ∃ B : BinaryField, B.degree = n ∧
      ∃ f : stabilizer d.radical a →* Sp B.Carrier,
        Function.Surjective f ∧ f.ker.map (stabilizer d.radical a).subtype = Q d.radical a ∧
        ((Q d.radical t).subgroupOf (stabilizer d.radical a)).map f ≤ unipotent ∧
        (∀ A : Subgroup (stabilizer d.radical a),
          (centralizer (A : Set (stabilizer d.radical a))).relIndex
            ((U d.radical a).subgroupOf (stabilizer d.radical a)) =
            2 ^ fixedCodim (restrictScalars (k := ZMod 2)
              (symplecticNatural (k := B.Carrier) 2)) (A.map f)) ∧
        ∀ c : Vertex d.radical, Adjacent d.radical c t →
          let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
            (Q d.radical t) (Nat.card F^2)
          let E := Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
            (Q d.radical t) (Nat.card F^2)
          E ≠ J →
            ∃ s : Sp B.Carrier, s ∈ planeLocal ∧ s ∉ pointParabolic ∧
              ¬ E.subgroupOf (stabilizer d.radical a) ⊓
                (planeParabolic.comap f).pCoreIn 2 ≤
                ((pointParabolic.map (MulAut.conj s).toMonoidHom).comap f).pCoreIn 2 := by
  obtain ⟨B,hB,f,hf,hfQ,hTf,_hTn,hindex,hall⟩ :=
    h.replacement_unequal_mover_parabolic_crossing_normalized d geometry hb ha hat
  exact ⟨B,hB,f,hf,hfQ,hTf,hindex,hall⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
