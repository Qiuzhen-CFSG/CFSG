module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Action
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Recognition.Projection

/-!
# Full images from the strict pair and an abelian edge quotient

The actual orbit images have order eight. An abelian two-subgroup of S₆ has
order at most eight, so the edge quotient cannot be larger. Equality of the
literal relative indices then fills both edge quotients. No identification
with a point core, and no natural subgroup complement, enters this argument.

The remaining radical-derived containment is the existing LocalImageInput
source obligation. Source: MS93 (3.6), printed p.871.
-/

@[expose] public noncomputable section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates

private theorem abelian_two_subgroup_card_le_eight (A : Subgroup (Equiv.Perm (Fin 6)))
    [IsMulCommutative A] (hp : IsPGroup 2 A) : Nat.card A ≤ 8 := by
  obtain ⟨P,hP⟩ := hp.exists_le_sylow
  have hPc : Nat.card (P : Subgroup (Equiv.Perm (Fin 6))) = 16 := by
    rw [P.card_eq_multiplicity,Nat.card_perm,Nat.card_fin]
    decide +kernel
  have hAc : Nat.card A ≤ 16 := (card_le_of_le hP).trans_eq hPc
  have hne : Nat.card A ≠ 16 := by
    intro hc
    let Q : Sylow 2 (Equiv.Perm (Fin 6)) := Sylow.ofCard A (by
      rw [hc,Nat.card_perm,Nat.card_fin]
      decide +kernel)
    exact alternatingGroup.SixSubgroupObstructions.not_injective_of_sylow_involutions_commute Q
      (by
        change ∀ a b : A, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b
        intro a b _ _
        exact mul_comm a b)
      (alternatingGroup (Fin 6)).subtype Subtype.coe_injective
  obtain ⟨n,hn⟩ := hp.exists_card_eq
  have hn4 : n < 4 := by
    apply (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp
    change 2 ^ n < 16
    omega
  rw [hn]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 3)

private theorem sup_eq_of_relIndex_eq {G : Type*} [Group G]
    (A N P : Subgroup G) (hAP : A ≤ P) (hNP : N ≤ P)
    (hn : P ≤ normalizer (N : Set G))
    (hindex : N.relIndex A = N.relIndex P) (hne : N.relIndex P ≠ 0) : A ⊔ N = P := by
  let C := N.subgroupOf P
  let D := A.subgroupOf P
  let : C.Normal := normal_subgroupOf_of_le_normalizer hn
  have hrel : C.relIndex D = N.relIndex P := (relIndex_subgroupOf hAP).trans hindex
  have hi : C.relIndex (D ⊔ C) = N.relIndex P := by
    rw [relIndex_sup_right]
    exact hrel
  have hmul := relIndex_mul_index (show C ≤ D ⊔ C from le_sup_right)
  rw [hi] at hmul
  have htop : D ⊔ C = ⊤ := index_eq_one.mp (by
    change N.relIndex P * (D ⊔ C).index = N.relIndex P at hmul
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (by simpa using hmul))
  have hm := congrArg (Subgroup.map P.subtype) htop
  simpa only [Subgroup.map_sup,D,C,map_subgroupOf_eq_of_le hAP,
    map_subgroupOf_eq_of_le hNP,←MonoidHom.range_eq_map,range_subtype] using hm

variable {M : Type*} [Group M] [Finite M] {R : Subgroup M} {geo : Geometry R}

/-- Every adjacent pair has the original radical's literal relative index. -/
theorem edge_index (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    {a b : Vertex R} (ha : color R a = false) (hab : Adjacent R a b) :
    (Q R a).relIndex (Q R b) = (pCore 2 M).relIndex R := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R a b).mp hab
  · rcases hg with ⟨rfl,rfl⟩
    have hQa : Q R (mVertex R g) = (Q R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [alpha,act_mVertex,one_mul] using Q_act R g (alpha R)
    have hQb : Q R (hVertex R g) = (Q R (beta R)).map (MulAut.conj g⁻¹).toMonoidHom := by
      simpa only [beta,act_hVertex,one_mul] using Q_act R g (beta R)
    rw [hQa,hQb,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective,
      Q_alpha R hp hQR,Q_beta,relIndex_map_map_of_injective _ _ (embedM_injective R)]
  · rw [hg.1] at ha
    cases ha

/-- Full edge images follow from the proved strict orbit indices and the
abelian radical quotient, preserving the actual pair and both joins. -/
theorem images_full (o : EarlyPair R geo) (s : ImageModel o)
    (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    (hder : ⁅R,R⁆ ≤ pCore 2 M) :
    o.opposite ⊔ Q R (alpha R) = Q R o.b ∧
      criticalOrbit R o.c o.b ⊔ Q R o.c = Q R o.b := by
  let := o.quotient_elementary
  obtain ⟨hB8,hA8,_⟩ := s.strict_indices hp hQR
  have hzero : ⁅R.map s.projection,R.map s.projection⁆ = ⊥ := by
    rw [←map_commutator]
    apply le_bot_iff.mp
    apply (map_mono hder).trans
    rw [←s.kernel,map_le_iff_le_comap]
    exact le_rfl
  let : IsMulCommutative (R.map s.projection) := commutator_self_eq_bot_iff.mp hzero
  have hcard : (pCore 2 M).relIndex R ≤ 8 := by
    rw [←s.kernel,relIndex_ker]
    exact abelian_two_subgroup_card_le_eight _ (hp.map s.projection)
  have hpos : (pCore 2 M).relIndex R ≠ 0 := by
    rw [←s.kernel,relIndex_ker]
    exact Nat.card_pos.ne'
  have hedge (a : Vertex R) (ha : color R a = false) (hab : Adjacent R a o.b) :
      (Q R a).relIndex (Q R o.b) ≤ 8 ∧ (Q R a).relIndex (Q R o.b) ≠ 0 := by
    rw [edge_index hp hQR ha hab]
    exact ⟨hcard,hpos⟩
  have hcol := DistanceTwo.NaturalCore.edge_color o.adjacent_left
  have hc0 := critical_endpoint_color R (alpha R) rfl _ o.critical
  have hQab : Q R (alpha R) ≤ Q R o.b := Q_le_adjacent_h R hcol o.adjacent_left
  have hQcb : Q R o.c ≤ Q R o.b := Q_le_adjacent_h R hcol o.adjacent_right
  have hAQ : criticalOrbit R o.c o.b ≤ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact map_mono o.orbit_le_core
  have hAP := hAQ.trans hQab
  have hBP := o.opposite_le.trans hQcb
  obtain ⟨hha,hpa⟩ := hedge (alpha R) rfl o.adjacent_left
  obtain ⟨hhc,hpc⟩ := hedge o.c hc0 o.adjacent_right
  have hia := relIndex_le_of_le_right (H := Q R (alpha R)) hBP hpa
  have hic := relIndex_le_of_le_right (H := Q R o.c) hAP hpc
  rw [hB8] at hia
  rw [hA8] at hic
  refine ⟨?_,?_⟩
  · exact sup_eq_of_relIndex_eq _ _ _ hBP hQab
      ((show Q R o.b ≤ stabilizer R (alpha R) from
        fun _ hx => hx.2 _ (adjacent_symm R o.adjacent_left)).trans (Q_normalized R (alpha R)))
      (hB8.trans (Nat.le_antisymm hha hia).symm) hpa
  · exact sup_eq_of_relIndex_eq _ _ _ hAP hQcb
      ((show Q R o.b ≤ stabilizer R o.c from
        fun _ hx => hx.2 _ (adjacent_symm R o.adjacent_right)).trans (Q_normalized R o.c))
      (hA8.trans (Nat.le_antisymm hhc hic).symm) hpc

universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)

/-- The original natural central quotient supplies the actual six-letter
marking; it preserves the possible order-32 cover. -/
def sourceImageModel (o : EarlyPair d.radical (replacementGeometry h d)) : ImageModel o where
  projection := Recognition.sourceProjection h e hz hn d
  kernel := Recognition.sourceProjection_kernel h e hz hn d
  component_image := Recognition.sourceProjection_component h e hz hn d

include e hz hn in
/-- Application to any literal ordered orbit of the original replacement. -/
theorem source_images_full
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map (Q d.radical (alpha d.radical)).subtype ⊔
        X d.radical (alpha d.radical))
    (hder : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup)
    (o : OrderedOrbit (replacementGeometry h d)) :
    o.opposite ⊔ Q d.radical (alpha d.radical) = Q d.radical o.b ∧
      criticalOrbit d.radical o.c o.b ⊔ Q d.radical o.c = Q d.radical o.b := by
  let a := earlyPair (replacement_radical_isPGroup h d) (replacement_core_le_radical h d)
    hl hb hlarge o
  exact images_full a (sourceImageModel h e hz hn d a)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hder

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
