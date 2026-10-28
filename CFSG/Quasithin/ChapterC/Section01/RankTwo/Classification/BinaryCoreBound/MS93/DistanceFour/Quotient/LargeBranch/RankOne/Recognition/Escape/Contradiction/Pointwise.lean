module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Fixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Transport
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy
public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Pointwise involution displacement from the actual orbit span

The moving orbit span has nontrivial two-group image in the local SL3(2)
quotient. Choose an involution in that image, without requiring an involutory
lift. Its displacement on the star has order at most four: the literal
neighbor bound is transported to alpha, and the starred intersection replaces
the radius-center denominator by Z_alpha. The radius splits into the star and
the globally fixed B_alpha/Z_alpha, so the same rank bound holds on the full
radius quotient. Actual matrix conjugacy transfers it to every involution.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(4), printed p.911, using (1)--(3), pp.910--911.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

omit [Finite M] in
private theorem involution_rank_eq
    (d : LayerModule source (V R (alpha R))) (t a : SL)
    (ht : orderOf t = 2) (ha : orderOf a = 2) :
    Module.finrank (ZMod 2) (LinearMap.range (d.representation t - LinearMap.id)) =
      Module.finrank (ZMod 2) (LinearMap.range (d.representation a - LinearMap.id)) := by
  let e := Matrix.PSL3Two.equiv
  obtain ⟨g, hg⟩ := Matrix.PSL3Two.involutions_conjugate (e t) (e a)
    ((e.orderOf_eq t).trans ht) ((e.orderOf_eq a).trans ha)
  have he : e.symm g * t * (e.symm g)⁻¹ = a := by
    apply e.injective
    simpa only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] using hg
  calc
    Module.finrank (ZMod 2) (LinearMap.range (d.representation t - LinearMap.id)) =
        Module.finrank (ZMod 2) (LinearMap.range
          (d.representation (e.symm g * t * (e.symm g)⁻¹) - LinearMap.id)) := by
      rw [← fixedCodim_zpowers_eq_displacement_rank,
        ← fixedCodim_zpowers_eq_displacement_rank, fixedCodim_zpowers_conj]
    _ = _ := by rw [he]

private theorem involution_rank_le_of_base_subgroup
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (K : Subgroup M) (hKR : K ≤ R)
    (hmove : ⁅Z R (alpha R), K.map (embedM R)⁆ ≠ ⊥)
    (hdisp : (B R (alpha R) (geometry.Z_normal _)).relIndex
      ⁅K.map (embedM R), V R (alpha R)⁆ ≤ 4)
    (d : LayerModule source (V R (alpha R))) :
    ∀ t : SL, orderOf t = 2 →
      Module.finrank (ZMod 2) (LinearMap.range (d.representation t - LinearMap.id)) ≤ 2 := by
  let A := K.map source.projection
  have hA : IsPGroup 2 A := (source.two_group.to_le hKR).map source.projection
  have hAn : A ≠ ⊥ := by
    intro he
    have hKQ : K ≤ pCore 2 M := by
      simpa only [source.projection_kernel] using (Subgroup.map_eq_bot_iff K).mp he
    apply hmove
    apply bot_unique
    apply (commutator_mono le_rfl (map_mono hKQ)).trans
    rw [← Q_alpha R source.two_group source.core_le]
    exact (geometry.centralizes (alpha R) rfl).le
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAn
  have hAc : 2 ∣ Nat.card A := by
    rcases hA.card_eq_or_dvd with he | he
    · exact (Finite.one_lt_card.ne' he).elim
    · exact he
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 hAc
  have ha' : orderOf (a : SL) = 2 := (Subgroup.orderOf_coe a).trans ha
  let S := VStar R geometry (alpha R) (beta R)
  let D := ⁅S, K.map (embedM R)⁆
  let F := ⁅K.map (embedM R), V R (alpha R)⁆
  have hKG : K.map (embedM R) ≤ stabilizer R (alpha R) := by
    have hQG : Q R (beta R) ≤ stabilizer R (alpha R) :=
      fun _ hx => hx.2 _ (adjacent_symm R (base_adjacent R))
    exact (map_mono hKR).trans ((Q_beta R).ge.trans hQG)
  have hKN : K.map (embedM R) ≤ normalizer S :=
    hKG.trans (Flags.star_normalized geometry _ _)
  have hDS : D ≤ S := le_normalizer_iff_commutator_le_left.mp hKN
  have hDF : D ≤ F := by
    dsimp only [D, F]
    rw [commutator_comm (K.map (embedM R))]
    exact commutator_mono (Flags.star_le_radius geometry _ _) le_rfl
  have hFV : F ≤ V R (alpha R) := le_normalizer_iff_commutator_le_right.mp
    (hKG.trans (DistanceEight.V_normalized R _))
  let : Finite (V R (alpha R)) := Early.finite_radius common _ rfl
  let : Finite F := Finite.of_injective (inclusion hFV) (inclusion_injective _)
  have hi : (B R (alpha R) (geometry.Z_normal _)).relIndex D ≤ 4 :=
    (relIndex_le_of_le_right hDF (show
      (B R (alpha R) (geometry.Z_normal _)).relIndex F ≠ 0 from
        Subgroup.index_ne_zero_of_finite)).trans hdisp
  have hDB : D ⊓ B R (alpha R) (geometry.Z_normal _) = D ⊓ Z R (alpha R) := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, (radius.star_intersection (alpha R) (beta R) rfl (base_adjacent R)).le
        ⟨hDS hx.1, hx.2⟩⟩
    · exact inf_le_inf_left _ (Flags.Z_le_B geometry (alpha R)
        (geometry.V_local (alpha R) rfl common.large_distance))
  have hindex : (Z R (alpha R)).relIndex D ≤ 4 := by
    rw [← inf_relIndex_left D, ← hDB, inf_relIndex_left]
    exact hi
  have hdim : Module.finrank (ZMod 2) (d.subspace D) ≤ 2 := by
    rw [d.subspace_relIndex D (hDS.trans (Flags.star_le_radius geometry _ _))] at hindex
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hindex
  have hZS : Z R (alpha R) ≤ S :=
    (radius.star_intersection (alpha R) (beta R) rfl (base_adjacent R)).ge.trans inf_le_left
  have hpre : d.preimage (d.subspace S) = S := by
    rw [Seed.LayerModule.preimage_subspace_eq d S (Flags.star_le_radius geometry _ _),
      sup_eq_right.mpr (inf_le_left.trans hZS)]
  have hm := d.subspace_commutator_preimage (d.subspace S) K
    (hKG.trans (DistanceEight.V_normalized R _))
  rw [hpre] at hm
  have harange : LinearMap.range (d.representation (a : SL) - LinearMap.id) ≤
      d.subspace D := by
    rintro _ ⟨v, rfl⟩
    obtain ⟨b, hb, w, hw, hv⟩ := radius_split common radius d v
    have hwdisp : d.representation (a : SL) w - w ∈ d.subspace D := by
      rw [hm]
      exact Submodule.subset_span ⟨(a : SL), a.property, w, hw, rfl⟩
    change d.representation (a : SL) v - v ∈ _
    rw [← hv, map_add, radius_B_fixed common radius d b hb (a : SL)]
    convert hwdisp using 1
    abel
  have haRank := (Submodule.finrank_mono harange).trans hdim
  intro t ht
  rw [involution_rank_eq d t (a : SL) ht ha']
  exact haRank

/-- The literal orbit-span bound at a moving neighbor controls every matrix
involution on the full radius quotient V_alpha/Z_alpha. No order-two lift is used. -/
theorem involution_displacement_rank_le_two_of_span_neighbor
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (s : CriticalSegment geometry) (μ : Vertex R)
    (hμ : Adjacent R (beta R) μ)
    (hmove : ⁅Z R μ, orbitSpan s.middle⁆ ≠ ⊥)
    (hdisp : (B R μ (geometry.Z_normal μ)).relIndex
      ⁅orbitSpan s.middle, V R μ⁆ ≤ 4)
    (d : LayerModule source (V R (alpha R))) :
    ∀ t : SL, orderOf t = 2 →
      Module.finrank (ZMod 2) (LinearMap.range (d.representation t - LinearMap.id)) ≤ 2 := by
  have hc : color R μ = false := by
    have hn := adjacent_color_ne R hμ
    have hb : color R (beta R) = true := rfl
    cases he : color R μ <;> simp_all
  obtain ⟨g, hg, hga⟩ := stabilizer_transitive_neighbors R (beta R) hμ
    (adjacent_symm R (base_adjacent R))
  change act R g μ = alpha R at hga
  have hgβ : act R g (beta R) = beta R := hg
  let e := (MulAut.conj g⁻¹).toMonoidHom
  let H := (orbitSpan s.middle).map e
  have hHQ : H ≤ Q R (beta R) := by
    have hH : orbitSpan s.middle ≤ Q R (beta R) :=
      (orbitSpan_le_radius _ ((cosetGraph R).dist_comm.trans s.first_distance).le).trans
        ((Early.radius_le_Q common _ rfl).trans (Q_le_adjacent_h R rfl (base_adjacent R)))
    have hQ : (Q R (beta R)).map e = Q R (beta R) := by
      rw [← Q_act, hgβ]
    exact (map_mono hH).trans_eq hQ
  let K := H.comap (embedM R)
  have hKR : K ≤ R := by
    have hh := comap_mono (f := embedM R) hHQ
    rw [Q_beta R, comap_map_eq_self_of_injective (embedM_injective R)] at hh
    exact hh
  have hKH : K.map (embedM R) = H := by
    apply map_comap_eq_self
    exact hHQ.trans ((Q_beta R).le.trans (map_le_range _ _))
  have hZ : Z R (alpha R) = (Z R μ).map e := by rw [← Z_act, hga]
  have hV : V R (alpha R) = (V R μ).map e := by rw [← V_act, hga]
  have hB : B R (alpha R) (geometry.Z_normal _) =
      (B R μ (geometry.Z_normal _)).map e := by
    simpa only [hga] using Flags.RankOne.B_act geometry radius.toEarlyFacts g μ hc
  apply involution_rank_le_of_base_subgroup common radius K hKR
  · rw [hKH, hZ, ← map_commutator]
    exact fun he => hmove ((map_eq_bot_iff_of_injective _ (MulAut.conj g⁻¹).injective).mp he)
  · rw [hKH, hB, hV, ← map_commutator,
      relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hdisp

/-- Under the clause-(4) containment assumption, the existing moving-neighbor
selector and the source displacement producer discharge every geometric input
to the pointwise rank bound. -/
theorem involution_displacement_rank_le_two_of_span_contained
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (d : LayerModule source (V R (alpha R))) :
    ∀ t : SL, orderOf t = 2 →
      Module.finrank (ZMod 2) (LinearMap.range (d.representation t - LinearMap.id)) ≤ 2 := by
  obtain ⟨μ, _, hμ, hmove, _, hdisp⟩ :=
    exists_moving_neighbor_with_span_displacement common radius hb s hbc hspan
  exact involution_displacement_rank_le_two_of_span_neighbor common radius s μ hμ hmove hdisp d

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
