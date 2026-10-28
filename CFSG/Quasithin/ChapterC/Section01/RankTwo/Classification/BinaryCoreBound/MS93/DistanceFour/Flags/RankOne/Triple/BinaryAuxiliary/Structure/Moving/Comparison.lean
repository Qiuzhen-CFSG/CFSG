module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Moving.Inputs

/-!
# The three-denominator index comparison on MS93 p.907

For C = [U_delta0,Y_lambda0], the first source inequality uses the inclusion
Z_beta <= Z_middle. Multiplicativity of relative indices factors the
Z_beta quotient through the original Z_alpha quotient; the correction
factor has order at most two by the earlier edge index. None of these
steps assumes normality in the infinite free amalgam.

The source reverse comparison between [U_delta0,Y_lambda0] modulo Z_alpha
and [U_delta0,U_lambda0] modulo Z_middle remains an explicit premise.
`midpoint_displacement_le_two` cancels those finite indices and obtains
the actual displacement bound modulo U_lambda0. Thus it isolates, rather
than assumes proved, the remaining geometric comparison.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), printed p.907,
first paragraph and displayed commutator inequality.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving

/-- The index cancellation behind the source displacement estimate. -/
theorem displacement_index_bound {G : Type*} [Group G]
    (C D A B T N : Subgroup G) [Finite C] (q : ℕ)
    (hBA : B ≤ A) (hBT : B ≤ T) (hTN : T ≤ N) (hD : D ≤ N ⊓ C)
    (hcomparison : A.relIndex C ≤ T.relIndex D)
    (hsmall : B.relIndex (A ⊓ C) ≤ q) : N.relIndex C ≤ q := by
  have hpos (K : Subgroup G) : 0 < K.relIndex C := by
    change 0 < Nat.card (C ⧸ K.subgroupOf C)
    exact Nat.card_pos
  let : Finite (N ⊓ C : Subgroup G) :=
    Finite.of_injective (inclusion inf_le_right) (inclusion_injective _)
  have hposNC : T.relIndex (N ⊓ C) ≠ 0 := by
    change Nat.card ((N ⊓ C : Subgroup G) ⧸ T.subgroupOf (N ⊓ C)) ≠ 0
    exact Nat.card_pos.ne'
  have h₁ := relIndex_inf_mul_relIndex B A C
  rw [inf_eq_left.mpr hBA] at h₁
  have h₂ := relIndex_inf_mul_relIndex T N C
  rw [inf_eq_left.mpr hTN] at h₂
  have hbound : A.relIndex C * N.relIndex C ≤ A.relIndex C * q := calc
    A.relIndex C * N.relIndex C ≤ T.relIndex D * N.relIndex C :=
      Nat.mul_le_mul_right _ hcomparison
    _ ≤ T.relIndex (N ⊓ C) * N.relIndex C :=
      Nat.mul_le_mul_right _ (relIndex_le_of_le_right hD hposNC)
    _ = T.relIndex C := h₂
    _ ≤ B.relIndex C := relIndex_le_of_le_left hBT (hpos B).ne'
    _ = A.relIndex C * B.relIndex (A ⊓ C) := by rw [← h₁, Nat.mul_comm]
    _ ≤ A.relIndex C * q := Nat.mul_le_mul_left _ hsmall
  exact Nat.le_of_mul_le_mul_left hbound (hpos A)

variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The first source comparison and its exact correction factor retain all
three original Z-denominators. This does not assert the harder reverse comparison. -/
theorem midpoint_index_comparison [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M)
    (hE : secondFlagLayer source i p.delta0 ≤
      (localFlagActor source (!i) e).map t.conjugation.toMonoidHom) :
    let C := ⁅secondFlagLayer source i p.delta0,
      (Y source i e).map t.conjugation.toMonoidHom⁆
    (Z R p.middle).relIndex C ≤ (Z R (beta R)).relIndex C ∧
      (Z R (beta R)).relIndex C = (Z R (alpha R)).relIndex C *
        (Z R (beta R)).relIndex (Z R (alpha R) ⊓ C) ∧
      (Z R (beta R)).relIndex (Z R (alpha R) ⊓ C) ≤ 2 := by
  let C := ⁅secondFlagLayer source i p.delta0,
    (Y source i e).map t.conjugation.toMonoidHom⁆
  have hnorm : (localFlagActor source (!i) e).map t.conjugation.toMonoidHom ≤
      normalizer ((Y source i e).map t.conjugation.toMonoidHom) :=
    (map_mono (Y_normalized source i e)).trans (le_normalizer_map _)
  have hCY : C ≤ (Y source i e).map t.conjugation.toMonoidHom :=
    le_normalizer_iff_commutator_le_right.mp (hE.trans hnorm)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (Y source i e) := Finite.of_injective
    (inclusion ((Y_le_radius source i e).trans (geometry.V_local _ rfl common.large_distance)))
    (inclusion_injective _)
  let : Finite ((Y source i e).map t.conjugation.toMonoidHom) :=
    Finite.of_equiv (Y source i e) (t.conjugation.subgroupMap (Y source i e)).toEquiv
  let : Finite C := Finite.of_injective (inclusion hCY) (inclusion_injective _)
  have hpos : (Z R (beta R)).relIndex C ≠ 0 := by
    change Nat.card (C ⧸ (Z R (beta R)).subgroupOf C) ≠ 0
    exact Nat.card_pos.ne'
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases he : color R p.middle <;> simp_all
  have hBA := Early.edge_Z_le (alpha R) (beta R) rfl (base_adjacent R)
  have hBT := Early.edge_Z_le p.middle (beta R) hcol (adjacent_symm R p.middle_neighbor)
  refine ⟨relIndex_le_of_le_left hBT hpos, ?_, ?_⟩
  · have hh := relIndex_inf_mul_relIndex (Z R (beta R)) (Z R (alpha R)) C
    rw [inf_eq_left.mpr hBA] at hh
    exact hh.symm.trans (Nat.mul_comm _ _)
  · have hb := early.edge_Z_index (alpha R) (beta R) rfl (base_adjacent R)
    have hn : (Z R (beta R)).relIndex (Z R (alpha R)) ≠ 0 := by omega
    exact (relIndex_le_of_le_right (show Z R (alpha R) ⊓ C ≤ Z R (alpha R) from inf_le_left)
      hn).trans_eq hb

/-- Once the geometric reverse comparison is proved, the actual quotient
commutator at the transported flag has order at most two. -/
theorem midpoint_displacement_le_two [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (early : EarlyFacts R geometry) (i : Bool)
    (p : SourceFlagPreparatoryData source geometry i) (t : MiddleTransport p.middle)
    (e : M)
    (hE : secondFlagLayer source i p.delta0 ≤
      (localFlagActor source (!i) e).map t.conjugation.toMonoidHom)
    (hcomparison : (Z R (alpha R)).relIndex
        ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤
      (Z R p.middle).relIndex
        ⁅secondFlagLayer source i p.delta0,
          (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆) :
    ((secondFlagLayer source i e).map t.conjugation.toMonoidHom).relIndex
      ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆ ≤ 2 := by
  let C := ⁅secondFlagLayer source i p.delta0, (Y source i e).map t.conjugation.toMonoidHom⁆
  have hnorm : (localFlagActor source (!i) e).map t.conjugation.toMonoidHom ≤
      normalizer ((Y source i e).map t.conjugation.toMonoidHom) :=
    (map_mono (Y_normalized source i e)).trans (le_normalizer_map _)
  have hCY : C ≤ (Y source i e).map t.conjugation.toMonoidHom :=
    le_normalizer_iff_commutator_le_right.mp (hE.trans hnorm)
  let : Finite (stabilizer R (alpha R)) := finite_stabilizer R (alpha R)
  let : Finite (Y source i e) := Finite.of_injective
    (inclusion ((Y_le_radius source i e).trans (geometry.V_local _ rfl common.large_distance)))
    (inclusion_injective _)
  let : Finite ((Y source i e).map t.conjugation.toMonoidHom) :=
    Finite.of_equiv (Y source i e) (t.conjugation.subgroupMap (Y source i e)).toEquiv
  let : Finite C := Finite.of_injective (inclusion hCY) (inclusion_injective _)
  have hcol : color R p.middle = false := by
    have hh := adjacent_color_ne R p.middle_neighbor
    have hbeta : color R (beta R) = true := rfl
    cases he : color R p.middle <;> simp_all
  apply displacement_index_bound C
    ⁅secondFlagLayer source i p.delta0, (secondFlagLayer source i e).map t.conjugation.toMonoidHom⁆
    (Z R (alpha R)) (Z R (beta R)) (Z R p.middle)
    ((secondFlagLayer source i e).map t.conjugation.toMonoidHom) 2
    (Early.edge_Z_le _ _ rfl (base_adjacent R))
    (Early.edge_Z_le _ _ hcol (adjacent_symm R p.middle_neighbor))
  · rw [← t.map_Z_alpha]
    exact map_mono (Z_le_secondFlagLayer source i e)
  · apply le_inf
    · exact le_normalizer_iff_commutator_le_right.mp
        (hE.trans ((map_mono
          (Incident.secondFlagLayer_normalized source geometry common.large_distance i e)).trans
            (le_normalizer_map _)))
    · exact commutator_mono le_rfl (map_mono (second_le_Y source i e))
  · exact hcomparison
  · exact (midpoint_index_comparison source geometry common early i p t e hE).2.2


/-- The geometric comparison gives every intrinsic estimate for the actual
pullback of U_delta0. In particular the small displacement is derived by
index cancellation and transported through an injective ambient equivalence. -/
theorem smallDisplacementData_of_middleComparison [Finite M]
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (early : EarlyFacts R geometry)
    (i : Bool) (p : SourceFlagPreparatoryData source geometry i)
    (t : MiddleTransport p.middle) (c : MiddleComparisonData source geometry i p t) :
    SmallDisplacementData source i c.flag
      ((secondFlagLayer source i p.delta0).map t.conjugation.symm.toMonoidHom) := by
  have hback (A : Subgroup (FreeAmalgam R)) :
      (A.map t.conjugation.symm.toMonoidHom).map t.conjugation.toMonoidHom = A := by
    rw [Subgroup.map_map]
    have he : t.conjugation.toMonoidHom.comp t.conjugation.symm.toMonoidHom =
        MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      exact t.conjugation.apply_symm_apply x
    rw [he, Subgroup.map_id]
  refine ⟨?_, ?_, ?_, c.core, c.residual, ?_⟩
  · apply (map_le_map_iff_of_injective (f := t.conjugation.toMonoidHom) t.conjugation.injective).mp
    rw [hback]
    exact c.actor
  · exact ((Q_isPGroup R source.two_group source.core_le (alpha R) rfl).to_le
      ((secondFlagLayer_le_radius source i p.delta0).trans
        (V_le_Q geometry common.large_distance _ rfl))).map _
  · intro h
    have hh := map_mono (f := t.conjugation.toMonoidHom) h
    rw [hback] at hh
    exact c.escapes hh
  · have hh := midpoint_displacement_le_two source geometry common early i p t
      c.flag c.actor c.comparison
    have he := relIndex_map_map_of_injective (f := t.conjugation.toMonoidHom)
      (secondFlagLayer source i c.flag)
      ⁅Y source i c.flag,
        (secondFlagLayer source i p.delta0).map t.conjugation.symm.toMonoidHom⁆
      t.conjugation.injective
    rw [map_commutator, hback, commutator_comm] at he
    exact he ▸ hh

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary.Moving
