module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Setup
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Estimates.Endpoint.Bounds
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections

/-!+# Source inputs for the full first-actor fixation calculation

The large-intersection hypothesis makes the literal second section K/Y
nonzero. Since it is a direct sum of natural cubic planes, its dimension
is at least two. Together with the first natural plane this gives
codimension at least four for Y in V_alpha/Z_alpha.

The endpoint estimate bounds every involution's displacement in the same
marked SL3(2) representation, by the unique involution class. These are
inputs to the cubic/involution calculation, not an assertion of fixation.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(1)--(2), p.910, and the opening of (5), p.911.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

private theorem endpoint_has_small_involution
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R)))
    (hendpoint :
      (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4) :
    ∃ a : SL, a ^ 2 = 1 ∧ a ≠ 1 ∧ fixedCodim d.representation (zpowers a) ≤ 2 := by
  let E := (Z R s.endpoint).comap (embedM R)
  let A := E.map source.projection
  have hecol := critical_endpoint_color R (alpha R) rfl _ s.critical
  have hES : Z R s.endpoint ≤ Mbar R := by
    have h := (source.critical_Z_le_stabilizer geometry (alpha R) rfl s.endpoint s.critical).2
    simpa only [alpha, stabilizer_m_base] using h
  have hE : E.map (embedM R) = Z R s.endpoint := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr hES
  have hidx : 2 ^ fixedCodim d.representation A ≤ 4 := by
    have hpre := radius_fixed_preimage common d E
    rw [hE] at hpre
    rw [← hpre, radius_preimage_relIndex] at hendpoint
    exact hendpoint
  have hcod : fixedCodim d.representation A ≤ 2 :=
    (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hidx
  obtain ⟨e, he, heQ⟩ := SetLike.not_le_iff_exists.mp
    (common.critical_reverse _ rfl _ hecol s.critical).2
  obtain ⟨m, rfl⟩ := hES he
  have hm : m ∈ E := he
  have hne : source.projection m ≠ 1 := by
    intro hh
    apply heQ
    rw [Q_alpha R source.two_group source.core_le]
    apply mem_map_of_mem
    rw [← source.projection_kernel]
    exact hh
  have htwo : source.projection m ^ 2 = 1 := by
    rw [← map_pow]
    have hm2 : m ^ 2 = 1 := by
      apply embedM_injective R
      rw [map_pow, map_one]
      let := geometry.Z_elementary (lt_trans (by decide) common.large_distance) s.endpoint hecol
      exact elemPow_eq_one_of_isElementaryAbelian _ he
    rw [hm2, map_one]
  refine ⟨source.projection m, htwo, hne, ?_⟩
  have hle : zpowers (source.projection m) ≤ A := zpowers_le.mpr (mem_map_of_mem _ hm)
  have hdim := Submodule.finrank_mono (fixedSpace_antitone d.representation hle)
  have h₁ := fixedCodim_add_finrank d.representation A
  have h₂ := fixedCodim_add_finrank d.representation (zpowers (source.projection m))
  omega

/-- The literal endpoint bound controls every square-one element in the original
marked quotient representation, including the identity. -/
theorem involution_displacement_le_two_of_endpoint_bound
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (d : LayerModule source (V R (alpha R)))
    (hendpoint :
      (commutatorPreimage (V R (alpha R)) (Z R s.endpoint) (Z R (alpha R))).relIndex
        (V R (alpha R)) ≤ 4) (b : SL) (hb : b ^ 2 = 1) :
    Module.finrank (ZMod 2) (LinearMap.range (d.representation b - 1)) ≤ 2 := by
  by_cases hbone : b = 1
  · subst b
    change Module.finrank (ZMod 2) (LinearMap.range (d.representation 1 - LinearMap.id)) ≤ 2
    rw [map_one]
    change Module.finrank (ZMod 2) (LinearMap.range (LinearMap.id - LinearMap.id : Module.End (ZMod 2) d.Space)) ≤ 2
    rw [sub_self, LinearMap.range_zero, finrank_bot]
    decide
  obtain ⟨a, ha, hane, hsmall⟩ := endpoint_has_small_involution common s d hendpoint
  obtain ⟨c, hc⟩ :=
    AbelianCore.DoubleCopy.CoverModels.ModelOffenders.InvolutionDisplacement.involution_conjugate_transvection
      a ha hane
  obtain ⟨e, he⟩ :=
    AbelianCore.DoubleCopy.CoverModels.ModelOffenders.InvolutionDisplacement.involution_conjugate_transvection
      b hb hbone
  have hac : a = c * Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) * c⁻¹ := by
    rw [← hc, mul_inv_cancel_right]
  have hbe : b = e * Matrix.SpecialLinearGroup.transvection
      (show (0 : Fin 3) ≠ 1 by decide) (1 : ZMod 2) * e⁻¹ := by
    rw [← he, mul_inv_cancel_right]
  have hsame : fixedCodim d.representation (zpowers b) =
      fixedCodim d.representation (zpowers a) := by
    rw [hac, hbe, fixedCodim_zpowers_conj, fixedCodim_zpowers_conj]
  change Module.finrank (ZMod 2) (LinearMap.range (d.representation b - LinearMap.id)) ≤ 2
  rw [← fixedCodim_zpowers_eq_displacement_rank]
  exact hsame.le.trans hsmall

/-- The source's large-intersection branch excludes Y = K. -/
theorem fixedPreimage_lt_intersection
    (common : CommonFacts R source geometry) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle) :
    Sections.fixedPreimage s.middle < Sections.intersection s.middle := by
  apply lt_of_le_of_ne (commutatorPreimage_le _ _ _)
  intro heq
  change Sections.fixedPreimage s.middle = Sections.intersection s.middle at heq
  apply hs
  have hVQ : V R s.middle ≤ Q R (beta R) :=
    (Early.radius_le_Q common s.middle s.middle_color).trans
      (Q_le_adjacent_h R rfl (adjacent_symm R hbc))
  have hc := commutator_commutatorPreimage_le
    (Sections.intersection s.middle) (Q R (beta R)) (Z R (alpha R))
    (inf_le_left.trans ((geometry.V_local _ rfl common.large_distance).trans (Z_normalized R _)))
  change ⁅Sections.fixedPreimage s.middle, Q R (beta R)⁆ ≤ Z R (alpha R) at hc
  rw [heq] at hc
  exact (commutator_mono le_rfl hVQ).trans hc

/-- Both literal natural sections have dimension at least two; the first has
dimension exactly two and the second uses the genuine large-branch assumption. -/
theorem natural_section_dimension_bounds
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    Module.finrank (ZMod 2) (d.Space ⧸ d.subspace (Sections.intersection s.middle)) = 2 ∧
      2 ≤ Module.finrank (ZMod 2) ((d.subspace (Sections.intersection s.middle)) ⧸
        (d.subspace (Sections.fixedPreimage s.middle)).comap
          (d.subspace (Sections.intersection s.middle)).subtype) := by
  obtain ⟨f⟩ := Sections.exists_frame common radius hb
  constructor
  · obtain ⟨e, _⟩ := Sections.exists_first_natural common radius f hb s hbc d
    simpa using e.finrank_eq
  · obtain ⟨n, e, φ, _, hker, _⟩ := Sections.exists_second_natural common radius f hb s hbc d
    have hn : n ≠ 0 := by
      intro hn
      subst n
      apply (fixedPreimage_lt_intersection common s hs hbc).not_ge
      intro x hx
      have hxker : (⟨x, hx⟩ : Sections.intersection s.middle) ∈ φ.ker := by
        exact Subsingleton.elim _ _
      rw [hker] at hxker
      exact hxker
    have he := e.finrank_eq
    have hefin : Module.finrank (ZMod 2) (Fin n → Fin 2 → ZMod 2) = n * 2 := by
      rw [Module.finrank_pi_fintype, Module.finrank_pi]
      simp
    rw [hefin] at he
    omega

/-- The two nonzero cubic sections give codimension at least four for the
literal Y, before the endpoint rank bound is used. -/
theorem fixedPreimage_quotient_finrank_ge_four
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hs : ¬ s.SmallIntersection) (hbc : Adjacent R (beta R) s.middle)
    (d : LayerModule source (V R (alpha R))) :
    4 ≤ Module.finrank (ZMod 2) (d.Space ⧸ d.subspace (Sections.fixedPreimage s.middle)) := by
  obtain ⟨hfirst, hsecond⟩ := natural_section_dimension_bounds common radius hb s hs hbc d
  have hle := d.subspace_mono (show Sections.fixedPreimage s.middle ≤
    Sections.intersection s.middle from commutatorPreimage_le _ _ _)
  have he := (Submodule.comapSubtypeEquivOfLe hle).finrank_eq
  have hK := (d.subspace (Sections.intersection s.middle)).finrank_quotient_add_finrank
  have hY := (d.subspace (Sections.fixedPreimage s.middle)).finrank_quotient_add_finrank
  have hKY := ((d.subspace (Sections.fixedPreimage s.middle)).comap
    (d.subspace (Sections.intersection s.middle)).subtype).finrank_quotient_add_finrank
  omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension
