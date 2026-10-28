module

public import Theory.AlgebraicGroup.Semisimple.SolvableNormal
public import Theory.AlgebraicGroup.Bor1.TorusBorelGeneration.Source
public import Theory.AlgebraicGroup.Unipotent.SolvableTorusDecomposition

/-!
# The torus acts nontrivially on the rank-one Borel radical

Borel's generation by a Borel and the normalizer of a maximal torus implies
that the Borel cannot normalize its torus in a semisimple group of positive
rank. The actual torus--unipotent decomposition then shows that its unipotent
radical is nontrivial and that the torus acts on it nontrivially. Connectedness
of the radical gives positive dimension. These are the original-source inputs
for Borel §§13.13--13.14, without a rank-one classification assumption.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace Theory.AlgebraicGroup.Bor1.RankOneGeometry
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

theorem borel_not_le_torus_normalizer
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety = 1)
    (hB : IsBorelSubgroup B) (hTB : T ≤ B) :
    ¬ B.toSubgroup ≤ T.normalizer.toSubgroup := by
  intro hBN
  have hgen := TorusBorelGeneration.borel_normalizer_generation hG.1 hB hT hTB
  have hNtop : T.normalizer.toSubgroup = ⊤ := by
    apply top_unique
    rw [← hgen]
    exact (Subgroup.closure_le T.normalizer.toSubgroup).2 (Set.union_subset hBN (by rfl))
  have hnormal : T.toSubgroup.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  obtain ⟨hfin, _⟩ := semisimple_normal_le_borel_finite_central hG B hB T hnormal hTB
  have hz := (dimension_zero_iff_finite_points T.carrierVariety).mpr hfin
  rw [hdimT] at hz
  exact one_ne_zero hz

theorem unipotentRadical_ne_bot
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety = 1)
    (hB : IsBorelSubgroup B) (hTB : T ≤ B)
    (hV : IsUnipotentRadicalOf B V) : V.toSubgroup ≠ ⊥ := by
  intro hbot
  apply borel_not_le_torus_normalizer hG T B hT hdimT hB hTB
  have hdecomp := maximalTorus_unipotentRadical_decomposition_of_connected_solvable
    hB.connected hB.solvable hV hT hTB
  rw [hdecomp.2.1,hbot,sup_bot_eq]
  exact T.toSubgroup.le_normalizer

theorem unipotentRadical_dimension_pos
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety = 1)
    (hB : IsBorelSubgroup B) (hTB : T ≤ B)
    (hV : IsUnipotentRadicalOf B V) :
    0 < Variety.dimension V.carrierVariety := by
  obtain ⟨V',hV',hc⟩ := exists_unipotentRadical_of_connected_solvable B hB.connected hB.solvable
  have he : V'=V := unipotent_radical_unique hV' hV
  subst V'
  apply connected_closedSubgroup_dimension_pos_of_ne_bot V hc
  intro hb
  exact unipotentRadical_ne_bot hG T B V hT hdimT hB hTB hV hb

theorem exists_torus_unipotentRadical_noncommuting
    (hG : IsSemisimpleAlgebraicGroup G)
    (T B V : ClosedSubgroup G) (hT : IsMaximalTorus T)
    (hdimT : Variety.dimension T.carrierVariety = 1)
    (hB : IsBorelSubgroup B) (hTB : T ≤ B)
    (hV : IsUnipotentRadicalOf B V) :
    ∃ t ∈ T.toSubgroup, ∃ v ∈ V.toSubgroup, t * v ≠ v * t := by
  by_contra! hcomm
  apply borel_not_le_torus_normalizer hG T B hT hdimT hB hTB
  have hdecomp := maximalTorus_unipotentRadical_decomposition_of_connected_solvable
    hB.connected hB.solvable hV hT hTB
  rw [hdecomp.2.1]
  apply sup_le T.toSubgroup.le_normalizer
  apply le_trans ?_ (Subgroup.centralizer_le_normalizer (T.toSubgroup : Set (Variety.Point G)))
  intro v hv
  exact Subgroup.mem_centralizer_iff.mpr (fun t ht => hcomm t ht v hv)
end Theory.AlgebraicGroup.Bor1.RankOneGeometry
