module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Transport
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Selection.Forward
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Selection.Lifting
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement.ReverseRadius.Selection.ModelProof

/-!
# Selecting the reverse parabolic from the forward displacement

An actual distinct incident fixed subgroup lets the forward inequalities
fill Q_beta/Q_middle with V_alpha. Move the base vertex to the midpoint by
an element fixing beta, and compare the original escaping edge transporter
with this one. Their difference belongs to the original M-vertex group.
If the corresponding parabolics coincided, the intrinsic core and its
characteristic edge layer would coincide, contradicting escape.

The finite same-type parabolic calculation `ReverseSelection.modelJoin`
and its quotient lift supply the required index-three join.
`FlagCriticalData.reverseRadiusWitness` assembles the concrete transporter,
escape, and join from the forward inequalities. The original conditional
construction `reverseRadiusWitness_of_model` remains available. The
excessive fixed-index hypothesis is used by the subsequent reverse
displacement calculation in `ReverseRadius.Transport`.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (1), printed
p.905, the sentence beginning “By a symmetric argument”.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

private theorem conjugate_twice {G : Type*} [Group G] (A : Subgroup G) (s u : G) :
    (A.map (MulAut.conj u⁻¹).toMonoidHom).map (MulAut.conj s).toMonoidHom =
      A.map (MulAut.conj (s * u⁻¹)).toMonoidHom := by
  rw [map_map]
  congr 1
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

/-- The source construction reduced to the finite same-type parabolic identity.
Every geometric placement and transporter is constructed here. -/
theorem FlagCriticalData.reverseRadiusWitness_of_model
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R))
    (hmodel : ReverseSelection.ModelJoin source.flag i)
    (hforward : ∀ d : M, flagIncident source i 1 d →
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
      ∀ g : M, flagIncident source i g d →
      localFlagZ source i g ≠ localFlagZ source i 1 →
      2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g)) :
    Nonempty (ReverseRadiusWitness source geometry i p) := by
  have hfill := p.radius_sup_middle_kernel_of_forward common hb early hkernel hforward
  obtain ⟨s, hs, hsm⟩ := stabilizer_transitive_neighbors R (beta R)
    (adjacent_symm R (base_adjacent R)) p.middle_neighbor
  change act R s (alpha R) = p.middle at hsm
  let b := MulAut.conj s
  have hQA : (Q R p.middle).map b.toMonoidHom = Q R (alpha R) := by
    have he : act R s⁻¹ p.middle = alpha R := by
      rw [← hsm, ← act_mul, mul_inv_cancel, act_one]
    have hh := Q_act R s⁻¹ p.middle
    rw [he, inv_inv] at hh
    exact hh.symm
  have hQB : (Q R (beta R)).map b.toMonoidHom = Q R (beta R) :=
    mem_normalizer_iff_map_conj_eq.mp (Q_normalized R _ hs)
  have hVB : (V R (beta R)).map b.toMonoidHom = V R (beta R) :=
    mem_normalizer_iff_map_conj_eq.mp (DistanceEight.V_normalized R _ hs)
  let A := (V R (alpha R)).map b.toMonoidHom
  have hA : A ⊔ Q R (alpha R) = flagKernel source i := by
    have hh := congrArg (Subgroup.map b.toMonoidHom) hfill
    rw [Subgroup.map_sup, hQA, hQB] at hh
    exact hh.trans hkernel.symm
  obtain ⟨u, hu, hescape⟩ := p.exists_reverse_escaping_edge common hb
  have hsu : s * u⁻¹ ∈ stabilizer R (alpha R) := by
    change act R (s * u⁻¹) (alpha R) = alpha R
    rw [act_mul, hsm, ← hu, ← act_mul, mul_inv_cancel, act_one]
  rw [alpha, stabilizer_m_base] at hsu
  obtain ⟨g, hg⟩ := hsu
  have hmap (D : Subgroup (FreeAmalgam R)) :
      (D.map (MulAut.conj u⁻¹).toMonoidHom).map b.toMonoidHom = localConjugate D g := by
    rw [conjugate_twice, ← hg]
    rfl
  have hne : localFlagActor source i g ≠ flagParabolic source i := by
    intro he
    have hw := ReverseSelection.firstLayer_eq_of_actor_eq source geometry common.large_distance
      i hkernel g he
    apply hescape
    apply (map_le_map_iff_of_injective (f := b.toMonoidHom) b.injective).mp
    rw [hmap]
    change firstFlagLayer (R := R) g ≤ _
    rw [hw, ← hVB]
    exact map_mono (edgeRadius_le_Q_alpha geometry common.large_distance)
  have hi := ReverseSelection.join_index_of_model source i hmodel A hA g hne
  refine ⟨⟨u, hu, hescape, ?_⟩⟩
  rw [← relIndex_map_map_of_injective _ _ (f := b.toMonoidHom) b.injective,
    Subgroup.map_sup, map_inf _ _ b.toMonoidHom b.injective, hmap, hmap]
  exact hi

/-- The reverse parabolic configuration constructed from the forward inequalities.
The finite same-type parabolic identity is discharged by `ReverseSelection.modelJoin`. -/
theorem FlagCriticalData.reverseRadiusWitness
    {source : LocalSource L R} {geometry : Geometry R} {i : Bool}
    (p : FlagCriticalData source geometry i) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (hkernel : flagKernel source i = Q R (beta R))
    (hforward : ∀ d : M, flagIncident source i 1 d →
      ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) d ≤ Q R (alpha R) →
      ∀ g : M, flagIncident source i g d →
      localFlagZ source i g ≠ localFlagZ source i 1 →
      2 < (Q R p.middle).relIndex (firstFlagLayer (R := R) g)) :
    Nonempty (ReverseRadiusWitness source geometry i p) :=
  p.reverseRadiusWitness_of_model common hb early hkernel
    (ReverseSelection.modelJoin source.flag i) hforward

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
