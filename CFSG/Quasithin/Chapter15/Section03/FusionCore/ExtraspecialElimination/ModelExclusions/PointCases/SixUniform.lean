module

public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.SixPoint
public import Theory.Representation.BinaryPermutationNaturalStructure
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Every point of the six-letter natural and core modules

Duad coordinates move any nonzero natural vector to the point used by
`SixPoint`. The projection from the even-weight core to the natural module
preserves every vector stabilizer: a nonzero quotient vector is represented
by a duad, and its other representative differs by the fixed constant vector.
Consequently a proper core point stabilizer also has no strong offender in
its intrinsic two-core. The zero and constant positions are treated explicitly.

Source: Aschbacher–Smith, combined manuscript, B.3.2, printed pp.83–84,
and the final A₆ paragraph of 15.3.49, printed p.1145.
-/

@[expose] public section

open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination
open ModelExclusions
open Theory.SpecificGroups.SymmetricSix
open BinaryFlags.NaturalGeometry
open BinaryPermutation
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.SixUniform
abbrev V := BinaryPermutation.natural (Fin 6)
abbrev W := naturalRepresentation (Fin 6)

private def duadMover (d : BinaryFlags.NaturalGeometry.Duad) : S6 :=
  Equiv.swap ((Equiv.swap 4 d.val.1) 5) d.val.2 * Equiv.swap 4 d.val.1
set_option maxRecDepth 4096 in
private theorem duadMover_apply : ∀ d : BinaryFlags.NaturalGeometry.Duad,
    duadMover d 4 = d.val.1 ∧ duadMover d 5 = d.val.2 := by decide

theorem point_reachable (v : V) (hv : v ≠ 0) :
    ∃ g : S6, W g (pairVector 4 5) = v := by
  obtain ⟨d,rfl⟩ := (vector_cases v).resolve_left hv
  refine ⟨duadMover d, ?_⟩
  rw [pairVector_map, (duadMover_apply d).1, (duadMover_apply d).2]
  rfl

private theorem action_conj (g a : S6) (v : V) :
    W g (W a v) = W ((MulAut.conj g) a) (W g v) := by
  simp only [← Module.End.mul_apply, ← map_mul, MulAut.conj_apply]
  rw [show g * a * g⁻¹ * g = g * a by group]

theorem not_strong_point (v : V) (hv : v ≠ 0) {A : Subgroup S6}
    (hA : A ≤ localTwoCore (pointStabilizer W v)) : ¬ IsStrongOffender W A := by
  intro hs
  obtain ⟨g,hg⟩ := point_reachable v hv
  let E : V ≃ₗ[ZMod 2] V := LinearEquiv.ofBijective (W g⁻¹) (W.apply_bijective g⁻¹)
  have hE : ∀ a v, E (W a v) = W ((MulAut.conj g⁻¹) a) (E v) := action_conj g⁻¹
  have hz : E v = pairVector 4 5 := by
    change W g⁻¹ v = _
    rw [← hg, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl
  apply exclude_strong_at_identified_point W W (MulAut.conj g⁻¹) E hE v
    (pointStabilizer W v) A rfl hA _ hs
  rw [hz, SixPoint.natural_point_stabilizer]
  exact fun _ hB => SixPoint.not_strong_natural hB

private def pairFull (i j : Fin 6) : Full (Fin 6) := Pi.single i 1 + Pi.single j 1

private theorem pairFull_map (g : S6) (i j : Fin 6) :
    representation (Fin 6) g (pairFull i j) = pairFull (g i) (g j) := by
  ext k
  simp [pairFull, representation_apply, Pi.single_apply, Equiv.symm_apply_eq]

private theorem pairFull_eq {i j k l : Fin 6} (h : pair i j = pair k l) :
    pairFull i j = pairFull k l := by
  have he : ({i,j} : Set (Fin 6)) = {k,l} := by
    simpa only [pair, Finset.coe_insert, Finset.coe_singleton] using
      congrArg (fun s : Finset (Fin 6) => (s : Set (Fin 6))) h
  rcases Set.pair_eq_pair_iff.mp he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · rfl
  · simp [pairFull, add_comm]

/-- On the even six-letter core, the natural quotient preserves each
vector stabilizer, including the two constant vectors. -/
theorem core_point_stabilizer (v : core (Fin 6)) :
    pointStabilizer (coreRepresentation (Fin 6)) v =
      pointStabilizer W (coreToNatural (Fin 6) v) := by
  ext g
  constructor
  · intro hg
    change W g (coreToNatural (Fin 6) v) = coreToNatural (Fin 6) v
    rw [← coreToNatural_equivariant]
    exact congrArg (coreToNatural (Fin 6)) hg
  · intro hg
    change W g (coreToNatural (Fin 6) v) = coreToNatural (Fin 6) v at hg
    rcases vector_cases (coreToNatural (Fin 6) v) with hz | ⟨d,hd⟩
    · have hz' := congrArg Subtype.val hz
      have hc : v.val ∈ constants (Fin 6) := (Submodule.Quotient.mk_eq_zero _).mp hz'
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
      apply Subtype.ext
      change representation (Fin 6) g v.val = v.val
      rw [← hc, map_smul, permute_allOne]
    · have he : (constants (Fin 6)).mkQ v.val =
          (constants (Fin 6)).mkQ (pairFull d.val.1 d.val.2) := congrArg Subtype.val hd
      have hc := (Submodule.Quotient.eq (constants (Fin 6))).mp he
      obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hc
      have hpair : W g (pairVector d.val.1 d.val.2) = pairVector d.val.1 d.val.2 := by
        simpa only [hd,duadVector] using hg
      rw [pairVector_map] at hpair
      have hfull := pairFull_eq ((pairVector_eq_iff
        (g.injective.ne (ne_of_lt d.property)) (ne_of_lt d.property)).mp hpair)
      have hv : v.val = pairFull d.val.1 d.val.2 + c • allOne (Fin 6) := by
        rw [hc]
        abel
      apply Subtype.ext
      change representation (Fin 6) g v.val = v.val
      rw [hv, map_add, map_smul, permute_allOne, pairFull_map, hfull]

theorem core_image_nonzero (v : core (Fin 6))
    (hp : pointStabilizer (coreRepresentation (Fin 6)) v ≠ ⊤) :
    coreToNatural (Fin 6) v ≠ 0 := by
  intro hz
  apply hp
  rw [core_point_stabilizer,hz]
  exact top_unique (fun _ _ => map_zero _)

theorem not_strong_core_point (v : core (Fin 6))
    (hp : pointStabilizer (coreRepresentation (Fin 6)) v ≠ ⊤)
    {A : Subgroup S6} (hA : A ≤ localTwoCore (pointStabilizer (coreRepresentation (Fin 6)) v)) :
    ¬ IsStrongOffender (coreRepresentation (Fin 6)) A := by
  intro hs
  rw [core_point_stabilizer] at hA
  apply not_strong_point (coreToNatural (Fin 6) v) (core_image_nonzero v hp) hA
  exact ⟨hs.1, (fixedCodim_le_of_equivariant_surjection (coreRepresentation (Fin 6)) W
    (coreToNatural (Fin 6)) coreToNatural_surjective coreToNatural_equivariant A).trans_lt hs.2⟩
end CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ModelExclusions.PointCases.SixUniform
