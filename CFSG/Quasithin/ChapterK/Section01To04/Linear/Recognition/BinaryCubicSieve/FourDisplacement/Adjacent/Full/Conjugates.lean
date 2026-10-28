module

public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import Theory.Representation.BinaryOffender.CubicConjugateDimension.CentralCover
public import Theory.Representation.BinaryOffender.NormalizerConjugateDimension
public import Theory.Alternating.EightInvolutionGeneration

/-!
# Seven-conjugate generation in the binary SL₄ linear normalizer

Identify the actual SL₄(2) image with A₈ using the exceptional exterior-square
comparison. The seven-inner-conjugate theorem for Aut(A₈) applies to every
nonidentity involution of the full linear normalizer, including outer actors.
The central-cover lifting theorem uses the cyclic linear centralizer and
perfectness of the image to lift containment back to the literal normalizer.
Finally its conjugators are included in the units of `Module.End`.

Only faithful irreducibility is required. In particular there is no absolute
irreducibility, dimension, support or cubic-action premise. This discharges
the generation input of `full_support_remaining_actors_of_seven_conjugates`.

Source context: Aschbacher–Smith K.3.2, printed pp.451,454–455;
Guralnick–Malle, *Classification of 2F-modules, II*, author manuscript
Proposition 4.8(3B). The seven-conjugate estimate is proved constructively in
`Theory.Alternating.EightInvolutionGeneration`, rather than assumed from the
source's module catalogue.
-/

public section

open Subgroup
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- Seven conjugates of every nonidentity involution in the full linear
normalizer generate a subgroup containing the actual SL₄(2) action image. -/
theorem normalizer_seven_conjugates
    (σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) V)
    (hf : Function.Injective σ) (hi : σ.IsIrreducible) :
    NormalizerConjugateGenerationBound σ 7 := by
  let A := actionImage σ
  let N := linearNormalizer σ
  let I := A.subgroupOf N
  let : I.Normal := Subgroup.normal_in_normalizer
  let eG : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ≃* A :=
    MonoidHom.ofInjective (f := σ.asGroupHom) (fun _ _ h => hf (congrArg Units.val h))
  let eGI : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) ≃* I :=
    eG.trans (subgroupOfEquivOfLe A.le_normalizer).symm
  let eI : I ≃* alternatingGroup (Fin 8) :=
    eGI.symm.trans (Atlas.Order20160A8.sl4TwoEquivPSL.trans
      Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8)
  let : Group.IsPerfect (alternatingGroup (Fin 8)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : Group.IsPerfect I := Group.IsPerfect.ofSurjective
    (f := eI.symm.toMonoidHom) eI.symm.surjective
  have hcenter : center I = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    apply (mem_bot).mpr
    apply eI.injective
    rw [map_one]
    have h : eI x ∈ center (alternatingGroup (Fin 8)) := by
      apply mem_center_iff.mpr
      intro y
      obtain ⟨z, rfl⟩ := eI.surjective y
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hx) z]
    rw [alternatingGroup.center_eq_bot (by simp)] at h
    exact (mem_bot.mp h)
  let e : I ⧸ center I ≃* alternatingGroup (Fin 8) :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      ((QuotientGroup.quotientBot).trans eI)
  have hrep : ((normalizerRepresentation σ).comp I.subtype).comp eGI.toMonoidHom = σ := by
    ext g v
    rfl
  have hiI : Representation.IsIrreducible ((normalizerRepresentation σ).comp I.subtype) :=
    (Representation.irreducible_comp_surjective_iff eGI.toMonoidHom eGI.surjective _).mp
      (hrep.symm ▸ hi)
  have hbound := involutionConjugateGenerationBound_of_centralCover
    (normalizerRepresentation σ) I (fun _ _ h => Subtype.ext (Units.ext h)) hiI e
      alternatingGroup.EightInvolutionGeneration.seven_inner_conjugates
  intro t ht ht2
  obtain ⟨c, hc⟩ := hbound t ht ht2
  refine ⟨fun i => (c i).val, ?_⟩
  have hmap := Subgroup.map_mono (f := N.subtype) hc
  rw [MonoidHom.map_closure] at hmap
  have hset : N.subtype '' (Set.range fun i => c i * t * (c i)⁻¹) =
      Set.range (fun i => (c i).val * t.val * (c i).val⁻¹) := by
    ext x
    simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hset] at hmap
  intro a ha
  exact hmap ⟨⟨a, A.le_normalizer ha⟩, ha, rfl⟩

end CFSG.Quasithin.ChapterK.Linear.Recognition.BinaryCubicSieve.FourDisplacement
