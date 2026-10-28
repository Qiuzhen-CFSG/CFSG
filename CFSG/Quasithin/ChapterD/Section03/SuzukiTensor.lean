module
public import CFSG.Quasithin.ChapterD.Section03.SuzukiConstituent
public import Theory.Representation.Suzuki.NormalizerActors
public import Theory.Representation.BinaryOffender.CubicSection

/-!
# Exclusion of a Suzuki tensor from the full linear normalizer

Every small elementary actor in the full normalizer of a faithful
irreducible Suzuki square belongs to the square image. Its cubic action,
fixed codimension and rank transport unchanged to the square itself.
The strict constituent descent and the Suzuki endpoint exclude that actor.
Thus the full normalizer has cubic ratio strictly greater than two.

The SQTK hypothesis is only on the actual Suzuki factor and is supplied
by the original Chapter 10 component quotient. The original seed application
retains both possible crossed-support orientations.
Source: Aschbacher--Smith D.3.7--8, printed pp.197--199.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD
open BenderSuzuki.MatrixGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- No small cubic actor exists anywhere in the full linear normalizer. -/
theorem suzuki_square_normalizer_cubicRatio_gt (m : ℕ) (hm : 0 < m)
    (hS : IsSQTK KnownSimple.IsKnownSimple (SuzukiMatrixGroup m))
    (ρ : Representation (ZMod 2) (SuzukiMatrixGroup m × SuzukiMatrixGroup m) V)
    (hi : ρ.IsIrreducible) (hf : Function.Injective ρ) :
    2 < cubicRatio (normalizerRepresentation ρ) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (Module.End (ZMod 2) V) := Finite.of_injective
    (fun f : Module.End (ZMod 2) V => (f : V → V)) DFunLike.coe_injective
  by_contra! hsmall
  obtain ⟨A,hA,hc,hd⟩ := (cubicRatio_le_nat_iff (normalizerRepresentation ρ) 2).mp hsmall
  let : IsElementaryAbelian 2 A := hA.2
  have hle := Suzuki.binary_square_small_actor_le_image m hm ρ hi hf A hd
  let N := (actionImage ρ).subgroupOf (linearNormalizer ρ)
  let E : N ≃* (SuzukiMatrixGroup m × SuzukiMatrixGroup m) :=
    (subgroupOfEquivOfLe (actionImage ρ).le_normalizer).trans
      (PerfectNormalizer.imageEquiv ρ hf).symm
  let C := A.subgroupOf N
  have hC : IsElementaryTwo C := by
    refine ⟨?_,IsElementaryAbelian.subgroupOf hle⟩
    intro he
    change A.subgroupOf N = ⊥ at he
    apply hA.1
    rw [←map_subgroupOf_eq_of_le hle,he,Subgroup.map_bot]
  have hsmallN : cubicRatio ((normalizerRepresentation ρ).comp N.subtype) ≤ 2 := by
    apply (cubicRatio_le_nat_iff _ 2).mpr
    refine ⟨C,hC,?_,?_⟩
    · intro a ha b hb c hc' v
      exact hc a ha b hb c hc' v
    · rw [fixedCodim_subgroupOf (normalizerRepresentation ρ) hle,rank_subgroupOf hle]
      exact hd
  have hinner : cubicRatio ρ ≤ 2 :=
    cubicRatio_comp_equiv_le_nat ((normalizerRepresentation ρ).comp N.subtype) E.symm 2 hsmallN
  exact (not_le_of_gt (suzuki_square_cubicRatio_gt m hm hS ρ hi hf)) hinner
end CFSG.Quasithin.ChapterD
