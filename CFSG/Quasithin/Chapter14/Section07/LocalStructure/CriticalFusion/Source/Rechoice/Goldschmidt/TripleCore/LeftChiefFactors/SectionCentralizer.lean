module
public import CFSG.Quasithin.Chapter12.Section08.Preliminary.LocalKernel.Kernel
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.TripleCore.LeftChiefFactors.BorelRefinements.NaturalChief

/-!
# The original section centralizer from the earlier local kernel

The coordinate action on U/V₁ and the original tilded conjugation action
have the same kernel: both fix precisely those actors whose commutators
with U lie in V₁. The source local-kernel theorem identifies that kernel
with O₂(H). The original coordinate map and quotient are retained, so this
supplies the centralizer premise in the natural chief-factor contribution.

Source: Aschbacher--Smith, 12.8.4(4), 14.5.15(4), and 14.7.70.
-/

public section
noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data
open Chapter12.Section08
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

private theorem coordinates_displacement (h : F.H) (a : F.U) :
    (d.conjugationSection.coordinates (F.uAction h a * a⁻¹)).toAdd =
      d.action h (d.conjugationSection.coordinates a).toAdd -
        (d.conjugationSection.coordinates a).toAdd := by
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv,
    sub_eq_add_neg]
  rw [show (d.conjugationSection.coordinates (F.uAction h a)).toAdd =
    d.action h (d.conjugationSection.coordinates a).toAdd from
      d.conjugationSection.equivariant h a]

private theorem action_kernel_iff (h : F.H) :
    h ∈ d.action.ker ↔ ∀ a ∈ F.U, ⁅(h : G), a⁆ ∈ F.Vi 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hh a ha
    let aU : F.U := ⟨a, ha⟩
    have hc : d.conjugationSection.coordinates (F.uAction h aU * aU⁻¹) = 1 := by
      apply Multiplicative.toAdd.injective
      change (d.conjugationSection.coordinates (F.uAction h aU * aU⁻¹)).toAdd = 0
      rw [coordinates_displacement, hh]
      simp
    exact (d.conjugationSection.coordinates_eq_one_iff _).mp hc
  · intro hh
    apply LinearMap.ext
    intro w
    change d.action h w = w
    obtain ⟨a, ha⟩ := d.conjugationSection.onto (Multiplicative.ofAdd w)
    have hc : d.conjugationSection.coordinates (F.uAction h a * a⁻¹) = 1 := by
      apply (d.conjugationSection.coordinates_eq_one_iff _).mpr
      exact hh a a.property
    have hz : (d.conjugationSection.coordinates (F.uAction h a * a⁻¹)).toAdd = 0 :=
      congrArg Multiplicative.toAdd hc
    rw [coordinates_displacement] at hz
    simpa only [ha, toAdd_ofAdd] using sub_eq_zero.mp hz

/-- The genuine earlier local kernel supplies the original section-centralizer
identity, retaining only the two earlier universal source inputs. -/
theorem sectionCentralizer_of_earlier_setup
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u}) :
    d.SectionCentralizer := by
  let := d.natural.chosen.elementary
  have hH : F.H ∈ F.Hz L (normalizer (L : Set G)) := by
    rw [d.unique_Hz]
    exact Set.mem_singleton _
  have hk : (F.localTildeAction F.H le_rfl).ker = pCore 2 F.H :=
    F.localKernel_eq_pCore d.counterexample.qtke
    L (normalizer (L : Set G)) F.H (by decide : 2 ≤ 3)
    d.natural.chosen.le_sylow d.natural.chosen.normalizes
    (d.natural.sylow_normalizes structural) d.natural.residual
    (fun _ => ⟨d.natural.naturalMarking⟩) rfl
    (d.natural.maximal_unique structural uniqueness).2
    (d.natural.seed_centralizer_le structural uniqueness)
    d.natural.centralizer_L hH
  change d.action.ker = (F.H.pCoreIn 2).subgroupOf F.H
  calc
    d.action.ker = (F.localTildeAction F.H le_rfl).ker := by
      ext h
      exact (action_kernel_iff d h).trans (F.mem_localTildeAction_ker_iff F.H le_rfl h).symm
    _ = pCore 2 F.H := hk
    _ = (F.H.pCoreIn 2).subgroupOf F.H := by
      change pCore 2 F.H = ((pCore 2 F.H).map F.H.subtype).comap F.H.subtype
      rw [comap_map_eq_self_of_injective F.H.subtype_injective]

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Data

namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
open Chapter12.Section08 NoncentralChiefRefinement
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]
  (d : Data T L V F W)

/-- The actual natural-factor lower bound with its section-centralizer premise
supplied from the earlier source, on every chief series of the original interval. -/
theorem sourceNaturalChief_count_of_earlier_setup
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (uniqueness : Chapter12.Section08.Uniqueness127 KnownSimple.IsKnownSimple.{u})
    (h : CompatibleBorel d)
    (s : ChiefSeries (F.Li L 1 ⊔ (T : Subgroup G) : Subgroup G))
    (hs0 : s.head = sourcePointNode (F := F) (L := L))
    (hsl : s.last = sourceUNode d) : 2 ≤ s.noncentralTwoCount :=
  sourceNaturalChief_count d h (d.sectionCentralizer_of_earlier_setup structural uniqueness)
    s hs0 hsl

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.Rechoice.Goldschmidt.LeftChiefFactors.BorelRefinements
