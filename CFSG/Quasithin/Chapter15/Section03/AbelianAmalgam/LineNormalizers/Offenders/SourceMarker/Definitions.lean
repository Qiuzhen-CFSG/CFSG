module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceSylow

/-!
# The literal projected marker and its source obligations

The marker is the image of the original V under the first coordinate of the
proved paired quotient U → (U/E)₁ × (U/E)₁. It is not an independently chosen
subspace. `Facts` specifies precisely the geometric conclusions needed by
the offender and original-I₀ assembly. Constructing this record is a proof
obligation, not a source theorem supplied by its projections.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
proof of 15.3.67, printed p.1154.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
open Replacement Replacement.Transvections BestReduction.FullCoreTransfer
  BestReduction.SourceAssembly
universe u
variable {G L : Type u} [Group G] [Finite G] [Group L]
  {Y T V M E Pc : Subgroup G} [IsMulCommutative V]
  (o : Geometry.OriginalData Y T V M E Pc)
  (f : temporaryLineNormalizer T V E →* L) (hf : Function.Surjective f)
  (hker : f.ker = centralizer
    (Replacement.Transvections.localSpan T V E : Set (temporaryLineNormalizer T V E)))

/-- The first projection of the original V/E, with the actual paired map. -/
noncomputable def projected :
    let := o.module_normal
    let := o.module_elementary
    Submodule (ZMod 2) (MarkedSection.fixedImage (Replacement.Transvections.localSpan T V E) (localLine T V E) o.tau) := by
  let := o.module_normal
  let := o.module_elementary
  exact (NormalElementaryQuotient.subspace (Replacement.Transvections.localSpan T V E)
    ((V.subgroupOf (temporaryLineNormalizer T V E)).subgroupOf (Replacement.Transvections.localSpan T V E))).map
      ((LinearMap.fst (ZMod 2) _ _).comp (o.pairedSection f hf hker).projection)

/-- The remaining source geometry, tied to the actual projected subspace.
All fields must be proved from the original local data before source assembly
can be declared complete. In particular neither cubic exclusion nor any S₃ or
index-three conclusion is among these fields. -/
structure Facts : Prop where
  nonzero : let := o.module_normal
    let := o.module_elementary
    projected o f hf hker ≠ ⊥
  sylow_fixed : let := o.module_normal
    let := o.module_elementary
    projected o f hf hker ≤ fixedSpace (o.pairedRepresentation f hf hker)
      ((centralizerSylow T V E).map (QuotientGroup.mk' (localCore T V E)))
  orbit_span : let := o.module_normal
    let := o.module_elementary
    Submodule.span (ZMod 2)
      {w | ∃ (g : thompsonImage T V E) (v : _), v ∈ projected o f hf hker ∧
        o.pairedRepresentation f hf hker g v = w} = ⊤
  displacement : let := o.module_normal
    let := o.module_elementary
    ∀ x ∈ localCentralizer T V E,
      (∀ w ∈ projected o f hf hker,
        o.pairedRepresentation f hf hker (QuotientGroup.mk' (localCore T V E) x) w = w) →
        ∀ v ∈ V.subgroupOf (temporaryLineNormalizer T V E), ⁅x, v⁆ ∈ localLine T V E
  normalizer_fixed : let := o.module_normal
    let := o.module_elementary
    ∀ g ∈ normalizer (markedThompson T V E : Set (thompsonImage T V E)),
      ∀ v ∈ projected o f hf hker, o.pairedRepresentation f hf hker g v = v
  intersection : let := o.module_normal
    let := o.module_elementary
    ∀ x ∈ localCentralizer T V E,
      (∀ w ∈ projected o f hf hker,
        o.pairedRepresentation f hf hker (QuotientGroup.mk' (localCore T V E) x) w = w) ↔
      x.val ∈ M

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.SourceMarker
