module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.CheckedPoint
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.Transport
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.Flags.SylowCalculation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup.Configuration.LocalReductions

/-!
# Assembling the A₅ flag and checked central point from finite coordinates

A permutation aligning the two pulled-back source subgroups constructs the
actual marked flag, while conjugating both action maps and preserving their
kernel. The two model orbit indices supply the local odd index. On that same
marking, a has a nonidentity central image in the literal checked Sylow image.
The final adapter applies this local index to the existing Baumann promotion.

The finite Sylow calculation supplies the coordinate witness and both indices
from `FlagSource` alone. The construction therefore assumes neither alignment
nor a local or global centralizer Sylow assertion. The final local-reduction
adapter retains the earlier-source and fusion premises for the configuration
assembly owner to discharge.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, Notation 13.2.1
(p.877), the local part of 13.2.6 (p.879), and the marking paragraph (p.926).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
open Subgroup BinaryPermutation BinaryPermutation.FiveCentralizerGeometry A5Module
open A5Module.FlagCoordinates
variable {G : Type*} [Group G] [Finite G]
namespace A5Module.FlagSource
variable {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G} (d : FlagSource T L V V₁ V₂)

/-- Assemble the actual flag from a permutation aligning the pulled-back source flag. -/
def flagOfCoordinates (g : Perm)
    (hz : zpowers (Multiplicative.ofAdd (rho g z)) = d.preimage V₁)
    (hv : Multiplicative.ofAdd (rho g v) ∈ d.preimage V₂)
    (hv₁ : Multiplicative.ofAdd (rho g v) ∉ d.preimage V₁) : FlagMarking T L V V₁ V₂ :=
  (d.relabel g).mark (by
    have he := congrArg (Subgroup.map d.module.map) hz
    rw [MonoidHom.map_zpowers, d.preimage_map V₁ (d.one_le_two.trans d.two_le_V)] at he
    exact he) hv hv₁

/-- All ambient outputs follow from the finite coordinate alignment and its
orbit indices. The finite calculation is still an explicit premise here. -/
theorem construction_of_coordinate_witness (g : Perm)
    (hz : zpowers (Multiplicative.ofAdd (rho g z)) = d.preimage V₁)
    (hv : Multiplicative.ofAdd (rho g v) ∈ d.preimage V₂)
    (hv₁ : Multiplicative.ofAdd (rho g v) ∉ d.preimage V₁)
    (hN : (stabilizer d.image (rho g v)).index = 10)
    (hT : (stabilizer d.image (rho g v)).relIndex (d.imageSylow : Subgroup d.image) = 2) :
    ∃ f : FlagMarking T L V V₁ V₂, f.module = d.module.relabel g ∧
      (¬ 2 ∣ (Tv (T : Subgroup G) (markedV f.module)).relIndex
        (normalizer (V : Set G) ⊓ Gv (markedV f.module))) ∧
      ∃ aT : Tv (T : Subgroup G) (markedV f.module),
        (aT : G) = markedA f.module ∧
        (checkedSylowMap (T : Subgroup G) (markedV f.module)).rangeRestrict aT ≠ 1 ∧
        (checkedSylowMap (T : Subgroup G) (markedV f.module)).rangeRestrict aT ∈
          center (checkedSylowMap (T : Subgroup G) (markedV f.module)).range := by
  refine ⟨d.flagOfCoordinates g hz hv hv₁, rfl,
    d.localIndex_of_coordinate_indices (rho g v) hN hT, (d.relabel g).checkedPoint, rfl,
    (d.relabel g).checkedPoint_ne_one, (d.relabel g).checkedPoint_central⟩

/-- Construct the aligned flag, local odd index and checked central point from
the unaligned source data. The flag retains the actual line, plane and action
kernel, and its module is obtained by relabelling the given module. -/
theorem construction :
    ∃ f : FlagMarking T L V V₁ V₂,
      (∃ g : Perm, f.module = d.module.relabel g) ∧
      (¬ 2 ∣ (Tv (T : Subgroup G) (markedV f.module)).relIndex
        (normalizer (V : Set G) ⊓ Gv (markedV f.module))) ∧
      ∃ aT : Tv (T : Subgroup G) (markedV f.module),
        (aT : G) = markedA f.module ∧
        (checkedSylowMap (T : Subgroup G) (markedV f.module)).rangeRestrict aT ≠ 1 ∧
        (checkedSylowMap (T : Subgroup G) (markedV f.module)).rangeRestrict aT ∈
          center (checkedSylowMap (T : Subgroup G) (markedV f.module)).range := by
  obtain ⟨g, hz, hv, hv₁, hN, hT⟩ := d.exists_coordinate_witness
  obtain ⟨f, hf, hlocal, ha⟩ := d.construction_of_coordinate_witness g hz hv hv₁ hN hT
  exact ⟨f, ⟨g, hf⟩, hlocal, ha⟩

/-- A fixed choice of the constructed flag, for subsequent source statements
whose parameters depend on its marked points. -/
noncomputable def flag : FlagMarking T L V V₁ V₂ := d.construction.choose

/-- The chosen marking comes from the original module by a coordinate permutation. -/
theorem flag_relabel : ∃ g : Perm, d.flag.module = d.module.relabel g :=
  d.construction.choose_spec.1

/-- The chosen flag satisfies the literal local-index premise of Baumann promotion. -/
theorem flag_localIndex :
    ¬ 2 ∣ (Tv (T : Subgroup G) (markedV d.flag.module)).relIndex
      (normalizer (V : Set G) ⊓ Gv (markedV d.flag.module)) :=
  d.construction.choose_spec.2.1

/-- The chosen flag has the actual marked a as a nonidentity central point in
the image of C_T(v) in the literal quotient C_G(v)/⟨v⟩. -/
theorem flag_checkedPoint :
    ∃ aT : Tv (T : Subgroup G) (markedV d.flag.module),
      (aT : G) = markedA d.flag.module ∧
      (checkedSylowMap (T : Subgroup G) (markedV d.flag.module)).rangeRestrict aT ≠ 1 ∧
      (checkedSylowMap (T : Subgroup G) (markedV d.flag.module)).rangeRestrict aT ∈
        center (checkedSylowMap (T : Subgroup G) (markedV d.flag.module)).range :=
  d.construction.choose_spec.2.2
end A5Module.FlagSource

/-- The model indices supply exactly the local-index premise of the existing
Baumann promotion, on the same marked flag and literal quotient. -/
theorem localReductions_of_coordinate_witness
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (g : Perm)
    (hz : zpowers (Multiplicative.ofAdd (rho g z)) = d.preimage V₁)
    (hv : Multiplicative.ofAdd (rho g v) ∈ d.preimage V₂)
    (hv₁ : Multiplicative.ofAdd (rho g v) ∉ d.preimage V₁)
    (hN : (stabilizer d.image (rho g v)).index = 10)
    (hT : (stabilizer d.image (rho g v)).relIndex (d.imageSylow : Subgroup d.image) = 2)
    (M V₃ : Subgroup G)
    (e : EarlierLocal T L M V V₂ V₃ (markedZ (d.flagOfCoordinates g hz hv hv₁).module))
    (hcounter : IsA5Counterexample G)
    (hfusion : ControlsFusionOfZ (d.flagOfCoordinates g hz hv hv₁).module) :
    Nonempty (LocalReductions T L M V
      (markedZ (d.flagOfCoordinates g hz hv hv₁).module)
      (markedV (d.flagOfCoordinates g hz hv hv₁).module)) := by
  exact localReductions_of_flag T L M V V₁ V₂ V₃ (d.flagOfCoordinates g hz hv hv₁)
    e hcounter (d.localIndex_of_coordinate_indices (rho g v) hN hT) hfusion

/-- Apply the constructed flag's local index to the actual Baumann promotion.
The configuration assembly owner supplies the earlier local statements and
fusion control on this same marking; no coordinate or index premise remains. -/
theorem localReductions_of_flagSource
    {T : Sylow 2 G} {L V V₁ V₂ : Subgroup G}
    (d : FlagSource T L V V₁ V₂) (M V₃ : Subgroup G)
    (e : EarlierLocal T L M V V₂ V₃ (markedZ d.flag.module))
    (hcounter : IsA5Counterexample G)
    (hfusion : ControlsFusionOfZ d.flag.module) :
    Nonempty (LocalReductions T L M V (markedZ d.flag.module) (markedV d.flag.module)) := by
  exact localReductions_of_flag T L M V V₁ V₂ V₃ d.flag e hcounter d.flag_localIndex hfusion
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
