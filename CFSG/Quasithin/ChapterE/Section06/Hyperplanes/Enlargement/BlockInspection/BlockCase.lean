module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.Inputs
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.LocalFacts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.FactorType
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.FixedSpace
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.Contracts
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.ModelAction
public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase.NaturalCentralizers

/-!
# Exclusion of a proper chi-zero block overgroup

C.1.9 first gives C_V(X) = A. Choose v in U outside A and realize its
nontrivial action on X by a noncentral element z of the omega-center of
X's common Sylow intersection with Q. Since v centralizes L, so does z.
The intrinsic natural-block calculation puts C_X(z) in the class of
two-groups, contradicting the nontrivial two-perfect short group L.

ModelAction identifies X with an actual E.6.7 factor in ⟨X,Q⟩, whose
characteristic-two hypothesis is proved using relative subnormality and
odd-core vanishing. Corank two forces the natural SL₂(4) module and excludes
the distinct A₅ deleted permutation module. NaturalCentralizers proves
the intrinsic centralizer bound, including the allowed central extensions.

The final theorem discharges both calculations and proves ProperBlockExclusion
from Hypothesis E.6.1 and the exact earlier E.6.7, C.1.9 and E.6.21 inputs.
Hypothesis E.6.15 is unnecessary for this step. The actual overgroup X is
an input; constructing it belongs to the separate lifting argument.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.23,
printed p.254 (PDF p.265), using E.6.7, printed p.246.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
universe u
variable {G : Type u} [Group G] [Finite G] {M V : Subgroup G}

private theorem short_not_twoGroup {L : Type*} [Group L] (hL : ChapterC.IsShort L) :
    ¬ IsPGroup 2 L := by
  intro hp
  have hb : (⊥ : Subgroup L) = ⊤ := hL.twoPerfect ⊥ inferInstance
    (hp.of_equiv QuotientGroup.quotientBot.symm)
  exact hL.blockU_ne_bot (le_bot_iff.mp (le_top.trans_eq hb.symm))

/-- A noncentral inner actor from U puts L in a two-group centralizer. -/
theorem exclusion_of_natural_overgroup [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    (hnatural : NaturalFourCentralizers.{u})
    {U A L X : Subgroup G} (hU : U ∈ obstructionFamily M V)
    (hUh : IsHyperplane V U) (hAU : A ≤ U) (hc : subgroupCorank V A = 2)
    (hL : SmallBlock U L) (he : ¬ L ≤ M)
    (hLX : L < X) (hX : CentralizerBlock A X)
    (hmodel : NaturalOvergroup (sylowCentralizer (T : Subgroup G) V) V X) : False := by
  have hfixed := proper_block_fixedSpace h h19 h21 hU hUh hAU hc hL he hLX hX
  have hn : ¬ U ≤ A := by
    intro hUA
    have heq := le_antisymm hUA hAU
    have := hUh.2
    rw [heq, hc] at this
    contradiction
  obtain ⟨v, hvU, hvA⟩ := SetLike.not_le_iff_exists.mp hn
  have hvC : v ∉ centralizer (X : Set G) := fun hv =>
    hvA (hfixed ▸ show v ∈ V ⊓ centralizer (X : Set G) from ⟨hUh.1 hvU, hv⟩)
  obtain ⟨htype, S, _, haction⟩ := hmodel
  obtain ⟨z, hzS, hzact⟩ := haction v (hUh.1 hvU)
  have hz : z ∉ center X := by
    intro hz
    apply hvC
    apply mem_centralizer_iff.mpr
    intro x hx
    have hzfix : z * (⟨x, hx⟩ : X) * z⁻¹ = ⟨x, hx⟩ := by
      rw [← mem_center_iff.mp hz ⟨x, hx⟩, mul_inv_cancel_right]
    have hvfix : v * x * v⁻¹ = x :=
      (hzact ⟨x, hx⟩).symm.trans (congrArg Subtype.val hzfix)
    exact (mul_inv_eq_iff_eq_mul.mp hvfix).symm
  have hp := hnatural X htype S z hzS hz
  let f : L →* X := Subgroup.inclusion hLX.le
  have hf : f.range ≤ centralizer ({z} : Set X) := by
    rintro _ ⟨l, rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    have hvfix : v * (l : G) * v⁻¹ = l := by
      rw [mem_centralizer_iff.mp (hL.1 l.property) v hvU, mul_inv_cancel_right]
    have hzfix : z * f l * z⁻¹ = f l :=
      Subtype.ext ((hzact (f l)).trans hvfix)
    exact (mul_inv_eq_iff_eq_mul.mp hzfix).symm
  have hpL : IsPGroup 2 L := (hp.to_le hf).of_injective f.rangeRestrict (by
    intro x y hxy
    exact Subtype.ext (congrArg (fun a : f.range => ((a : X) : G)) hxy))
  exact short_not_twoGroup (hL.2.2.elim (fun h => h.2.1) (fun h => h.2.1)) hpL

/-- Conditional interface for assembling the model action and centralizer calculation. -/
theorem properBlockExclusion_of_calculations [IsElementaryAbelian 2 V]
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h19 : BlockCommutationInput G) (h21 : OddCoreFree V)
    (hmodels : ProperOvergroupModels T M V) (hnatural : NaturalFourCentralizers.{u}) :
    ProperBlockExclusion M V := by
  intro U hU hUh L hL he A hA hAU hc X hLX hX htype
  exact exclusion_of_natural_overgroup h h19 h21 hnatural hU hUh hAU hc hL he hLX hX
    (hmodels U hU hUh L hL he A hA hAU hc X hLX hX htype)

/-- The proper chi-zero block alternative in E.6.23 is impossible. Both the
actual natural-module identification and its intrinsic centralizer calculation
are discharged; only the permitted exact earlier-source inputs remain. -/
theorem properBlockExclusion_of_e67
    {K : GroupClass} {T : Sylow 2 G} (h : HypothesisE61 K T M V)
    (h67 : InvariantSubspaces.BlockSelection.E67Input T M V)
    (h19 : BlockCommutationInput G) (h21 : OddCoreFree V) :
    ProperBlockExclusion M V := by
  let _ := h.elementary
  exact properBlockExclusion_of_calculations h h19 h21
    (properOvergroupModels_of_e67 h h67 h19 h21) naturalFourCentralizers

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.Enlargement.BlockInspection.BlockCase
