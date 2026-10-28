module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction.Constrained.Alternatives
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.LargeActionExclusion.ComponentReduction

/-!
# The literal block layer and fixed plane in the binary SL3 branch

The fixed plane centralizes the residual of `M ∩ L` by monotonicity, before
any identification of the residual of `C_G(V₁)`. The supplied parabolic
centralizer identity therefore makes it centralize L. Restriction retains
the selected C-component in that literal centralizer.

The moving-section bound below keeps both exchanged rows until the order
of the containing section excludes the sixteen-element plane. Constructing
that section and identifying the later residual remain source obligations.

Source: Aschbacher--Smith 15.1.24(2), printed p.1101.
-/

public section
open Subgroup Representation Representation.BinaryOffender Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
open ChapterC
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc V : Subgroup G}

/-- The source `U(L) = [O₂(L),L]`, embedded in the original ambient group. -/
@[expose] def linearThreeU (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (blockU d.L).map d.L.subtype

/-- The source `Y₀ = O²(M ∩ L)`, with its literal inclusion into G. -/
@[expose] def linearThreeY (d : CaseIComponentData T M Mc V) : Subgroup G :=
  (pResidual 2 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype

/-- The source section `U₂ = [C_{U(L)}(O₂(Y₀)),Y₀]`, without quotienting
away a possible central attachment of the block layer. -/
@[expose] def linearThreeSection (d : CaseIComponentData T M Mc V) : Subgroup G :=
  ⁅d.linearThreeU ⊓ centralizer (d.linearThreeY.pCoreIn 2 : Set G),d.linearThreeY⁆

/-- The plane already centralizes the selected parabolic's two-residual. -/
theorem fixedPlane_centralizes_linearThreeY (d : CaseIComponentData T M Mc V) :
    d.nineFixedPlane ≤ centralizer (d.linearThreeY : Set G) :=
  inf_le_right.trans (centralizer_le (embedded_pResidual_mono 2
    (inf_le_inf_left M d.L_component.1)))

/-- The centralizer identity gives fixed-plane centralization without any
three-rank-two assertion about the binary SL3 quotient. -/
theorem ConstrainedL3Alternative.fixedPlane_centralizes
    {d : CaseIComponentData T M Mc V} (a : d.ConstrainedL3Alternative)
    (hTM : (T : Subgroup G) ≤ M) (h : PreparedChosenModule T M V) :
    d.nineFixedPlane ≤ centralizer (d.L : Set G) := by
  have hr : (primeToResidual 3 (M ⊓ d.L : Subgroup G)).map (M ⊓ d.L).subtype ≤
      d.nineCubic := embedded_primeToResidual_mono 3
        (inf_le_inf_left M d.L_component.1)
  have hc := (d.fixedPlane_le_sylow_cubicCentralizer hTM h).trans
    (inf_le_inf_left d.S (centralizer_le hr))
  exact (hc.trans a.centralizers.le).trans inf_le_right

/-- The same selected component persists in the fixed-plane centralizer. -/
theorem ConstrainedL3Alternative.component_in_fixed_centralizer
    {d : CaseIComponentData T M Mc V} (a : d.ConstrainedL3Alternative)
    (s : d.ExchangedSource) (hTM : (T : Subgroup G) ≤ M)
    (h : PreparedChosenModule T M V) :
    (d.L.subgroupOf (centralizer (d.nineFixedPlane : Set G))).IsCComponent := by
  exact d.L_isCComponent_in_G1.subgroupOf_of_le
    (le_centralizer_iff.mp (a.fixedPlane_centralizes hTM h))
    (centralizer_le s.marked_le_fixed)

/-- Once the actual containing section has order four, the plane equals it
and the sixteen-element row is excluded by subgroup cardinality. -/
theorem ExchangedSource.row_four_of_linearThreeSection
    {d : CaseIComponentData T M Mc V} (s : d.ExchangedSource)
    (hV : d.nineMovingPlane ≤ d.linearThreeSection)
    (hcard : Nat.card d.linearThreeSection = 4) :
    d.row = .four ∧ Nat.card d.Z1 = 2 ∧ Nat.card d.nineFixedPlane = 4 ∧
      d.nineMovingPlane = d.linearThreeSection := by
  have hb := Nat.card_le_card_of_injective (inclusion hV) (inclusion_injective hV)
  rw [hcard] at hb
  rcases s.sizes with hs | hs
  · refine ⟨hs.1,hs.2.1,hs.2.2.1,?_⟩
    exact eq_of_le_of_card_ge hV (by rw [hcard,hs.2.2.2])
  · have hh := hs.2.2.2
    omega

end CFSG.Quasithin.Chapter15.Section01.CaseIComponentData
