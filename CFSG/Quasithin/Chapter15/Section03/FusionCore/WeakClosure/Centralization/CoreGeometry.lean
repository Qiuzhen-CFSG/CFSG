module
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.CoordinateModel
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Centralization.Reductions
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.WeakClosure.Centralization.CoreGeometry.FiniteCalculations

/-!
# The rank-two dual core in orthogonal weak-closure centralization

For a conjugate `A = V^g ≤ T` that is not normalized by `V`, the actual
induced automizer has rank greater than one and its dual core is proper in
`V`. Compatible coordinates identify this automizer with an elementary
subgroup of `SL₂(2) ≀ C₂`. Its dihedral Sylow model forces order four.

The literal fixed-space calculation distinguishes its two possible Klein
four actions: one generates the entire four-space, and the other generates
an order-eight core with two fixed vectors. Properness excludes the former.
The same actual action gives `|A:C_A(V)|=4`; since `|A|=16`, the fixed group
has order four. All comparisons retain the conjugation action on `V`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), the second
case in the proof of 15.3.46(4), printed p.1141; E.3.30–32, pp.237–238,
and the generated-core convention of Definition F.4.41, p.294.
-/

public section
namespace CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization
open Subgroup ChapterE CoreGeometry
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {M V P : Subgroup G} [IsElementaryAbelian 2 V]

/-- The three actual core calculations in the second case of 15.3.46(4). -/
theorem core_calculations_of_not_normalizes
    (d : NaturalOrthogonalAction M V) (h : EarlierFusionInputs T M V P)
    (_hP : IsDefinitePlane d.form P) (k : OrthogonalCoordinateModel d P)
    (c : OrthogonalFusionCalculations T M V P d.form) (g : G)
    (hgT : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hn : ¬ V ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    Nat.card (automizerDualCore V
      (inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) 1) = 8 ∧
    Nat.card (automizerDualCore V
      (inducedAutomizer V (V.map (MulAut.conj g).toMonoidHom)) 1 ⊓
        centralizer (V.map (MulAut.conj g).toMonoidHom : Set G) : Subgroup G) = 2 ∧
    Nat.card (V.map (MulAut.conj g).toMonoidHom ⊓ centralizer (V : Set G) :
      Subgroup G) = 4 := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let _ : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hAM : A ≤ M := hgT.trans h.sylow_le
  let J := coordinateImage k.action hAM
  let _ : IsElementaryAbelian 2 J := coordinateImage_elementary k.action hAM
  have hJ : Nat.card J = 4 := by
    rw [← Nat.card_congr (coordinateImageEquiv k.action hAM).toEquiv]
    exact card_inducedAutomizer_conjugate d h k c g hgT hn
  have hproper : imageCore J ≠ ⊤ := imageCore_ne_top k.action hAM
    (dualCore_one_lt d h c g hgT hn)
  obtain ⟨hcore, hfixed⟩ := coordinate_core_sizes J hJ hproper
  exact ⟨(card_ambient_core k.action hAM).trans hcore,
    (card_ambient_core_fixed k.action hAM).trans hfixed,
    card_conjugate_fixed d h k c g hgT hn⟩
end CFSG.Quasithin.Chapter15.Section03.FusionCore.Centralization
