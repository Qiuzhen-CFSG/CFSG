module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceNonMathieuHermitianFieldFourOrdinaryRadical
public import CFSG.Quasithin.Chapter7.NormalizedSource.NonMathieuHermitianRadicalDisplacement

/-!
# The original nine-space is the ordinary pushing-up module

The tensor marking supplies the original order 512 and the non-FF setup
supplies its zero fixed space. On the same ordinary J₄ component, the
three-free native centralizer removes the central kernel in L/O₂(L).
The small-quotient action theorem then identifies the full radical
commutator with the original module, so the auxiliary module W is exactly
that module. The full covering-component residual normalizer preserves it.

The final application constructs this strengthened witness for the actual
escaping noncubic actor. These are inputs to the ordinary J₄ exclusion;
the whole odd-normalizer containment and 8.2.7--13 are still required.
Source: Aschbacher--Smith 4.2.13 and 4.4.3, printed pp.611--612,623,
as used in 8.2.7, p.718, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open Representation.HermitianTensorThree Representation.HermitianTensorThree.ImageOuter
open scoped IsMulCommutative MatrixGroups Pointwise
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open ChapterE ChapterB.QuasisimpleSource ChapterK.Linear.Recognition
open ChapterG.Section09.DefiningCharacteristic.LinearThreeRecognition
open Chapter4 Chapter4.Section04 Chapter4.Section04.NormalizedRankOneOddControl
open Chapter4.Section02.RankOneReciprocalEscape
open Chapter8.Section02.HermitianSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

/-- The literal tensor marking recovers the original module and controls
its full radical commutator and covering-component residual normalizer. -/
theorem sourceOrbit_hermitian_ordinary_radical_displacement
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {A J H W : Subgroup G} (hw : Witness L D.sourceOrbit A J H W)
    (K : Subgroup H) (hK : IsComponent H K) :
    W = D.sourceOrbit ∧ center (L ⧸ pCore 2 L) = ⊥ ∧
      ⁅J.pCoreIn 2,(solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype⁆ =
        D.sourceOrbit ∧
      normalizer (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).comap
        (H.subtype.comp K.subtype) : Set K) ≤
        normalizer (D.sourceOrbit.comap (H.subtype.comp K.subtype) : Set K) := by
  obtain ⟨e⟩ := D.sourceOrbit_hermitian_field_four_ordinary_janko
    h hmany hV hnon d B eQ hfield hw K hK
  have hw' : Witness L V A J H W := by simpa only [hV] using hw
  have hfix : V ⊓ centralizer (L : Set G) = ⊥ :=
    (D.sourceOrbit_fixed_and_thompson_of_many h hmany hnon).1
  have hcard : Nat.card V = 512 := by
    rw [hV]
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.sourceOrbit)
    change Nat.card D.sourceOrbit = _ at hc
    rw [Nat.card_zmod,(D.hermitianOrbitCoordinates 1 d).finrank_eq,finrank_binary] at hc
    exact hc
  have hfour : Nat.card B.Carrier = 4 := by rw [B.card_eq,hfield]; decide
  have heq := D.sourceOrbit_hermitian_ordinary_auxiliary_module_eq_of_card
    h.toHypothesis1221 hfix hcard eQ hfour hw' K hK e
  have hk := D.sourceOrbit_hermitian_ordinary_center_kernel_of_card
    h.toHypothesis1221 hfix hcard eQ hfour hw' K hK e
  have hc := D.sourceOrbit_hermitian_ordinary_radical_commutator_of_card
    h.toHypothesis1221 hfix hcard eQ hfour hw' K hK e
  have hn := D.sourceOrbit_hermitian_ordinary_cover_module_normalizer_of_card
    h.toHypothesis1221 hfix hcard eQ hfour hw' K hK e
  exact ⟨heq.trans hV,hk.2.2.1,hc.trans hV,by simpa only [hV] using hn⟩

/-- Every actual escaping noncubic actor has an ordinary witness whose
pushing-up module is the original nine-space, with its full commutator retained. -/
theorem sourceOrbit_hermitian_field_four_oddActor_original_module
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hV : V = D.sourceOrbit) (hnon : D.SourceOrbitNonFF)
    (d : ActionEquiv (D.orbitRepresentation.comp D.orbitComponent.subtype)
      (overgroupAction 1 (binaryImage 1)))
    (B : BinaryField) (eQ : (D.orbitComponent ⧸ center D.orbitComponent) ≃* PSL(3,B.Carrier))
    (hfield : B.degree = 2)
    {p : ℕ} (hp : p.Prime) (hgt : 3 < p)
    (A : Subgroup G) (hne : A ≠ ⊥) (hAe : IsElementaryAbelian p A)
    (hA : A ≤ normalizer (L : Set G) ⊓ centralizer (D.sourceOrbit : Set G))
    (hout : ¬ normalizer (A : Set G) ≤ normalizer (L : Set G)) :
    ∃ J H : Subgroup G, Witness L D.sourceOrbit A J H D.sourceOrbit ∧
      center (L ⧸ pCore 2 L) = ⊥ ∧
      ⁅J.pCoreIn 2,(solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype⁆ =
        D.sourceOrbit ∧
      ∃ K : Subgroup H, IsComponent H K ∧ K.Normal ∧
        ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H ∧
        Nonempty ((K ⧸ center K) ≃* Janko4.Model) ∧
        normalizer (((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype).comap
          (H.subtype.comp K.subtype) : Set K) ≤
          normalizer (D.sourceOrbit.comap (H.subtype.comp K.subtype) : Set K) := by
  obtain ⟨J,H,W,hw,K,hK,hn,houtK,_,_,he⟩ :=
    D.sourceOrbit_hermitian_field_four_oddActor_pushingUp
      h hmany hV hnon d B eQ hfield hp hgt A hne hAe hA hout
  obtain ⟨hW,hZ,hcomm,hN⟩ := D.sourceOrbit_hermitian_ordinary_radical_displacement
    h hmany hV hnon d B eQ hfield hw K hK
  exact ⟨J,H,hW ▸ hw,hZ,hcomm,K,hK,hn,houtK,he,hN⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
