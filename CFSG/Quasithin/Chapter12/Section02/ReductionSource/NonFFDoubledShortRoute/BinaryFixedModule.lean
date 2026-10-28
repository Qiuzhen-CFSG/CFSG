module

public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.NonFFSourceDoubledBinaryC48Residual
public import Theory.Representation.BinaryNaturalDual.SmallRepeatedEmbedding

/-!
# Excluding repeated-natural markings of the actual C.4.8 fixed module

The source orbit is a submodule of the fixed-space commutator W from C.4.8,
not necessarily all of W. Inclusion is an injective linear map intertwining
conjugation by the original intersection residual LH. The retained quotient
coordinates make the two original summands inequivalent simple modules of
rank three. The small repeated-module theorem excludes their sum from copies
of any module of rank less than six. In particular, either repeated-natural
marking of W in C.4.8(2) contradicts the original orbit inclusion.

The last theorem applies this to the literal star module, full two-core and
fixed-space commutator already constructed from the original reciprocal
witness. The quotient LH R/R and its quotient map are unchanged; the proposed
marking of W need not agree with the original natural-dual marking. Neither
an equality of the orbit and W nor a classification of the orbit is assumed.

This proves the repeated-natural transport step. Producing the parabolic
marking and classification of W, excluding the ordinary component branch,
and assembling the other doubled rows remain with this task's source assembly.
Source: Aschbacher--Smith B.5.1 and the final paragraph of C.4.8, printed
pp.99 and 154, applied in 4.4.3(i.a), p.619, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter4 Chapter4.Section04 Chapter4.Section02.RankOneReciprocalEscape
open ChapterB.QuasisimpleSource Chapter7.NormalizedSource
open ChapterC.Section04.BinaryThreeNaturalDualExclusion
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
open BinaryLinear.OuterCyclic
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  (D : ChosenModule T L V)

private theorem no_small_repeated_overmodule
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    {W : Subgroup G} [IsElementaryAbelian 2 W] (hOW : D.sourceOrbit ≤ W)
    (hLW : ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) ≤
      normalizer (W : Set G))
    {Y : Type*} [AddCommGroup Y] [Module (ZMod 2) Y] [FiniteDimensional (ZMod 2) Y]
    (σ : Representation (ZMod 2)
      ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) Y)
    (hdim : Module.finrank (ZMod 2) Y < 6)
    (m : ℕ) (N : Additive W ≃ₗ[ZMod 2] (Fin m → Y))
    (hN : ∀ l w, N (doubledSeedAction _ W hLW l w) = fun i => σ l (N w i)) : False := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  have hLH : LH ≤ L := (map_subtype_le _).trans inf_le_left
  obtain ⟨_,_,_,_,_,_,e,_,E,hE,_,_⟩ :=
    D.sourceOrbit_binary_witness_coordinates h hd F hF hmodel hw
  let q : LH →* BinaryLinearThree.Group :=
    e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 LH))
  let p : LH →* LinearGroup 3 := (slEquivLinear 3).toMonoidHom.comp q
  have hp : Function.Surjective p := (slEquivLinear 3).surjective.comp
    (e.surjective.comp (QuotientGroup.mk'_surjective _))
  let i : Additive D.sourceOrbit →ₗ[ZMod 2] Additive W :=
    (inclusion hOW).toAdditive.toZModLinearMap 2
  have hi : Function.Injective i := inclusion_injective hOW
  have hiE (l : LH) (v : Additive D.sourceOrbit) :
      i (doubledSeedAction LH D.sourceOrbit
        (hLH.trans D.sourceOrbit_component_normalizes) l v) =
      doubledSeedAction LH W hLW l (i v) := by
    rfl
  have he (l : LH) (v : BinaryNaturalDual.CoordinateSpace 3) :
      E.symm (BinaryNaturalDual.naturalDualRepresentation (p l) v) =
      doubledSeedAction LH D.sourceOrbit
        (hLH.trans D.sourceOrbit_component_normalizes) l (E.symm v) := by
    apply E.injective
    rw [E.apply_symm_apply,hE,E.apply_symm_apply]
    exact LinearMap.congr_fun
      (BinaryLinearThree.NaturalDual.naturalDualRepresentation_slEquivLinear (q l)) v
  let τ := repeated σ m
  apply BinaryNaturalDual.no_small_repeated_embedding (by decide : 3 ≤ 3)
    p hp σ τ (fun _ _ _ => rfl) (by simpa using hdim)
    ((N.toLinearMap.comp i).comp E.symm.toLinearMap)
    (N.injective.comp (hi.comp E.symm.injective))
  intro l v
  change N (i (E.symm _)) = _
  rw [he,hiE,hN]
  rfl

/-- An elementary overmodule of the original orbit cannot carry either repeated
natural C.4.8 marking. The original residual acts through the literal LH R/R;
only the actual invariant inclusion is used to transport the obstruction. -/
theorem sourceOrbit_binary_witness_no_repeated_overmodule
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    {W : Subgroup G} [IsElementaryAbelian 2 W] (hOW : D.sourceOrbit ≤ W)
    (hLW : ((solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype) ≤
      normalizer (W : Set G)) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let R := J.pCoreIn 2
    let := normal_subgroupOf_sup_of_le_normalizer
      ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
        hw.2.2.2.2.2.2.1.span_normalizes_radical)
    ∀ (d : ℕ), d = 3 ∨ d = 4 →
    ∀ (a : ((LH ⊔ R : Subgroup G) ⧸ R.subgroupOf (LH ⊔ R)) ≃* LinearGroup d)
      (m : ℕ) (N : Additive W ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space d)),
      (∀ l w, N (doubledSeedAction LH W hLW l w) =
        fun i => a (radicalQuotientMap LH R l) (N w i)) → False := by
  let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
  let R := J.pCoreIn 2
  let := normal_subgroupOf_sup_of_le_normalizer
    ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
      hw.2.2.2.2.2.2.1.span_normalizes_radical)
  dsimp only
  intro d hdims a m N hN
  let p := a.toMonoidHom.comp (radicalQuotientMap LH R)
  let σ := (BinaryNaturalDual.linearNatural d).comp p
  apply D.no_small_repeated_overmodule h hd F hF hmodel hw hOW hLW σ _ m N hN
  simpa [BinaryLinear.OuterCyclic.Space,Module.finrank_pi] using
    (show d < 6 by omega)

/-- The literal p.154 fixed-space commutator W cannot have either repeated-natural
marking. Its elementary structure, orbit inclusion and normalization are all
constructed from the original constrained reciprocal witness. This leaves the
source classification of W to be proved; it assumes no marking on the orbit. -/
theorem sourceOrbit_binary_witness_fixed_moved_no_repeated_natural
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (hd : D.MarkedDoubled)
    (F : BinaryField) (hF : F.degree = 1) (hmodel : D.HasNaturalThreeSeed F)
    {A J H U : Subgroup G} (hw : Witness L V A J H U)
    (hWJ : D.sourceOrbit ≤ J.pCoreIn 2)
    (hJC : J.pCoreIn 2 ≤ sectionCentralizerIn (normalizer (L : Set G)) L)
    (K : Subgroup H) (hK : K.IsCComponent)
    (hq : IsQuasisimple (K ⧸ pCore 2 K))
    (hout : ¬ K ≤ (H ⊓ normalizer (L : Set G)).subgroupOf H)
    (hfK : generalizedFitting K = pCore 2 K) :
    let LH := (solvableResidual (L ⊓ H : Subgroup G)).map (L ⊓ H).subtype
    let R := J.pCoreIn 2
    let Q := (starV (K.map H.subtype) R).map (K.map H.subtype ⊔ R).subtype
    let W := ⁅Q ⊓ centralizer (LH.pCoreIn 2 : Set G),LH⁆
    let := (D.sourceOrbit_binary_witness_fixed_moved_action h hd F hF hmodel
      hw hWJ hJC K hK hq hout hfK).1
    let hLW : LH ≤ normalizer (W : Set G) :=
      (D.sourceOrbit_binary_witness_constrained_fixed_moved h hd F hF hmodel
        hw hWJ hJC K hK hq hout hfK).2.2
    let := normal_subgroupOf_sup_of_le_normalizer
      ((le_conjugateSpanBy LH (H ⊓ normalizer (L : Set G))).trans
        hw.2.2.2.2.2.2.1.span_normalizes_radical)
    ∀ (d : ℕ), d = 3 ∨ d = 4 →
    ∀ (a : ((LH ⊔ R : Subgroup G) ⧸ R.subgroupOf (LH ⊔ R)) ≃* LinearGroup d)
      (m : ℕ) (N : Additive W ≃ₗ[ZMod 2] (Fin m → BinaryLinear.OuterCyclic.Space d)),
      (∀ l w, N (doubledSeedAction LH W hLW l w) =
        fun i => a (radicalQuotientMap LH R l) (N w i)) → False := by
  have hdata := D.sourceOrbit_binary_witness_constrained_fixed_moved h hd F hF hmodel
    hw hWJ hJC K hK hq hout hfK
  let := (D.sourceOrbit_binary_witness_fixed_moved_action h hd F hF hmodel
    hw hWJ hJC K hK hq hout hfK).1
  exact D.sourceOrbit_binary_witness_no_repeated_overmodule h hd F hF hmodel hw
    hdata.1 hdata.2.2

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
