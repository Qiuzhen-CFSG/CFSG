module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.Displacements
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Normalization

/-!
# The reciprocal common-axis index

The kernel of the surjective A-parameter in the forward natural action is
exactly C_A(V_H). Thus its index in A is q, before reciprocal field linearity
or a common field-hyperplane has been established. The positive multiplicity
is necessary: with no natural summands every vector is fixed.

Source: Aschbacher--Smith, 11.3.7(4), refs/quasithin.pdf, printed p.773.
-/

@[expose] public noncomputable section
open Subgroup Matrix
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
open CFSG.Quasithin.ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] {T : Sylow 2 G} {H A : Subgroup G} {F : BinaryField}
namespace NaturalSylowCoordinates
variable {m : ℕ} (n : NaturalSylowCoordinates T H A F m)

/-- For positive multiplicity the original action parameter detects exactly
those original A-elements centralizing the entire omega closure. -/
theorem parameter_eq_one_iff (hm : 0 < m) (a : A) :
    n.parameter a = 1 ↔ (a : G) ∈ centralizer (omegaClosure T H : Set G) := by
  constructor
  · intro ha w hw
    have he : localAction T H (inclusion n.le_local a) ⟨w,hw⟩ = ⟨w,hw⟩ := by
      apply n.coordinates.injective
      apply Multiplicative.toAdd.injective
      funext i
      rw [n.intertwines, ha]
      ext j
      fin_cases j <;> simp
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  · intro ha
    let w := n.coordinates.symm (Multiplicative.ofAdd (fun _ => ![0,1]))
    have hw : localAction T H (inclusion n.le_local a) w = w := by
      apply Subtype.ext
      exact mul_inv_eq_iff_eq_mul.mpr (ha w w.property).symm
    have he := congrFun (n.intertwines a w ⟨0,hm⟩) 0
    rw [hw] at he
    have hc : (n.coordinates w).toAdd = fun _ => ![0,1] := by
      simp only [w, MulEquiv.apply_symm_apply]; rfl
    rw [hc] at he
    apply Multiplicative.toAdd.injective
    simpa using he.symm

/-- The literal relative centralizer is the kernel of the forward parameter. -/
theorem parameter_ker_eq (hm : 0 < m) :
    n.parameter.ker = (centralizer (omegaClosure T H : Set G)).comap A.subtype := by
  ext a
  exact n.parameter_eq_one_iff hm a

include n in
/-- The reciprocal common fixed subgroup has index q in the original A. -/
theorem centralizer_index (hm : 0 < m) :
    ((centralizer (omegaClosure T H : Set G)).comap A.subtype).index =
      Nat.card F.Carrier := by
  rw [← n.parameter_ker_eq hm]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective
    n.parameter n.surjective).toEquiv

include n in
/-- The exact binary corank required in source 11.2.2(3). -/
theorem centralizer_corank (hm : 0 < m) :
    CFSG.Quasithin.ChapterE.subgroupCorank A
      (A ⊓ centralizer (omegaClosure T H : Set G)) = F.degree := by
  rw [CFSG.Quasithin.ChapterE.subgroupCorank, inf_relIndex_left]
  change Nat.log 2 ((centralizer (omegaClosure T H : Set G)).comap A.subtype).index = _
  rw [n.centralizer_index hm, F.card_eq, Nat.log_pow (by decide : 1 < 2)]

end NaturalSylowCoordinates
open LocalGeometry CFSG.Quasithin.ChapterE
variable [Finite G] {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

/-- The actual forward coordinates discharge the action-corank premise of
the published normalization theorem, without assuming reciprocal linearity. -/
theorem source_normalizes_of_natural_coordinates
    (s : Hypothesis1131At D S U₁ H)
    (c : Coordinates D S.field) (f : InvariantFlag c)
    (hline : U₁ = c.binarySubspace (f.space 0))
    (hparameters : (S.field.degree : ℕ∞) < globalR V ∨
      (Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
        globalR V = S.field.degree ∧
        ¬ centralizer (f.Vi 1 : Set G) ≤ normalizer (L : Set G)))
    (g : G) {m : ℕ} (hm : 0 < m)
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m) :
    omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G) :=
  source_omegaClosure_normalizes_conjugate s c f hline hparameters g
    (n.centralizer_corank hm).le

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore
