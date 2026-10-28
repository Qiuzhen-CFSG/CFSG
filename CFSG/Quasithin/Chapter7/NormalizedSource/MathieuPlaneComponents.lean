module
public import CFSG.Quasithin.Chapter8.Section02.HermitianSourceFieldFourRadicalPlacement
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents.Classification.Equivalences
public import CFSG.Quasithin.ChapterA.Section03.SQTKStructure.OrdinarySource.Complete
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter7.NormalizedSource.MathieuPlaneCore
public import CFSG.Quasithin.Chapter8.Section02.Normalizer.SmallOvergroups.QuasisimpleAction

/-!
# Recognizing the containing component in the cocode case

Suppose the original relative-normal residual has simple two-core quotient,
and every outside H-star group is nonsolvable. A nonquasisimple containing
component has an actual odd Fitting prime by A.3.6. Its Xi radical is
solvable, is normalized by the original Sylow, and escapes M by the
residual's relative normality and simple two-core quotient. Finite minimal
descent inside the radical Sylow join supplies a solvable H-star subgroup,
a contradiction. The whole radical join need not be minimal.

The action lemma converts a full marked GL3(2) action to the literal
intrinsic automorphism image. NonFFSourceMathieuM24Recognition discharges
all inputs on the original offender plane, including the nonsolvability
condition from its proved generation parameter two.
Source: Aschbacher--Smith 8.2.7 and 8.2.8(1), printed pp.717--719,
refs/quasithin.pdf. The generic radical-placement theorem in HermitianSource
has no Hermitian hypothesis and is used with the actual Mathieu residual.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
open Chapter1 Chapter1.Section02
universe u
variable {G : Type u} [Group G] [Finite G]

open Sporadic.Mathieu.M24LocalGeometry.PairOvergroups.QuotientConstruction

omit [Finite G] in
/-- A surjective linear action in marked plane coordinates realizes every
intrinsic automorphism of the original elementary subgroup. -/
theorem full_actionImage_of_linear_action (H U : Subgroup G)
    (hHU : H ≤ normalizer (U : Set G))
    (e : U ≃* Multiplicative Vector) (π : H →* BinaryLinear.GL Vector)
    (hπ : Function.Surjective π)
    (ha : ∀ (h : H) (u : U),
      (e (U.normalizerMonoidHom ⟨h,hHU h.property⟩ u)).toAdd = π h (e u).toAdd) :
    Chapter8.Section02.Normalizer.SmallOvergroups.actionImage H U = ⊤ := by
  apply top_unique
  intro α _
  let c : MulAut (Multiplicative Vector) := MulAut.congr e α
  let f : Vector →+ Vector :=
    { toFun := fun v => (c (Multiplicative.ofAdd v)).toAdd
      map_zero' := c.map_one
      map_add' := fun v w => c.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w) }
  let fL : BinaryLinear.GL Vector := LinearEquiv.ofBijective (f.toZModLinearMap 2) c.bijective
  obtain ⟨h,hh⟩ := hπ fL
  refine ⟨⟨h,hHU h.property⟩,h.property,?_⟩
  apply MulEquiv.ext
  intro u
  apply e.injective
  apply Multiplicative.toAdd.injective
  rw [ha,hh]
  change (e (α (e.symm (e u)))).toAdd = (e (α u)).toAdd
  rw [e.symm_apply_apply]

/-- A nonsolvable simple two-core residual forces quasisimplicity of its
containing local component when every outside H-star group is nonsolvable. -/
theorem containing_component_quasisimple
    (T : Sylow 2 G) (M N R K : Subgroup G)
    [Group.IsPerfect R] [IsSimpleGroup (R ⧸ pCore 2 R)]
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hQ : IsSQTK KnownSimple.IsKnownSimple
      ((K ⊔ (T : Subgroup G) : Subgroup G) ⧸ pCore 2 (K ⊔ (T : Subgroup G) : Subgroup G)))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hTR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hRK : R ≤ K) (hKN : K ≤ N)
    (hMR : M ⊓ N ≤ normalizer (R : Set G))
    (hnsol : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M, ¬ Group.IsSolvable H) :
    IsQuasisimple (K ⧸ pCore 2 K) := by
  classical
  have hA36 := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
  let X := radicalLocalImage (T : Subgroup G) K
  let ex : XiQuotient K ≃* X := radicalLocalQuotientEquiv hK
  let := pCore_isNilpotent (p := 2) (G := (K ⊔ (T : Subgroup G) : Subgroup G))
  have hX : X.IsCComponent := hK.1.map_quotient _
  have ha := proposition_1_2_1_four_earlier_conclusion hA36 hQ hK.1
  by_contra hn
  have hnX : ¬ IsQuasisimple X := fun hx => hn (hx.of_mulEquiv ex.symm)
  have hs := RadicalStructure.nonsimple_radical ha hnX
  have hsK : A36Natural (XiQuotient K) ∨ A36Nilpotent (XiQuotient K) :=
    hs.elim (fun hn => .inl (hn.of_mulEquiv ex.symm))
      (fun hn => .inr (hn.of_mulEquiv ex.symm))
  let : Nontrivial X := (nontrivial_iff_ne_bot _).mpr hX.ne_bot
  let : Nontrivial (XiQuotient K) := ex.symm.injective.nontrivial
  have hfit : Nat.card (fittingSubgroup (XiQuotient K)) ≠ 1 := by
    intro hc
    have hg : generalizedFitting (XiQuotient K) = ⊥ :=
      (hsK.elim And.left And.left).trans (card_eq_one.mp hc)
    have hh := Theory.GroupTheory.centralizer_generalizedFitting_le (XiQuotient K)
    have hb : centralizer ((⊥ : Subgroup (XiQuotient K)) : Set (XiQuotient K)) = ⊤ := by
      ext g
      simp [mem_centralizer_iff]
    rw [hg,hb] at hh
    exact top_ne_bot (le_antisymm hh bot_le)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hfit
  let : Fact p.Prime := ⟨hp⟩
  have hp3 := (RadicalStructure.radical_core hsK hd).2.1
  have ho : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  have hXi : XiMember (T : Subgroup G) (XiP p K) :=
    ⟨XiP_isPPerfect p K,XiP_invariant p hTK,XiP_join_mem_H p hK,
      ⟨p,hp,ho,(XiP_oddQuotient_of_A36 hA36 hK hQ hn ho hd).2⟩,
      RadicalActions.XiP_irreducible_of_A36 hA36 hK hQ hn hTK ho hd⟩
  have hout := Chapter8.Section02.HermitianSource.radical_not_le_relative_normalizer
    hA36 hK hQ hTK hTR hRK hKN hMR hn ho hd hXi
  let J := XiP p K ⊔ (T : Subgroup G)
  let : Group.IsSolvable (XiP p K) := hXi.isSolvable
  let : Group.IsNilpotent (T : Subgroup G) := T.isPGroup'.isNilpotent
  let : Group.IsSolvable J := Group.isSolvable_sup_of_normalizes _ _ hXi.invariant
  have hJ : J ∈ Chapter1.HOver G (T : Set G) := ⟨hXi.join_mem_H,fun _ ht => mem_sup_right ht⟩
  have hJM : ¬ J ≤ M := fun hj => hout (le_sup_left.trans hj)
  let S : Set (Subgroup G) := {Y | (Y ∈ Chapter1.HOver G (T : Set G) ∧ ¬ Y ≤ M) ∧ Y ≤ J}
  obtain ⟨H,hmin⟩ := (Set.toFinite S).exists_minimalFor id S ⟨J,⟨hJ,hJM⟩,le_rfl⟩
  have hHJ : H ≤ J := hmin.1.2
  have hH : H ∈ Chapter3.HStar (T : Subgroup G) M :=
    ⟨hmin.1.1,fun Y hY hYH => hmin.2 ⟨hY,hYH.trans hHJ⟩ hYH⟩
  exact hnsol H hH (Group.isSolvable_of_isSolvable_injective (inclusion_injective hHJ))

end CFSG.Quasithin.Chapter7.NormalizedSource.MathieuTrio
