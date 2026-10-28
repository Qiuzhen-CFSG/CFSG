module

public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.NormalOffenderExclusion
public import CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Cases.Intersection.LowRows.Reduction
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.TwoFactors.FFBranch.Recognition.ClassificationComparison.FFAlternatives.Adequate
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Theory.AtlasPort.ExceptionalIsomorphisms.Support

/-!
# The extraspecial terminal row cannot have the source FF alternatives

The ambient quotient has order 108 and is solvable. Hence a full FF
alternative either contains a group too large for this ambient quotient,
or identifies the normal offender subgroup with S3 or S3 × S3. The two
normal-subgroup obstructions exclude those last cases. In the product case
the actual factor models force binary fields of order two, and their field
isomorphisms give the S3 factors; group order alone is not used for recognition.

Source: Aschbacher--Smith, B.5.6 and F.6.18, compared in the terminal
proof of 15.3.1, printed p.1155.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Centrality.Semilinear.Recognition
open CFSG.Quasithin.Chapter15.Section04.LocalSetup.TwoFactors.FFBranch.ClassificationComparison.FFAlternatives

namespace LowRows.Extraspecial

private theorem linearThree_card_lower (F : BinaryField) :
    168 ≤ Nat.card SL(3,F.Carrier) := by
  let f := Matrix.SpecialLinearGroup.map (n := Fin 3) (ZMod.castHom (dvd_refl 2) F.Carrier)
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    ext i j
    apply (ZMod.castHom (dvd_refl 2) F.Carrier).injective
    exact congrArg (fun c : SL(3,F.Carrier) => c.val i j) h
  rw [← Matrix.PSL3Two.card_SL]
  exact Nat.card_le_card_of_injective f hf

private theorem factor_card_lower {A : Type*} [Group A] (h : FactorModel A) :
    6 ≤ Nat.card A := by
  cases h with
  | linearTwo F e =>
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two]
    have hq : 2 ≤ Nat.card F.Carrier := Finite.one_lt_card
    have hh : 3 ≤ Nat.card F.Carrier ^ 2 - 1 := by
      have hs : 4 ≤ Nat.card F.Carrier ^ 2 := by nlinarith
      omega
    exact (by decide : 6 ≤ 2 * 3).trans (Nat.mul_le_mul hq hh)
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv]
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  | linearThree F _ e =>
    rw [Nat.card_congr e.toEquiv]
    exact (by decide : 6 ≤ 168).trans (linearThree_card_lower F)

private theorem factor_equiv_symmetricThree {A : Type*} [Group A]
    (h : FactorModel A) (hc : Nat.card A ≤ 18) :
    Nonempty (A ≃* Equiv.Perm (Fin 3)) := by
  cases h with
  | linearTwo F e =>
    rw [Nat.card_congr e.toEquiv, Atlas.card_sl_two] at hc
    have hsmall : Nat.card F.Carrier < 4 := by
      by_contra h
      have hq : 4 ≤ Nat.card F.Carrier := by omega
      have hh : 15 ≤ Nat.card F.Carrier ^ 2 - 1 := by
        have hs : 16 ≤ Nat.card F.Carrier ^ 2 := by nlinarith
        omega
      have hd := Nat.mul_le_mul hq hh
      omega
    have hn : F.degree = 1 := by
      have hp := F.degree_pos
      by_contra h
      have htwo : 2 ≤ F.degree := by omega
      have hpow := Nat.pow_le_pow_right (by decide : 0 < 2) htwo
      rw [← F.card_eq] at hpow
      norm_num at hpow
      omega
    let : Fintype F.Carrier := Fintype.ofFinite _
    let b : F.Carrier ≃+* ZMod 2 :=
      (ZMod.ringEquivOfPrime F.Carrier Nat.prime_two (by
        rw [← Nat.card_eq_fintype_card, F.card_eq, hn]
        norm_num)).symm
    exact ⟨e.trans ((Atlas.fieldEquivSL 2 b).trans
      SLTwoPermThree.sl2Two_equiv_perm_three.some)⟩
  | symmetricFive e =>
    rw [Nat.card_congr e.toEquiv] at hc
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at hc
  | linearThree F _ e =>
    have hh := linearThree_card_lower F
    rw [Nat.card_congr e.toEquiv] at hc
    omega

/-- An actual B.5.6 factor product of order at most 108 is S3 × S3.
The two equivalences come from the original `FactorModel` witnesses. -/
theorem product_equiv_symmetricThreePair {A : Type*} [Group A]
    {B C : Subgroup A} (c : InternalProduct B C) (hB : FactorModel B)
    (hC : FactorModel C) (hc : Nat.card A ≤ 108) :
    Nonempty (A ≃* (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))) := by
  have he : Nat.card B * Nat.card C = Nat.card A := by
    rw [← Nat.card_prod, Nat.card_congr c.equiv.toEquiv]
  have hb := factor_card_lower hB
  have hd := factor_card_lower hC
  have hBsmall : Nat.card B ≤ 18 := by nlinarith
  have hCsmall : Nat.card C ≤ 18 := by nlinarith
  obtain ⟨eB⟩ := factor_equiv_symmetricThree hB hBsmall
  obtain ⟨eC⟩ := factor_equiv_symmetricThree hC hCsmall
  exact ⟨c.equiv.symm.trans (eB.prodCongr eC)⟩

private theorem quasisimple_not_solvable {A : Type*} [Group A]
    (h : IsQuasisimple A) : ¬ Group.IsSolvable A := by
  let : IsQuasisimple A := h
  let : IsSimpleGroup (A ⧸ center A) := h.simple
  let : Nontrivial A := (QuotientGroup.mk'_surjective (center A)).nontrivial
  exact Group.IsPerfect.not_isSolvable A

end LowRows.Extraspecial

namespace SourceInput
variable {H : Type*} [Group H] [Finite H] {V : Subgroup H}
  [IsElementaryAbelian 2 (moduleClosure V)] (d : SourceInput V)

/-- Every adequate FF alternative is impossible for the actual extraspecial
terminal row. No extension action or equality of the two actors is assumed. -/
theorem no_extraspecial_row_of_adequateSourceAlternative
    (N : Subgroup (coreQuotient H)) [N.Normal] [IsExtraspecial 3 N]
    (hN : Nat.card N = 27)
    (q : Nonempty ((coreQuotient H ⧸ N) ≃* FSource.E4))
    (hB : AdequateSourceAlternative d.offenderAction) : False := by
  have hD : Nat.card (coreQuotient H) = 108 := by
    obtain ⟨e⟩ := q
    rw [card_eq_card_quotient_mul_card_subgroup N, Nat.card_congr e.toEquiv, hN]
    norm_num [FSource.E4, FSource.C]
  have hi : Nat.card d.offenderGroup ≤ 108 := by
    rw [← hD]
    exact Nat.card_le_card_of_injective d.offenderGroup.subtype d.offenderGroup.subtype_injective
  cases hB with
  | trivial h =>
    let : Subsingleton d.offenderGroup := h
    apply d.offender_ne_bot
    apply le_bot_iff.mp
    intro x hx
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subsingleton.elim (⟨x,hx⟩ : d.offenderGroup) 1))
  | quasisimple hq _ =>
    let : Group.IsNilpotent N := (IsExtraspecial.isPGroup 3 N).isNilpotent
    have hQ : IsPGroup 2 (coreQuotient H ⧸ N) := by
      obtain ⟨e⟩ := q
      have hE : IsPGroup 2 FSource.E4 := IsPGroup.of_card (n := 2) (by
        simp [FSource.E4, FSource.C])
      exact hE.of_equiv e.symm
    let : Group.IsNilpotent (coreQuotient H ⧸ N) := hQ.isNilpotent
    let : Group.IsSolvable (coreQuotient H) :=
      (Group.isSolvable_iff_subgroup_quotient N).mpr ⟨inferInstance, inferInstance⟩
    exact LowRows.Extraspecial.quasisimple_not_solvable hq inferInstance
  | symmetricThree c =>
    exact d.no_symmetricThree_offender_of_extraspecial_row N q c.equiv
  | twoFactors c =>
    obtain ⟨e⟩ := LowRows.Extraspecial.product_equiv_symmetricThreePair c.product
      (c.firstCase.factorModel _) (c.secondCase.factorModel _) hi
    exact d.no_symmetricThreePair_offender_of_extraspecial_row N q e
  | outerSixThree c =>
    exact d.no_outerSixThreeShape_of_extraspecial_row N hN q c
  | hyperplane c =>
    have hh := (Nat.card_le_card_of_injective c.first.subtype c.first.subtype_injective).trans hi
    rw [Nat.card_congr c.firstEquiv.toEquiv, Matrix.PSL3Two.card_SL] at hh
    omega

/-- The original full source interface also excludes the extraspecial row. -/
theorem no_extraspecial_row_of_sourceAlternative
    (N : Subgroup (coreQuotient H)) [N.Normal] [IsExtraspecial 3 N]
    (hN : Nat.card N = 27)
    (q : Nonempty ((coreQuotient H ⧸ N) ≃* FSource.E4))
    (hB : SourceAlternative d.offenderAction) : False :=
  d.no_extraspecial_row_of_adequateSourceAlternative N hN q (hB.toAdequate _)

end SourceInput
end CFSG.Quasithin.Chapter15.Section03.TerminalRecognition.Intersection

