module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceDegree.AbsoluteWindow.FortyExclusion.NormIdeal
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.GeneratorCover
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup
import all Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.FiveSubgroup.RationalFusion

/-!
# Identifying the literal HS center norm with a generator norm

The center of the marked order-125 subgroup has order five and is generated
by its certified commutator z. A checked permutation word conjugates z to
the published generator B. Thus the two cyclic norms generate the same
two-sided ideal in the actual binary HS group algebra.

The internal imports continue the packed permutation calculation without
exposing its implementation or changing the carrier. GAP supplies only the
candidate word; all identities are checked by the kernel.
Source: ATLAS HSG1-p100B0; Guralnick--Malle, Classification of 2F-modules I,
Proposition 5.1, HS paragraph, author-preprint p.16.
-/

public section
open scoped BigOperators MonoidAlgebra
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion
namespace AlgebraCertificate
open _root_.Sporadic.LeechRelated.HS
open FiveSubgroup

private def conjugatorMap (i : Fin 100) : Fin 100 :=
  ⟨(174821851947591824625423168740442121485076675022620927122876086055616957642341794897830183095399341896441494131577939931162889783687019303054582223430424021993952058930761621988365849172474748208383939652797834 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private def conjugatorInvMap (i : Fin 100) : Fin 100 :=
  ⟨(1151832169887668889195393427280607729985922899297344131736171386655281918110639701513931463999268279037271658224227848620990096701770290680153782120646868134437564312757866654493780970083991784895322858887290278 >>> (7 * i.val)) % 128 % 100, Nat.mod_lt _ (by decide)⟩

private theorem conjugatorLeft : ∀ i, conjugatorInvMap (conjugatorMap i) = i := by
  apply allFin
  decide +kernel

private def conjugatorPerm : Equiv.Perm (Fin 100) :=
  Theory.GroupTheory.tablePerm conjugatorMap conjugatorInvMap conjugatorLeft
    (Theory.GroupTheory.rightInverse_of_leftInverse_fin conjugatorLeft)

private def conjugatorWord : Carrier :=
  b⁻¹ * a⁻¹ * b * a⁻¹ * (b⁻¹ ^ 2) * a * b * a * b⁻¹ * a * (b⁻¹ ^ 2) * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b ^ 3) * a * (b⁻¹ ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * b⁻¹ * a⁻¹ * b * a * b * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a * b⁻¹ * a * (b⁻¹ ^ 2) * a * (b ^ 2) * a * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * b * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b⁻¹ * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * (b ^ 2) * a⁻¹ * (b⁻¹ ^ 2) * a⁻¹ * b

private theorem conjugatorPerm_eq_word :
    conjugatorPerm = (conjugatorWord : Equiv.Perm (Fin 100)) := by
  apply Equiv.ext
  apply allFin
  decide +kernel

private def conjugator : Carrier :=
  ⟨conjugatorPerm, conjugatorPerm_eq_word.symm ▸ conjugatorWord.property⟩

private theorem conjugator_relation : conjugator⁻¹ * z * conjugator = b := by
  apply Subtype.ext
  apply Equiv.ext
  apply allFin
  decide +kernel

private theorem b_eq_generatorB : b = generatorBElement := by
  apply Subtype.ext
  exact bPerm_eq_generator

/-- The actual commutator marking is conjugate to the published B generator. -/
theorem centerGenerator_conjugate_generatorB :
    ∃ c : Carrier, c⁻¹ * z * c = generatorBElement :=
  ⟨conjugator, conjugator_relation.trans b_eq_generatorB⟩

/-- The literal image of the center has five elements. -/
theorem card_fiveCenter : Nat.card fiveCenter = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  change Nat.card ((Subgroup.center subgroup).map subgroup.subtype) = 5
  rw [Subgroup.card_map_of_injective subgroup.subtype_injective]
  exact Subgroup.card_center_eq_prime_of_card_eq_prime_cube
    card_subgroup subgroup_not_commutative

private theorem z_mem_fiveCenter : z ∈ fiveCenter := by
  refine ⟨⟨z, RationalFusion.z_mem_subgroup⟩, ?_, rfl⟩
  apply Subgroup.mem_center_iff.mpr
  intro g
  exact Subtype.ext (RationalFusion.z_mem_centralizer g g.property)

private def centerPower (i : Fin 5) : fiveCenter :=
  ⟨z ^ i.val, fiveCenter.pow_mem z_mem_fiveCenter i.val⟩

private theorem centerPower_bijective : Function.Bijective centerPower := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let : Finite fiveCenter := inferInstanceAs (Finite (_ : Subgroup Carrier))
  apply (Nat.bijective_iff_injective_and_card centerPower).mpr
  constructor
  · intro i j h
    apply Fin.ext
    have ho : orderOf z = 5 :=
      orderOf_eq_prime RationalFusion.z_pow_five RationalFusion.z_ne_one
    exact pow_injOn_Iio_orderOf (x := (z : Carrier))
      (by simpa only [Set.mem_Iio, ho] using i.isLt)
      (by simpa only [Set.mem_Iio, ho] using j.isLt)
      (congrArg Subtype.val h)
  · simpa using card_fiveCenter.symm

set_option backward.isDefEq.respectTransparency false in
/-- The definition using the whole center is the five-term cyclic norm of z. -/
theorem fiveNorm_eq_sum_centerGenerator :
    fiveNorm = ∑ i : Fin 5, MonoidAlgebra.single (z ^ i.val) 1 := by
  classical
  let : Finite KnownSimple.SporadicName.hs.Carrier := inferInstanceAs (Finite Carrier)
  let := Fintype.ofFinite fiveCenter
  simpa only [fiveNorm, BinaryAlgebra, KnownSimple.SporadicName.Carrier,
    KnownSimple.SporadicName.carrierGroup] using (Fintype.sum_bijective centerPower centerPower_bijective
    (fun i => (MonoidAlgebra.single (z ^ i.val) 1 : BinaryAlgebra))
    (fun t : fiveCenter => (MonoidAlgebra.single t.val 1 : BinaryAlgebra)) (fun _ => rfl)).symm

/-- The short cyclic norm used in algebra calculations, on the actual generator. -/
@[expose] noncomputable def generatorNorm : BinaryAlgebra :=
  ∑ i : Fin 5, MonoidAlgebra.single (generatorBElement ^ i.val) 1

set_option backward.isDefEq.respectTransparency false in
private theorem conjugated_fiveNorm (c : Carrier)
    (hc : c⁻¹ * z * c = generatorBElement) :
    (MonoidAlgebra.single c⁻¹ 1 : BinaryAlgebra) * fiveNorm *
      MonoidAlgebra.single c 1 = generatorNorm := by
  let N : (ZMod 2)[Carrier] := fiveNorm
  change (MonoidAlgebra.single c⁻¹ 1 : (ZMod 2)[Carrier]) * N *
    MonoidAlgebra.single c 1 = ∑ i : Fin 5, MonoidAlgebra.single (generatorBElement ^ i.val) 1
  have hn : N =
      ∑ i : Fin 5, MonoidAlgebra.single (z ^ i.val) 1 := fiveNorm_eq_sum_centerGenerator
  rw [hn, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  simp only [MonoidAlgebra.single_mul_single, one_mul]
  congr 1
  rw [← hc]
  simpa only [inv_inv] using (conj_pow (i := i.val) (a := c⁻¹) (b := z)).symm

/-- Membership in the literal ideal, with the subgroup/conjugacy comparison discharged. -/
theorem generatorNorm_mem_fiveNormIdeal : generatorNorm ∈ fiveNormIdeal := by
  obtain ⟨c, hc⟩ := centerGenerator_conjugate_generatorB
  rw [← conjugated_fiveNorm c hc]
  apply fiveNormIdeal.mul_mem_right
  apply fiveNormIdeal.mul_mem_left
  exact TwoSidedIdeal.subset_span (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- The generator norm defines exactly the original two-sided ideal. -/
theorem fiveNormIdeal_eq_generatorNormIdeal :
    fiveNormIdeal = TwoSidedIdeal.span {generatorNorm} := by
  apply le_antisymm
  · apply TwoSidedIdeal.span_le.mpr
    rintro _ (rfl : _ = fiveNorm)
    obtain ⟨c, hc⟩ := centerGenerator_conjugate_generatorB
    let u : BinaryAlgebra := MonoidAlgebra.single c 1
    let v : BinaryAlgebra := MonoidAlgebra.single c⁻¹ 1
    have huv : u * v = 1 := by
      simp [u, v, MonoidAlgebra.single_mul_single, ← MonoidAlgebra.one_def]
    have he : u * generatorNorm * v = fiveNorm := by
      rw [← conjugated_fiveNorm c hc]
      change u * (v * fiveNorm * u) * v = fiveNorm
      calc
        _ = (u * v) * fiveNorm * (u * v) := by simp only [mul_assoc]
        _ = fiveNorm := by rw [huv, one_mul, mul_one]
    rw [← he]
    apply (TwoSidedIdeal.span {generatorNorm}).mul_mem_right
    apply (TwoSidedIdeal.span {generatorNorm}).mul_mem_left
    exact TwoSidedIdeal.subset_span (by simp)
  · exact TwoSidedIdeal.span_le.mpr (by
      rintro _ (rfl : _ = generatorNorm)
      exact generatorNorm_mem_fiveNormIdeal)

/-- Every actual two-sided generator-norm translate is a legitimate relation
for the original certificate ideal. -/
theorem generatorNorm_translate_mem (a b : KnownSimple.SporadicName.hs.Carrier) :
    MonoidAlgebra.single a 1 * generatorNorm * MonoidAlgebra.single b 1 ∈
      fiveNormIdeal := by
  apply fiveNormIdeal.mul_mem_right
  apply fiveNormIdeal.mul_mem_left
  exact generatorNorm_mem_fiveNormIdeal

end AlgebraCertificate
end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.AbsoluteWindow.FortyExclusion
