module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.SmallUnitaryDegree
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryCover

/-!
# Constructing the binary unitary actor, including the nonperfect endpoint

At fixed-field order two, the original characteristic-two condition makes
the actual six-dimensional Frattini section faithful. The generic SU3 cover
and its projective square put the section kernel inside the scalar subgroup.
The faithful PSU3(2) minimum degree eight rules out a nontrivial kernel, so
the full SU3(2) marking is constructed. Combining this with UnitaryCover gives
actor profiles for every positive binary field degree, in either orientation.

The original DGS panel orders and special radical identities are explicit;
the source-cover transport remains with the split-recognition producer.
No full actor bijection or perfectness is assumed in the field-two branch.

Sources: Fong--Seitz I (4D), (6A)(c), pp.21--23,37; DGS (11.8), pp.175--176.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped MatrixGroups IsMulCommutative
open BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P) (split : SplitData Q.tits)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
include e h

/-- Faithfulness on the literal six-dimensional section selects the full
field-two cover. The projective square bounds its possible kernel by scalars. -/
theorem marked_small_unitary_cover_injective
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) (hE : Nat.card E = 2^2)
    (hconj : ∀ x, J.conj x = x^2)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = 2^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = 2^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) : Function.Injective π := by
  have hf : Nat.card {x : E // J.conj x = x} = 2 := by
    simpa using FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 1
      (by decide) (by simpa using hE) (by simpa using hconj)
  have hc := (marked_unitary_section Q split e h J (n := 1) (by decide)
    (by simpa using hE) (by simpa using hf) hJ hm i j hij hVi hVj s ν
    (by simpa using hindexi) (by simpa using hindexj) hQi hderived hfrattini).2.1
  let V := (simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply marked_remainderFrattiniAction_injective Q e h split j s hVj
    ext v
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) hab)
  have hk : (ρ.comp π).ker ≤ J.specialToProjective.ker := by
    intro a ha
    have he : π a = 1 := hρ (ha.trans ρ.map_one.symm)
    rw [MonoidHom.mem_ker,←hπν,he,map_one,map_one]
  have hd : Module.finrank (ZMod 2) (Additive V) < 8 := by
    have hd := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at hd
    have he : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2^6 := by
      rw [←hd]
      exact hc
    have he' := Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) he
    omega
  have hinj := small_unitary_faithful_of_scalar_kernel J hE hconj hJ (ρ.comp π) hk hd
  exact fun _ _ he => hinj (congrArg ρ he)

/-- Construct the full actor profile for every positive binary field degree.
The field-two case uses the faithful original section, without perfectness. -/
theorem marked_unitary_profile_all_of_cover
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    Nonempty (UnitaryActorProfile Q split j J hVj ν) := by
  by_cases hn2 : 2 ≤ n
  · exact (marked_unitary_profile_of_cover Q split e h J hn2 hE hconj hJ
      hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini).1
  have hn1 : n = 1 := by omega
  subst n
  have hinj := marked_small_unitary_cover_injective Q split e h J
    (by simpa using hE) (by simpa using hconj) hJ hm i j hij hVi hVj s ν π hπν
    (by simpa using hindexi) (by simpa using hindexj) hQi hderived hfrattini
  let a := MulEquiv.ofBijective π ⟨hinj,hπ⟩
  refine ⟨⟨a.symm.toMonoidHom,a.symm.surjective,a.symm.injective,?_⟩⟩
  intro r
  have he := hπν (a.symm r)
  change ν (RootLocalCover.projection Q split j (a (a.symm r))) = _ at he
  rw [a.apply_symm_apply] at he
  simpa only [rankOneLocalEquiv_eq_projection,MulEquiv.coe_toMonoidHom] using he

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
