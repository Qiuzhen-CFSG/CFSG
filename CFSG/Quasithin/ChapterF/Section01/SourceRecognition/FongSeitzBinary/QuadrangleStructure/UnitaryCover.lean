module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.SectionFaithfulness
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.UnitarySection
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.PanelProjection
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitarySixA
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryIdentificationApplications
public import CFSG.Quasithin.ChapterK.Section01To04.RankOne.UnitaryRecognition.MinimalDegree

/-!
# Selecting the full unitary root actor from its source cover

For q = 2^n with n at least two, the literal unitary radical has a
Frattini quotient of order q^6 and a nontrivial root-reflection action.
The minimum-degree theorem makes this section irreducible; natural-module
recognition then proves that a surjective SU3 cover is injective. This
constructs the full actor profile used by the existing (6A)(c) assembly,
including its projective square and scalar kernel, in either orientation.

The original perfect-factor adapter constructs the covering map from either
DGS quotient alternative, special or projective. The general adapter retains
the surjective covering map and its projective square as the independent
source-cover transport input; it assumes neither injectivity nor a target
actor equivalence. The original SourceQuotient application retains the
literal representatives and both endpoint maps.

The section-order, reflection, and faithful-section results include q = 2.
Cover selection and unitary-side irreducibility in that nonperfect case
remain separate: none of
the cover-selection theorems below claims to handle n = 1.

Sources: Fong--Seitz I (4D), (6A)(c), pp.21--23,37; DGS (11.8)(c),(f),
pp.175--176. Generic source-cover transport is supplied by split recognition;
compatible natural/Hermitian realizations remain with the unitary consumer.
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

/-- The minimum-degree theorem selects the full cover from a surjective
covering map; its injectivity is a conclusion. -/
theorem unitary_cover_injective
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hphi : (frattini (simpleRemainder Q split j)).map
        (simpleRemainder Q split j).subtype =
      (center (rootAt Q split j (Q.simple i))).map
        (rootAt Q split j (Q.simple i)).subtype)
    (hcard : Nat.card (simpleRemainder Q split j) = (2^n)^7) :
    Function.Injective π := by
  let : Algebra (ZMod 2) E := ZMod.algebra E 2
  let V := (simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)
  let ρ := elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)
  let : IsIrreducible ρ := unitary_frattini_irreducible_of_cover Q split J hn hE hconj hJ
    hm i j hij hVj s ν π hπ hphi hcard
  let σ := ρ.comp π
  let : IsIrreducible σ := (irreducible_comp_surjective_iff π hπ ρ).mpr inferInstance
  have hnt := remainderFrattiniAction_nontrivial_of_cross_center Q split hm i j hij hVj s
    (hphi.le.trans (map_subtype_le _))
  have hnσ : ∃ g, σ g ≠ 1 := by
    obtain ⟨r,hr⟩ := hnt
    obtain ⟨g,rfl⟩ := hπ r
    refine ⟨g,fun he => hr ?_⟩
    ext v
    exact Additive.ofMul.injective
      (congrArg (fun f : Module.End (ZMod 2) (Additive V) => f (Additive.ofMul v)) he)
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hE hconj
  have hcardF := (unitary_frattini_section_card Q split J (by omega) hE hf hJ i j hVj ν hphi hcard).2
  have hd : Module.finrank (ZMod 2) (Additive V) ≤ 6*n := by
    have hc := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive V)
    rw [Nat.card_zmod] at hc
    have he : 2 ^ Module.finrank (ZMod 2) (Additive V) = 2^(6*n) := by
      rw [←hc]
      change Nat.card V = _
      rw [hcardF,←pow_mul,Nat.mul_comm n 6]
    exact (Nat.pow_right_injective (by decide : 1 < (2 : ℕ)) he).le
  have hnat := ChapterK.RankOne.UnitaryRecognition.MinimalDegree.isNatural_of_finrank_le
    J σ hn hE hconj hnσ hd
  intro a b hab
  apply hnat.injective J
  exact congrArg ρ hab

/-- Construct the existing actor profile from the genuine cover, its projective
square, and the source radical. No full actor equivalence is supplied. -/
def unitaryActorProfileOfCover
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q split j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a)
    (hphi : (frattini (simpleRemainder Q split j)).map
        (simpleRemainder Q split j).subtype =
      (center (rootAt Q split j (Q.simple i))).map
        (rootAt Q split j (Q.simple i)).subtype)
    (hcard : Nat.card (simpleRemainder Q split j) = (2^n)^7) :
    UnitaryActorProfile Q split j J hVj ν := by
  let a := MulEquiv.ofBijective π ⟨unitary_cover_injective Q split J hn hE hconj hJ
    hm i j hij hVj s ν π hπ hphi hcard,hπ⟩
  refine ⟨a.symm.toMonoidHom,a.symm.surjective,a.symm.injective,?_⟩
  intro r
  have he := hπν (a.symm r)
  change ν (RootLocalCover.projection Q split j (a (a.symm r))) = _ at he
  rw [a.apply_symm_apply] at he
  simpa only [rankOneLocalEquiv_eq_projection,MulEquiv.coe_toMonoidHom] using he

/-- The original characteristic-two hypothesis makes the full actor faithful
on the actual Frattini section, including q = 2 and either orientation. -/
theorem marked_remainderFrattiniAction_injective
    (Q : MarkedQuotient P)
    (e : RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
        (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
      Q.standardAmalgam)
    (h : HypothesisF11 L S) (split : SplitData Q.tits)
    (i : Fin 2) (s : RootReflection Q split i)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    Function.Injective (remainderFrattiniAction Q split i hV) :=
  remainderFrattiniAction_injective Q split i s hV
    (MarkedLocal.parabolic_core_selfCentralizing Q e h i)

/-- The same faithful section action on the literal original SourceQuotient. -/
theorem original_remainderFrattiniAction_injective
    (h : HypothesisF11 L S)
    (Q : SourceQuotient L S) (split : SplitData Q.tits)
    (i : Fin 2) (s : RootReflection Q split i)
    (hV : simpleRemainder Q split i ≤ localKernel Q i) :
    Function.Injective (remainderFrattiniAction Q split i hV) :=
  marked_remainderFrattiniAction_injective Q (originalMarkedIso Q) h split i s hV


variable
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S)
include e h

/-- The original special-or-projective quotient supplies a surjective SU cover
on the perfect-factor branch, with the literal projective square. Both
alternatives are retained; this theorem does not assert injectivity. -/
theorem marked_unitary_cover_of_perfect_factor
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (j : Fin 2) (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (hp : Group.IsPerfect (L j))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J)) :
    ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      ∃ π : J.specialSubgroup →* rankOne Q split j,
        Function.Surjective π ∧
        ∀ a, ν (RootLocalCover.projection Q split j (π a)) = J.specialToProjective a := by
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases hfactor with hs | hpj
  · obtain ⟨f⟩ := hs
    let a := MarkedLocal.specialUnitaryRankOneEquiv Q e h split j hp T hT J hn hE hconj f
    let b := MarkedLocal.specialUnitaryLocalEquiv Q e h split j hp T hT J hn hE hconj f hVj
    refine ⟨b,a.symm.toMonoidHom,a.symm.surjective,?_⟩
    intro x
    rw [MarkedLocal.specialUnitaryLocalEquiv_projection,
      ←MarkedLocal.specialUnitaryRankOneEquiv_apply Q e h split j hp T hT J hn hE hconj f]
    change J.specialToProjective (a (a.symm x)) = _
    rw [a.apply_symm_apply]
  · obtain ⟨f⟩ := hpj
    let a := MarkedLocal.projectiveUnitaryRankOneEquiv Q e h split j hp T hT J hn hE hconj f
    let b := MarkedLocal.projectiveUnitaryLocalEquiv Q e h split j hp T hT J hn hE hconj f hVj
    refine ⟨b,a.symm.toMonoidHom.comp J.specialToProjective,
      a.symm.surjective.comp J.specialToProjective_surjective,?_⟩
    intro x
    rw [MarkedLocal.projectiveUnitaryLocalEquiv_projection,
      ←MarkedLocal.projectiveUnitaryRankOneEquiv_apply Q e h split j hp T hT J hn hE hconj f]
    change a (a.symm (J.specialToProjective x)) = _
    rw [a.apply_symm_apply]

/-- DGS specialness and the actual panel indices give the unitary section's
order and a nontrivial reflection action, including q = 2. -/
theorem marked_unitary_section
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 0 < n)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    Nat.card (frattini (simpleRemainder Q split j)) = 2^n ∧
      Nat.card ((simpleRemainder Q split j) ⧸ frattini (simpleRemainder Q split j)) = (2^n)^6 ∧
      ∃ r, remainderFrattiniAction Q split j hVj r ≠ 1 := by
  have hphi := (marked_unitary_special_radical Q e h split hm i j hij hVi hVj
    hQi hderived hfrattini).2.1
  have hc := (marked_unitary_root_orders Q e h split hm i j hij (2^n)
    (pow_pos (by decide) n) hindexi hindexj).2.2.2.1
  obtain ⟨hp,hcF⟩ := unitary_frattini_section_card Q split J hn hE hfixed hJ
    i j hVj ν hphi hc
  exact ⟨hp,hcF,remainderFrattiniAction_nontrivial_of_cross_center Q split hm i j hij hVj s
    (hphi.le.trans (map_subtype_le _))⟩

/-- For q > 2, construct the full SU3 marking from the original profile and
its generic covering transport. The degree argument discharges injectivity. -/
theorem marked_unitary_profile_of_cover
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
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
    Nonempty (UnitaryActorProfile Q split j J hVj ν) ∧
      (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  have hphi := (marked_unitary_special_radical Q e h split hm i j hij hVi hVj
    hQi hderived hfrattini).2.1
  have hc := (marked_unitary_root_orders Q e h split hm i j hij (2^n)
    (pow_pos (by decide) n) hindexi hindexj).2.2.2.1
  exact ⟨⟨unitaryActorProfileOfCover Q split J hn hE hconj hJ hm i j hij hVj s ν π hπ hπν
      hphi hc⟩,unitary_frattini_irreducible_of_cover Q split J hn hE hconj hJ
        hm i j hij hVj s ν π hπ hphi hc⟩


/-- The original U3-or-SU3 alternative supplies a constructed full actor profile
on the perfect-factor branch for q > 2. -/
theorem marked_unitary_profile_of_perfect_factor
    {E : Type*} [Field E] [Finite E] [CharP E 2]
    (J : HermitianForm 3 E) {n : ℕ} (hn : 2 ≤ n)
    (hE : Nat.card E = (2^n)^2) (hconj : ∀ x, J.conj x = x^(2^n))
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split j)
    (hp : Group.IsPerfect (L j))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
      Nonempty (UnitaryActorProfile Q split j J hVj ν) ∧
      (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  obtain ⟨ν,π,hπ,hπν⟩ := marked_unitary_cover_of_perfect_factor Q split e h
    J (by omega : 0 < n) hE hconj j hVj hp hfactor
  exact ⟨ν,marked_unitary_profile_of_cover Q split e h J hn hE hconj hJ
    hm i j hij hVi hVj s ν π hπ hπν hindexi hindexj hQi hderived hfrattini⟩

/-- Feed the existing (6A)(c) assembly with a profile constructed by the
unitary-section degree argument. The generic covering transport remains
explicit; its injectivity and the unitary section action are proved here. -/
theorem marked_unitary_sixA_of_cover
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i) (t : RootReflection Q split j)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
      ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q split j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
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
    (∃ κ : rankOne Q split j ≃* J.specialSubgroup,
      (∀ r : rankOne Q split j,
        ν (rankOneLocalEquiv Q split j hVj (QuotientGroup.mk r)) =
          J.specialToProjective (κ r)) ∧
      J.specialToProjective.ker = center J.specialSubgroup ∧
      center (rankOne Q split j) =
        (center J.specialSubgroup).comap κ.toMonoidHom) ∧
    (∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ =
        rootAt Q split i (Q.simple j) ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (center (rootAt Q split j (Q.simple i))).map
          (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (frattini (simpleRemainder Q split j)).map
          (simpleRemainder Q split j).subtype) ∧
    (∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      frattini (simpleRemainder Q split i) =
        _root_.commutator (simpleRemainder Q split i) ∧
      (∃ he : IsElementaryAbelian 2
          (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
            Subgroup (X ⧸ Q.D)),
        letI := he
        Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
          Subgroup (X ⧸ Q.D)) = (2^n)^4 ∧
        (elementaryRepresentation (p := 2)
          (remainderDerivedAction Q split i hVi)).IsIrreducible) ∧
      Nat.card (frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q split i) ⧸
        frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split i hVi)).IsIrreducible ∧
      Representation.IsIrreducible
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreActorRepresentation
          Q split i hVi)) ∧
    (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  obtain ⟨⟨d⟩,hi⟩ := marked_unitary_profile_of_cover Q split e h J hn hE hconj hJ
    hm i j hij hVi hVj t ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hZ := HermitianForm.EvenProjectiveComparison.center_eq_bot J
    (by omega : 0 < n) hE hconj
  obtain ⟨ha,hc,hl⟩ := marked_unitary_sixA Q e h split J (by omega) hK hE hfixed hJ
    hm i j hij hVi hVj s f hf hk ν d hZ hindexi hindexj hQi hderived hfrattini
  exact ⟨ha,hc,hl,hi⟩

/-- The actual original special-or-projective perfect factor supplies all
covering data for (6A)(c), without choosing the special alternative as input. -/
theorem marked_unitary_sixA_of_perfect_factor
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q split i ≤ localKernel Q i)
    (hVj : simpleRemainder Q split j ≤ localKernel Q j)
    (s : RootReflection Q split i) (t : RootReflection Q split j)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
      ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (hp : Group.IsPerfect (L j))
    (hfactor : Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* J.specialSubgroup) ∨
      Nonempty (((L j) ⧸ pCore 2 (L j)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    ∃ ν : localGroup Q split j ≃* ProjectiveSpecialUnitaryMatrixGroup J,
    (∃ κ : rankOne Q split j ≃* J.specialSubgroup,
      (∀ r : rankOne Q split j,
        ν (rankOneLocalEquiv Q split j hVj (QuotientGroup.mk r)) =
          J.specialToProjective (κ r)) ∧
      J.specialToProjective.ker = center J.specialSubgroup ∧
      center (rankOne Q split j) =
        (center J.specialSubgroup).comap κ.toMonoidHom) ∧
    (∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      ⁅simpleRoot Q split j,rootAt Q split j (Q.simple i)⁆ =
        rootAt Q split i (Q.simple j) ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (center (rootAt Q split j (Q.simple i))).map
          (rootAt Q split j (Q.simple i)).subtype ∧
      ⁅simpleRoot Q split i,rootAt Q split i (Q.simple j)⁆ =
        (frattini (simpleRemainder Q split j)).map
          (simpleRemainder Q split j).subtype) ∧
    (∃ μ : rankOne Q split i ≃* SL(2,K),
      (∀ r : rankOne Q split i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        MarkedLocal.endpointMap Q e i a.val = r ∧ μ r = f a) ∧
      frattini (simpleRemainder Q split i) =
        _root_.commutator (simpleRemainder Q split i) ∧
      (∃ he : IsElementaryAbelian 2
          (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
            Subgroup (X ⧸ Q.D)),
        letI := he
        Nat.card (⁅simpleRemainder Q split i,simpleRemainder Q split i⁆ :
          Subgroup (X ⧸ Q.D)) = (2^n)^4 ∧
        (elementaryRepresentation (p := 2)
          (remainderDerivedAction Q split i hVi)).IsIrreducible) ∧
      Nat.card (frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q split i) ⧸
        frattini (simpleRemainder Q split i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q split i hVi)).IsIrreducible ∧
      Representation.IsIrreducible
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreActorRepresentation
          Q split i hVi)) ∧
    (elementaryRepresentation (p := 2) (remainderFrattiniAction Q split j hVj)).IsIrreducible := by
  obtain ⟨ν,π,hπ,hπν⟩ := marked_unitary_cover_of_perfect_factor Q split e h
    J (by omega : 0 < n) hE hconj j hVj hp hfactor
  exact ⟨ν,marked_unitary_sixA_of_cover Q split e h J hn hK hE hfixed hJ hconj
    hm i j hij hVi hVj s t f hf hk ν π hπ hπν hindexi hindexj hQi hderived hfrattini⟩

omit Q split e in
/-- The constructed cover profile feeds the original SourceQuotient assembly,
retaining the literal quotient representatives and both original endpoint maps. -/
theorem original_unitary_sixA_of_cover
    (Q₀ : SourceQuotient L S) (split₀ : SplitData Q₀.tits)
    {K E : Type*} [Field K] [Finite K] [CharP K 2]
    [Field E] [Finite E] [CharP E 2]
    (J : BenderSuzuki.MatrixGroups.HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = (2^n)^2)
    (hE : Nat.card E = (2^n)^2)
    (hfixed : Nat.card {x : E // J.conj x = x} = 2^n)
    (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q₀ = 4) (i j : Fin 2) (hij : i ≠ j)
    (hVi : simpleRemainder Q₀ split₀ i ≤ localKernel Q₀ i)
    (hVj : simpleRemainder Q₀ split₀ j ≤ localKernel Q₀ j)
    (s : RootReflection Q₀ split₀ i) (t : RootReflection Q₀ split₀ j)
    (f : (S ⊔ L i).subgroupOf (parabolic L S i) →* SL(2,K))
    (hf : Function.Surjective f)
    (hk : f.ker = (pCore 2 (parabolic L S i)).subgroupOf
      ((S ⊔ L i).subgroupOf (parabolic L S i)))
    (ν : localGroup Q₀ split₀ j ≃*
      BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J)
    (π : J.specialSubgroup →* rankOne Q₀ split₀ j) (hπ : Function.Surjective π)
    (hπν : ∀ a, ν (RootLocalCover.projection Q₀ split₀ j (π a)) = J.specialToProjective a)
    (hindexi : (commonBorel L S).relIndex (parabolic L S i) = (2^n)^2 + 1)
    (hindexj : (commonBorel L S).relIndex (parabolic L S j) = (2^n)^3 + 1)
    (hQi : letI := original_core_normal_in_sylow (L := L) (S := S) i
      IsElementaryAbelian 2 (S ⧸ ((parabolic L S i).pCoreIn 2).subgroupOf S))
    (hderived : _root_.commutator ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2))
    (hfrattini : frattini ((parabolic L S j).pCoreIn 2) =
      center ((parabolic L S j).pCoreIn 2)) :
    (∃ κ : rankOne Q₀ split₀ j ≃* J.specialSubgroup,
      (∀ r : rankOne Q₀ split₀ j,
        ν (rankOneLocalEquiv Q₀ split₀ j hVj (QuotientGroup.mk r)) =
          J.specialToProjective (κ r)) ∧
      J.specialToProjective.ker = center J.specialSubgroup ∧
      center (rankOne Q₀ split₀ j) =
        (center J.specialSubgroup).comap κ.toMonoidHom) ∧
    (∃ μ : rankOne Q₀ split₀ i ≃* SL(2,K),
      (∀ r : rankOne Q₀ split₀ i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q₀.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a) ∧
      ⁅simpleRoot Q₀ split₀ j,rootAt Q₀ split₀ j (Q₀.simple i)⁆ =
        rootAt Q₀ split₀ i (Q₀.simple j) ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (center (rootAt Q₀ split₀ j (Q₀.simple i))).map
          (rootAt Q₀ split₀ j (Q₀.simple i)).subtype ∧
      ⁅simpleRoot Q₀ split₀ i,rootAt Q₀ split₀ i (Q₀.simple j)⁆ =
        (frattini (simpleRemainder Q₀ split₀ j)).map
          (simpleRemainder Q₀ split₀ j).subtype) ∧
    (∃ μ : rankOne Q₀ split₀ i ≃* SL(2,K),
      (∀ r : rankOne Q₀ split₀ i, ∃ a : (S ⊔ L i).subgroupOf (parabolic L S i),
        Q₀.q ⟨a.val,parabolic_le_generated i a.val.property⟩ = r ∧ μ r = f a) ∧
      frattini (simpleRemainder Q₀ split₀ i) =
        _root_.commutator (simpleRemainder Q₀ split₀ i) ∧
      (∃ he : IsElementaryAbelian 2
          (⁅simpleRemainder Q₀ split₀ i,simpleRemainder Q₀ split₀ i⁆ : Subgroup _),
        letI := he
        Nat.card (⁅simpleRemainder Q₀ split₀ i,simpleRemainder Q₀ split₀ i⁆ :
          Subgroup _) = (2^n)^4 ∧
        (elementaryRepresentation (p := 2)
          (remainderDerivedAction Q₀ split₀ i hVi)).IsIrreducible) ∧
      Nat.card (frattini (simpleRemainder Q₀ split₀ i)) = (2^n)^4 ∧
      Nat.card ((simpleRemainder Q₀ split₀ i) ⧸
        frattini (simpleRemainder Q₀ split₀ i)) = (2^n)^4 ∧
      (elementaryRepresentation (p := 2)
        (remainderFrattiniAction Q₀ split₀ i hVi)).IsIrreducible ∧
      Representation.IsIrreducible
        (Theory.AlgebraicGroup.TitsSystem.SourceBinary.UnitarySource.coreActorRepresentation
          Q₀ split₀ i hVi)) ∧
    (elementaryRepresentation (p := 2) (remainderFrattiniAction Q₀ split₀ j hVj)).IsIrreducible := by
  obtain ⟨⟨d⟩,hi⟩ := marked_unitary_profile_of_cover Q₀ split₀ (originalMarkedIso Q₀) h J hn hE hconj hJ
    hm i j hij hVi hVj t ν π hπ hπν hindexi hindexj hQi hderived hfrattini
  have hZ := HermitianForm.EvenProjectiveComparison.center_eq_bot J
    (by omega : 0 < n) hE hconj
  obtain ⟨ha,hc,hl⟩ := original_unitary_sixA h Q₀ split₀ J (by omega) hK hE hfixed hJ
    hm i j hij hVi hVj s f hf hk ν d hZ hindexi hindexj hQi hderived hfrattini
  exact ⟨ha,hc,hl,hi⟩

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.QuadrangleStructure
