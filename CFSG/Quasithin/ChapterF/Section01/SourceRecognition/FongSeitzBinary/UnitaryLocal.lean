module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.UnitaryPanelModel
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.UnitaryLocalIdentification
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.LinearLocal
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Unitary

/-!
# Fong--Seitz (2B) for the original unitary endpoints

Transport the Borel two-actor calculation through an actual Hermitian basis
change, Sylow conjugacy, and the original endpoint factor map. The same
full Borel supplies the required quotient-normalizer containment. Its
already proved panel count identifies the canonical root order with the
original quotient Sylow order. Thus the simple remainder lies in the
full panel kernel for SU3 and PSU3 with q at least four, without original
perfectness. Perfectness itself excludes q = 2 when it is available.

Substitution into the checked local identification removes (2B) from both
the faithful local-group comparison and the original whole-root cover.
The SU3 cover retains its scalars and projects to PSU3 in the local action;
all formulas retain the actual original quotient representatives. The
finite marked quotient, both endpoint squares and full-Borel marking stay
as genuine earlier geometric inputs. Small nonperfect cases and the
seven-row rank-two recognition remain with the final source assembly.
Source: Fong--Seitz I (2B), (5C), pp.7--9,25--26;
Aschbacher--Smith F.1.1--3, pp.259--260.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)]
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)

include e h hT in
/-- Apply the Borel-actor calculation to the SAME original factor and full Borel. -/
theorem remainder_le_kernel_of_factor_borel_two_inner
    (hi : ∀ R : Sylow 2 ((L i) ⧸ pCore 2 (L i)),
      PanelKernel.BorelTwoInner (R : Subgroup _) (normalizer (R : Set ((L i) ⧸ pCore 2 (L i)))))
    (hc : Nat.card (simpleRoot Q split i) = Nat.card (quotientSylow T)) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  let f := factorMap Q e i
  let A := f.range
  let a : L i ≃* A := MonoidHom.ofInjective (factorMap_injective Q e i)
  let c := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let T' := T.mapSurjective (f := a.toMonoidHom) a.surjective
  have hTA : (T' : Subgroup A).map A.subtype = (T : Subgroup (L i)).map f := by
    change ((T : Subgroup (L i)).map a.toMonoidHom).map A.subtype = _
    rw [Subgroup.map_map]
    rfl
  have hTU : (T : Subgroup (L i)).map f ≤ split.U := by
    apply map_le_iff_le_comap.mpr
    rw [factor_unipotent_comap Q e h split i, ← hT]
    intro t ht
    exact mem_map_of_mem (L i).subtype ht
  have hgen : A ⊔ Q.tits.B = Q.tits.standardParabolic {Q.simple i} := by
    have he := congrArg (Subgroup.map (Q.tits.standardParabolic {Q.simple i}).subtype)
      (factorInEndpoint_generates_panel Q e h i)
    rw [Subgroup.map_sup, ← MonoidHom.range_comp,
      map_subgroupOf_eq_of_le (Q.tits.B_le_standardParabolic _),
      ← MonoidHom.range_eq_map, range_subtype] at he
    exact he
  apply PanelKernel.remainder_le_kernel_of_borel_two_inner Q split i A
    (factor_parabolic_normalizes Q e h i) hgen T' (hTA ▸ hTU)
  · change ((normalizer ((quotientSylow T' : Subgroup (A ⧸ pCore 2 A)) :
        Set (A ⧸ pCore 2 A))).comap
        (QuotientGroup.mk' (pCore 2 A))).map A.subtype ≤ Q.tits.B
    rw [quotientSylow_normalizer_comap]
    change (normalizer ((T : Subgroup (L i)).map a.toMonoidHom : Set A)).map A.subtype ≤ _
    rw [← map_equiv_normalizer_eq, Subgroup.map_map]
    change (normalizer (T : Set (L i))).map f ≤ Q.tits.B
    apply map_le_iff_le_comap.mpr
    rw [factor_borel_comap Q e h i, borel_subgroupOf_eq_sylowNormalizer (L i) S T hT]
    exact le_rfl
  · exact PanelKernel.BorelTwoInner.of_equiv c.symm rfl
      (map_equiv_normalizer_eq _ c.symm)
      (hi ((quotientSylow T').mapSurjective (f := c.symm.toMonoidHom) c.symm.surjective))
  · rw [hc]
    change Nat.card ((T : Subgroup (L i)).map (QuotientGroup.mk' (pCore 2 (L i)))) = _
    rw [← relIndex_ker, QuotientGroup.ker_mk',
      ← relIndex_ker, QuotientGroup.ker_mk']
    change (pCore 2 (L i)).relIndex T =
      (pCore 2 A).relIndex ((T : Subgroup (L i)).map a.toMonoidHom)
    rw [← pCore_map_iso 2 a]
    exact (relIndex_map_map_of_injective (f := a.toMonoidHom) _ _ a.injective).symm

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.PanelKernel
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
open HermitianForm HermitianForm.BorelTorus

private instance {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
  Finite.of_surjective J.specialToProjective J.specialToProjective_surjective

private theorem projectiveUnitary_borel_two_inner
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 (ProjectiveSpecialUnitaryMatrixGroup J)) :
    BorelTwoInner (T : Subgroup _) (normalizer (T : Set (ProjectiveSpecialUnitaryMatrixGroup J))) := by
  obtain ⟨C,hC⟩ := Unitary.FormTransport.exists_standard_basis J n (by omega) hc hconj
  let J0 := Unitary.FormTransport.standardForm J
  let e0 := Unitary.FormTransport.projectiveEquiv J C hC
  let T0 := T.mapSurjective (f := e0.toMonoidHom) e0.surjective
  have hf := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hc hconj
  have hJ0 : J0.form = !![0,0,1;0,1,0;1,0,0] := rfl
  let R0 := EvenTwoRank.rootSylow J0 hJ0 (by omega : 0 < n) hc hf
  have hR : BorelTwoInner (R0 : Subgroup _) (normalizer (R0 : Set (ProjectiveSpecialUnitaryMatrixGroup J0))) := by
    change BorelTwoInner (projectiveRoot J0 hJ0) (normalizer (projectiveRoot J0 hJ0 : Set _))
    obtain ⟨_,_,_,_,_,_,hs,hnorm,_⟩ :=
      Unitary.standard_projective_matrix_borel J0 n (by omega) hc hconj rfl
    change BorelTwoInner (BenderSuzuki.External.hermitianUnipotentPSU J0 hJ0).range
      (normalizer ((BenderSuzuki.External.hermitianUnipotentPSU J0 hJ0).range : Set _))
    rw [hnorm,←hs]
    exact projective_borel_two_inner J0 rfl hn hc hconj
  have hT0 := hR.sylow R0 T0
  exact BorelTwoInner.of_equiv e0 rfl (map_equiv_normalizer_eq _ e0) hT0

private theorem specialUnitary_borel_two_inner
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (T : Sylow 2 J.specialSubgroup) :
    BorelTwoInner (T : Subgroup _) (normalizer (T : Set J.specialSubgroup)) := by
  obtain ⟨C,hC⟩ := Unitary.FormTransport.exists_standard_basis J n (by omega) hc hconj
  let J0 := Unitary.FormTransport.standardForm J
  let e0 := Unitary.FormTransport.specialEquiv J C hC
  let T0 := T.mapSurjective (f := e0.toMonoidHom) e0.surjective
  obtain ⟨_,_,R0,hR0,_,_,_,hN,_⟩ := Unitary.standard_su_borel_data J0 n (by omega) hc hconj rfl
  have hR : BorelTwoInner (R0 : Subgroup _) (normalizer (R0 : Set J0.specialSubgroup)) := by
    change BorelTwoInner (R0 : Subgroup _) (normalizer ((R0 : Subgroup J0.specialSubgroup) : Set J0.specialSubgroup))
    rw [hR0,hN]
    exact special_borel_two_inner J0 rfl hn hc hconj
  have hT0 := hR.sylow R0 T0
  exact BorelTwoInner.of_equiv e0 rfl (map_equiv_normalizer_eq _ e0) hT0

variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits) (i : Fin 2)
  [Finite (L i)]
  (T : Sylow 2 (L i)) (hT : (T : Subgroup (L i)).map (L i).subtype = S ⊓ L i)
  {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
  {n : ℕ} (hn : 2 ≤ n) (hc : Nat.card E = (2^n)^2)
  (hconj : ∀ x, J.conj x = x^(2^n))

include e h hT hn hc hconj in
/-- The projective-unitary (2B) branch for q ≥ 4, with no perfectness assumption. -/
theorem projectiveUnitary_remainder_le_kernel
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  apply remainder_le_kernel_of_factor_borel_two_inner Q e h split i T hT
  · intro R
    exact BorelTwoInner.of_equiv μ rfl (map_equiv_normalizer_eq _ μ)
      (projectiveUnitary_borel_two_inner J hn hc hconj
        (R.mapSurjective (f := μ.toMonoidHom) μ.surjective))
  · exact projectiveUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J
      (by omega) hc hconj μ

include e h hT hn hc hconj in
/-- The SU3 scalar cover satisfies the same (2B) containment for q ≥ 4. -/
theorem specialUnitary_remainder_le_kernel
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    simpleRemainder Q split i ≤ localKernel Q i := by
  apply remainder_le_kernel_of_factor_borel_two_inner Q e h split i T hT
  · intro R
    exact BorelTwoInner.of_equiv μ rfl (map_equiv_normalizer_eq _ μ)
      (specialUnitary_borel_two_inner J hn hc hconj
        (R.mapSurjective (f := μ.toMonoidHom) μ.surjective))
  · exact specialUnitary_simpleRoot_card_eq_quotientSylow Q e h split i T hT J
      (by omega) hc hconj μ

section Perfect
variable (hp : Group.IsPerfect (L i)) {m : ℕ} (hm : 0 < m)
  (hcard : Nat.card E = (2^m)^2) (hconjugate : ∀ x, J.conj x = x^(2^m))

include e h hT hp hm hcard hconjugate in
/-- Original perfectness excludes q = 2; no parameter bound is added. -/
theorem projectiveUnitary_remainder_le_kernel_of_perfect
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    simpleRemainder Q split i ≤ localKernel Q i :=
  projectiveUnitary_remainder_le_kernel Q e h split i T hT J
    (projectiveUnitary_parameter_ge_two i hp J hm hcard hconjugate μ) hcard hconjugate μ

include e h hT hp hm hcard hconjugate in
/-- The same perfect-source exclusion with the actual scalar cover retained. -/
theorem specialUnitary_remainder_le_kernel_of_perfect
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    simpleRemainder Q split i ≤ localKernel Q i :=
  specialUnitary_remainder_le_kernel Q e h split i T hT J
    (specialUnitary_parameter_ge_two i hp J hm hcard hconjugate μ) hcard hconjugate μ

/-- The original projective quotient supplies the faithful projective local group. -/
def regularProjectiveUnitaryLocalEquiv
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  projectiveUnitaryLocalEquiv Q e h split i hp T hT J hm hcard hconjugate μ
    (projectiveUnitary_remainder_le_kernel_of_perfect Q e h split i T hT J hp hm hcard hconjugate μ)

@[simp] theorem regularProjectiveUnitaryLocalEquiv_projection
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) (r : rankOne Q split i) :
    regularProjectiveUnitaryLocalEquiv Q e h split i T hT J hp hm hcard hconjugate μ
      (RootLocalCover.projection Q split i r) =
      μ (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp r)) :=
  projectiveUnitaryLocalEquiv_projection Q e h split i hp T hT J hm hcard hconjugate μ _ r

/-- The full original root cover, with its (2B) premise discharged. -/
def regularOriginalProjectiveUnitaryCoverEquiv
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  originalProjectiveUnitaryCoverEquiv Q e h split i hp T hT J hm hcard hconjugate μ
    (projectiveUnitary_remainder_le_kernel_of_perfect Q e h split i T hT J hp hm hcard hconjugate μ)

@[simp] theorem regularOriginalProjectiveUnitaryCoverEquiv_mk
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J) (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    regularOriginalProjectiveUnitaryCoverEquiv Q e h split i T hT J hp hm hcard hconjugate μ
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      μ (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r))) :=
  originalProjectiveUnitaryCoverEquiv_mk Q e h split i hp T hT J hm hcard hconjugate μ _ r

/-- The original special quotient supplies the faithful projective local group. -/
def regularSpecialUnitaryLocalEquiv
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    localGroup Q split i ≃* ProjectiveSpecialUnitaryMatrixGroup J :=
  specialUnitaryLocalEquiv Q e h split i hp T hT J hm hcard hconjugate μ
    (specialUnitary_remainder_le_kernel_of_perfect Q e h split i T hT J hp hm hcard hconjugate μ)

@[simp] theorem regularSpecialUnitaryLocalEquiv_projection
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) (r : rankOne Q split i) :
    regularSpecialUnitaryLocalEquiv Q e h split i T hT J hp hm hcard hconjugate μ
      (RootLocalCover.projection Q split i r) =
      J.specialToProjective (μ (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp r))) :=
  specialUnitaryLocalEquiv_projection Q e h split i hp T hT J hm hcard hconjugate μ _ r

/-- The full original root cover, with its (2B) premise discharged. -/
def regularOriginalSpecialUnitaryCoverEquiv
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) :
    letI := originalRadicalInClosure_normal Q e h split i
    (originalLocalClosure Q e split i ⧸ originalRadicalInClosure Q e split i) ≃* J.specialSubgroup :=
  originalSpecialUnitaryCoverEquiv Q e h split i hp T hT J hm hcard hconjugate μ
    (specialUnitary_remainder_le_kernel_of_perfect Q e h split i T hT J hp hm hcard hconjugate μ)

@[simp] theorem regularOriginalSpecialUnitaryCoverEquiv_mk
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) (r : originalRankOne Q e split i) :
    letI := originalRadicalInClosure_normal Q e h split i
    regularOriginalSpecialUnitaryCoverEquiv Q e h split i T hT J hp hm hcard hconjugate μ
      (QuotientGroup.mk' (originalRadicalInClosure Q e split i)
        (inclusion (originalRankOne_le_localClosure Q e split i) r)) =
      μ (QuotientGroup.mk' (pCore 2 (L i))
        (rankOneLift Q e h split i hp (originalRankOneEquiv Q e split i r))) :=
  originalSpecialUnitaryCoverEquiv_mk Q e h split i hp T hT J hm hcard hconjugate μ _ r

end Perfect

end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
