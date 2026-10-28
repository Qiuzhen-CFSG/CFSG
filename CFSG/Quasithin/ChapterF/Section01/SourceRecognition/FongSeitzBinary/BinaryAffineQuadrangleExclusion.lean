module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.QuadrangleStructure.AffineExclusion
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.AffineLocalCover
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.BinaryAffineHexagonExclusion
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.QuadrangleStructure.UnitaryFactorOrders
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.FongSeitzBinary.OriginalActorQuotient

/-!
# Quadrangle regularity for the complete original local catalogue

The binary unitary exception has a faithful root image because the full
order-144 panel group has no nontrivial odd central stem cover. The
quadrangle estimates then exclude the affine panel against every F.1.1
opposite factor: the linear field is at most four, nonbinary Suzuki and
unitary factors contradict their two-layer degree bounds, and every
remaining root has order at most eight. This includes D10, Sz(2), PSU3(2)
and SU3(2), without any perfectness assumption.

Consequently both canonical remainders lie in their actual panel kernels.
The full original amalgam marking identifies their preimages with the
original parabolic two-cores. The marked quotient, split data and source
rotation four remain the earlier source inputs. The unitary profile
consumer uses these containments to remove its last binary regularity
premise while retaining the full scalar/projective square.

Source: Fong--Seitz I (4A),(4B),(4D),(4F),(5I), pp.19--24,31--35;
AS F.1.1--3; DGS (11.8), pp.175--176.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.HexagonStructure
open Theory.AlgebraicGroup.TitsSystem.SourceBinary.QuadrangleStructure
namespace CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G} {P : Fin 2 → Subgroup X}
  (Q : MarkedQuotient P)
  (e : RankTwoAmalgam.Iso
    (RankTwoAmalgam.ofSubgroups (parabolic L S 0)
      (parabolic L S 0 ⊓ parabolic L S 1) (parabolic L S 1) inf_le_left inf_le_right)
    Q.standardAmalgam)
  (h : HypothesisF11 L S) (split : SplitData Q.tits)

include e h in
theorem binary_affine_quadrangle_false_of_linear_quotient
    {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (μ : ((L i) ⧸ pCore 2 (L i)) ≃* PSL(2,F))
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV := linear_remainder_le_kernel Q e h split i T hT μ
  obtain ⟨f,hf,hk,_⟩ := linear_actor_quotient_of_factor Q e h split i μ
  let : ((S ⊔ L i).subgroupOf (parabolic L S i)).Normal :=
    QuadrangleStructure.marked_sylow_factor_normal Q e h split i
  obtain ⟨ν,_⟩ := QuadrangleStructure.marked_linear_rankOne Q e h split i
    (UnitarySource.actorReflection Q split i) hV _ (subgroupOf_mono _ le_sup_left) f hf hk
  have hsmall := affine_quadrangle_linear_field_le_four Q split hm i j hij hV ν hx.1 hx.2.1 hx.2.2.1
  exact no_affine_quadrangle_of_small_opposite_of_faithful Q split hm i j hij
    (parabolic_core_selfCentralizing Q e h j)
    (by rw [simpleRoot_card_linear Q e h split i T hT μ]; omega)
    hx.1 hx.2.1 hx.2.2.1 (affine_root_image_injective Q split j hx.1 hx.2.1 hx.2.2.1)

include e h in
theorem binary_affine_quadrangle_false_of_unitary
    {E : Type*} [Field E] [Finite E] (J : HermitianForm 3 E)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card E = (2^n)^2)
    (hconj : ∀ x, J.conj x = x^(2^n))
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hfactor : Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* J.specialSubgroup) ∨
      Nonempty (((L i) ⧸ pCore 2 (L i)) ≃* ProjectiveSpecialUnitaryMatrixGroup J))
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hV : simpleRemainder Q split i ≤ localKernel Q i := by
    rcases hfactor with hs | hp
    · exact specialUnitary_remainder_le_kernel Q e h split i T hT J hn hcard hconj hs.some
    · exact projectiveUnitary_remainder_le_kernel Q e h split i T hT J hn hcard hconj hp.some
  obtain ⟨ν,π,hπ,_⟩ := regular_unitary_cover_of_factor Q e h split J (by omega) hcard hconj i hV hfactor
  have hr : Nat.card (simpleRoot Q split i) = (2^n)^3 := by
    rcases hfactor with hs | hp
    · exact specialUnitary_simpleRoot_card Q e h split i T hT J (by omega) hcard hconj hs.some
    · exact projectiveUnitary_simpleRoot_card Q e h split i T hT J (by omega) hcard hconj hp.some
  exact no_affine_quadrangle_of_unitary Q split hm i j hij hV J hn hcard hconj π hπ hr
    hx.1 hx.2.1 hx.2.2.1

include e h in
theorem binary_affine_quadrangle_false
    (hm : rotationOrder Q = 4) (i j : Fin 2) (hij : i ≠ j)
    (hx : BinaryUnitaryException Q split j) : False := by
  let := h.finite_local i
  obtain ⟨T,hT⟩ := h.sylow i
  have hsmall (hc : Nat.card (simpleRoot Q split i) ≤ 8) : False :=
    no_affine_quadrangle_of_small_opposite_of_faithful Q split hm i j hij
      (parabolic_core_selfCentralizing Q e h j) hc hx.1 hx.2.1 hx.2.2.1 (affine_root_image_injective Q split j hx.1 hx.2.1 hx.2.2.1)
  cases h.quotient i with
  | linear n hn hmodel =>
    obtain ⟨F,hF,hfin,hcard,⟨μ⟩⟩ := hmodel
    let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using hcard)
    exact binary_affine_quadrangle_false_of_linear_quotient Q e h split hm i j hij μ hx
  | suzuki m hmodel =>
    by_cases hm0 : 0 < m
    · exact no_affine_quadrangle_of_suzuki Q split hm i j hij
        (suzuki_remainder_le_kernel_all Q e h split i T hT hmodel.some) hm0
        (suzukiAllRankOneEquiv Q e h split i T hT hmodel.some)
        (suzuki_simpleRoot_card Q e h split i T hT hmodel.some) hx.1 hx.2.1 hx.2.2.1
    · have he : m = 0 := by omega
      subst m
      apply hsmall
      rw [suzuki_simpleRoot_card Q e h split i T hT hmodel.some]
      decide
  | projective_unitary n hn hmodel =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hmodel
    by_cases hn2 : 2 ≤ n
    · exact binary_affine_quadrangle_false_of_unitary Q e h split J hn2 hcard hconj hm i j hij
        (Or.inr ⟨μ⟩) hx
    · have he : n = 1 := by omega
      subst n
      apply hsmall
      rw [projectiveUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ]
      decide
  | special_unitary n hn hmodel =>
    obtain ⟨F,hF,hfin,J,hcard,hconj,⟨μ⟩⟩ := hmodel
    by_cases hn2 : 2 ≤ n
    · exact binary_affine_quadrangle_false_of_unitary Q e h split J hn2 hcard hconj hm i j hij
        (Or.inl ⟨μ⟩) hx
    · have he : n = 1 := by omega
      subst n
      apply hsmall
      rw [specialUnitary_simpleRoot_card Q e h split i T hT J hn hcard hconj μ]
      decide
  | dihedral hmodel =>
    apply hsmall
    rw [dihedral_simpleRoot_card Q e h split i T hT hmodel.some]
    decide

include e h in
theorem marked_quadrangle_regularity (hm : rotationOrder Q = 4) :
    ∀ j : Fin 2, simpleRemainder Q split j ≤ localKernel Q j ∧
      (simpleRemainder Q split j).comap (endpointMap Q e j) = pCore 2 (parabolic L S j) := by
  intro j
  let := h.finite_local j
  obtain ⟨T,hT⟩ := h.sylow j
  rcases remainder_le_kernel_or_binary_unitary_exception Q e h split j T hT with hr | hx
  · exact hr
  · exact (binary_affine_quadrangle_false Q e h split hm (1-j) j
      (by fin_cases j <;> decide) hx).elim
end CFSG.Quasithin.ChapterF.Source.FongSeitzBinary.MarkedLocal
