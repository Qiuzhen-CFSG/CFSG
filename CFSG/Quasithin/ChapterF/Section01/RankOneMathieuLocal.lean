module
public import CFSG.Quasithin.ChapterF.Section01.RankOneMathieuSections
public import CFSG.Quasithin.ChapterF.Section01.RankOneBinaryLinear
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.MathieuNestedQuotients
public import CFSG.Quasithin.MainConverse.MathieuLocal.M22Even
public import CFSG.Quasithin.MainConverse.MathieuLocal.M23Even
public import Theory.SpecificGroups.PSL2.BinaryAutomorphismOrder
public import Theory.Mathieu.M22.Properties.TwoLocalSeven
public import Theory.Mathieu.M23.QuasithinGeometry.SylowTwoLocals.PointParabolic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.EvenCharacteristic
public import CFSG.Quasithin.MainConverse.MathieuLocal.M24Even
public import Theory.GroupTheory.SylowNormalIntersectionIndex

/-!
# Full-Sylow rank-one local components in the larger Mathieu groups

A local component with PSL₂(8) two-core quotient has nontrivial two-core:
otherwise even characteristic makes the full Sylow act faithfully on PSL₂(8),
whose automorphism order is not divisible by sixteen. Its characteristic
kernel then supplies a common two-local overgroup of the component and Sylow.

Native M22 two-locals containing a full Sylow are seven-free. In M23, the
component–Sylow join would have order8064, excluded by the native heptad and
triple geometry. In M24, the octad, trio and sextet quotients permit only a
quotient of order at most168 or PSL₄(2), both incompatible with PSL₂(8).
The common-order reduction therefore leaves only PSL₂(4) for any genuine
source rank-one quotient in the three models.

The original smaller changed-Sylow consumer is
Chapter6/SourceReduction/RankOneModuleGenericExceptionalCartanGlobalPrimeSylowMathieu.
Source: Aschbacher–Smith A.3.12 and5.2.2, pp.47–48 and648–649
(`refs/quasithin.pdf`), and GLS3 Tables5.3c–e for the native Mathieu geometry.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterF.Source.MathieuLocal
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G]

private theorem eight_card {X : Type*} [Group X]
    (h : ClassicalGroup.IsPSL X 2 8) : Nat.card X = 504 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := h
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 3) (by
    simpa only [Nat.card_eq_fintype_card, show (2:ℕ)^3 = 8 from rfl] using hF)
  have hc := BenderSuzuki.External.huppert614_card_psl_mul_center (K := F)
  rw [BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (CharTwo.neg_eq 1),mul_one,hF] at hc
  exact (Nat.card_congr e.toEquiv).trans hc

private theorem eight_core_ne_bot (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 8)
    (hE : IsEvenCharacteristicAt S) (h16 : 16 ∣ Nat.card S) : pCore 2 B ≠ ⊥ := by
  intro hc
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (f := 3) (by
    simpa only [Nat.card_eq_fintype_card, show (2:ℕ)^3 = 8 from rfl] using hF)
  let a : B ≃* PSL(2,F) :=
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).symm.trans e
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup B := a.isSimpleGroup
  let := hl.perfect
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hz : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp ht))
  let : IsQuasisimple B :=
    ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩
  have hf := sylow_centralizer_eq_bot_of_evenCharacteristic S hE hl hn
  let f := B.normalizerMonoidHom.comp (inclusion hn)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    apply Subtype.ext
    apply mem_bot.mp
    rw [← hf]
    refine ⟨x.property,?_⟩
    change inclusion hn x ∈ B.normalizerMonoidHom.ker at hx
    rw [normalizerMonoidHom_ker] at hx
    exact hx
  have haut : Nat.card (MulAut B) ∣ 1512 := by
    rw [Nat.card_congr (MulAut.congr a).toEquiv]
    exact Theory.PSL2.BinaryAutomorphismOrder.aut_card_dvd (n := 3) hF
  have hh := h16.trans ((card_dvd_of_injective f hinj).trans haut)
  norm_num at hh

/-- The native M22 full-Sylow local geometry excludes a PSL2(8) core quotient. -/
theorem not_eight_m22 (S : Sylow 2 M22) (B : Subgroup M22)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup M22) ≤ normalizer (B : Set M22)) :
    ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 8 := by
  intro hm
  have h16 : 16 ∣ Nat.card S := by
    rw [S.card_eq_multiplicity,m22_order]; decide +kernel
  have hc := eight_core_ne_bot S B hl hn hm (MainConverse.m22_evenCharacteristic S) h16
  let U := B.pCoreIn 2
  have hU : U ≠ ⊥ := fun he => hc ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  have hB : B ≤ normalizer (U : Set M22) := B.le_normalizer.trans hnorm
  have h7 : 7 ∣ Nat.card B := (by rw [eight_card hm]; decide : 7 ∣ Nat.card (B ⧸ pCore 2 B)).trans
    (card_quotient_dvd_card _)
  exact M22TwoLocalOrders.not_seven_dvd_card_twoLocal S _
    ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩ (hn.trans hnorm) (h7.trans (card_dvd_of_le hB))

private theorem join_card (S : Sylow 2 G) (B : Subgroup G)
    (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hm : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 8) :
    Nat.card (B ⊔ (S : Subgroup G) : Subgroup G) = Nat.card S * 63 := by
  let J := B ⊔ (S : Subgroup G)
  let B' := B.subgroupOf J
  let S' := S.subtype (show (S : Subgroup G) ≤ J from le_sup_right)
  let : B'.Normal := (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le B.le_normalizer hn)
  obtain ⟨Q,hQ⟩ := S'.exists_subgroupOf_eq_of_normal B'
  let e := subgroupOfEquivOfLe (show B ≤ J from le_sup_left)
  let q := QuotientGroup.mk' (pCore 2 B')
  let P := Q.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 B'))
  have hq : Nat.card (B' ⧸ pCore 2 B') = 504 :=
    (Nat.card_congr (QuotientGroup.congr _ _ e (pCore_map_iso 2 e)).toEquiv).trans (eight_card hm)
  have hindex : Q.index = 63 := by
    have hi := Q.index_map_of_two_kernel q (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup)
    have hh := (P : Subgroup (B' ⧸ pCore 2 B')).index_mul_card
    rw [P.card_eq_multiplicity,hq,hi,show Nat.factorization 504 2 = 3 from by decide +kernel] at hh
    norm_num at hh
    omega
  have he := normal_intersection_relIndex (S' : Subgroup J) (⊤ : Subgroup J) B' le_top (by
    change ⊤ ≤ B.subgroupOf J ⊔ (S : Subgroup G).subgroupOf J
    rw [←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self])
  rw [top_subgroupOf,relIndex_top_right,←hQ,relIndex_top_right,hindex] at he
  have hh := (S' : Subgroup J).card_mul_index
  have hSc : Nat.card S' = Nat.card S :=
    Nat.card_congr (subgroupOfEquivOfLe (show (S : Subgroup G) ≤ J from le_sup_right)).toEquiv
  rw [←he,hSc] at hh
  exact hh.symm

/-- The native M23 index-63 obstruction excludes a PSL2(8) local core quotient. -/
theorem not_eight_m23 (S : Sylow 2 M23) (B : Subgroup M23)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup M23) ≤ normalizer (B : Set M23)) :
    ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 8 := by
  intro hm
  have hSc : Nat.card S = 128 := by
    rw [S.card_eq_multiplicity,m23_order]; decide +kernel
  have hc := eight_core_ne_bot S B hl hn hm (MainConverse.m23_evenCharacteristic S)
    (by rw [hSc]; decide)
  let U := B.pCoreIn 2
  have hU : U ≠ ⊥ := fun he => hc ((map_eq_bot_iff_of_injective _ B.subtype_injective).mp he)
  have hnorm := normalizer_le_normalizer_characteristic_image B (pCore 2 B)
  have hJ : B ⊔ (S : Subgroup M23) ≤ normalizer (U : Set M23) :=
    sup_le (B.le_normalizer.trans hnorm) (hn.trans hnorm)
  apply M23Geometry.SylowTwoLocals.no_card_8064_in_twoLocal S _ _
    ⟨U,hU,pCore_isPGroup.map B.subtype,rfl⟩ (hn.trans hnorm) hJ
  rw [join_card S B hn hm,hSc]

/-- The native M24 local catalogue excludes a PSL2(8) local core quotient. -/
theorem not_eight_m24 (S : Sylow 2 M24) (B : Subgroup M24)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup M24) ≤ normalizer (B : Set M24)) :
    ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 8 := by
  intro hm
  have h16 : 16 ∣ Nat.card S := by
    rw [S.card_eq_multiplicity,m24_order]; decide +kernel
  have hc := eight_core_ne_bot S B hl hn hm (MainConverse.m24_evenCharacteristic S) h16
  rcases MathieuNested.local_models_of_core_ne_bot (MulEquiv.refl _) S B hl hn hc
    (by rw [eight_card hm]; decide) with hsmall | hfour
  · rw [eight_card hm] at hsmall
    omega
  · have hmodel : IsRankOneModel (B ⧸ pCore 2 B) := .linear 3 (by decide) hm
    obtain ⟨F,_,_,hF,⟨a⟩⟩ := hfour
    let := Fintype.ofFinite F
    let f : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
      simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hF)
    exact hmodel.not_binary_linear (by decide : 3 ≤ 4)
      ((a.trans (Atlas.fieldEquivPSL 4 f)).trans
        (BinaryLinear.OuterCyclic.projectiveEquivLinear (by decide)))

private theorem not_eight_transport {X : Type*} [Group X] [Finite X]
    (e : G ≃* X) (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hex : ∀ (P : Sylow 2 X) (C : Subgroup X), C ∈ localCComponents P →
      (P : Subgroup X) ≤ normalizer (C : Set X) →
      ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 8) :
    ¬ ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 8 := by
  intro hm
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot e.injective]; infer_instance
  let b := e.subgroupMap B
  let q := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact hex (S.mapSurjective e.surjective) (B.map e.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hl e.toMonoidHom)
    ((map_mono hn).trans (le_normalizer_map e.toMonoidHom))
    (hm.of_mulEquiv q.symm)

/-- In all three larger Mathieu models, a full-Sylow-normalized source
rank-one local component has its actual two-core quotient isomorphic to PSL2(4). -/
theorem rankOne_quotient_four (S : Sylow 2 G) (B : Subgroup G)
    (hl : B ∈ localCComponents S) (hn : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hm : IsRankOneModel (B ⧸ pCore 2 B))
    (he : Nonempty (G ≃* M22) ∨ Nonempty (G ≃* M23) ∨ Nonempty (G ≃* M24)) :
    ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 2 4 := by
  have hd : Nat.card G ∣ 244823040 := by
    rcases he with he | he | he
    all_goals obtain ⟨e⟩ := he
    · rw [Nat.card_congr e.toEquiv,m22_order]; decide
    · rw [Nat.card_congr e.toEquiv,m23_order]; decide
    · rw [Nat.card_congr e.toEquiv,m24_order]
  have hns : ¬ Group.IsSolvable (B ⧸ pCore 2 B) := by
    intro hs
    let := hs
    let : Group.IsNilpotent (pCore 2 B) := pCore_isNilpotent
    let : Group.IsSolvable B := Group.isSolvable_of_ker_le_range (pCore 2 B).subtype
      (QuotientGroup.mk' (pCore 2 B)) (by simp)
    exact hl.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).injective)
  apply (hm.mathieu_section hns ((card_quotient_dvd_card _).trans
    (B.card_subgroup_dvd_card.trans hd))).resolve_right
  rcases he with he | he | he
  all_goals obtain ⟨e⟩ := he
  · exact not_eight_transport e S B hl hn not_eight_m22
  · exact not_eight_transport e S B hl hn not_eight_m23
  · exact not_eight_transport e S B hl hn not_eight_m24

end CFSG.Quasithin.ChapterF.Source.MathieuLocal
