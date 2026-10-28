module
public import CFSG.Quasithin.ChapterI.Section03.MathieuFixedLieModels
public import Theory.SpecificGroups.PSL4.FermatSeven
public import Theory.SpecificGroups.SU3.SylowFixedInvolutions
public import Theory.SpecificGroups.SU3.EvenProjectiveComparison
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.UnitaryGeometry.TwoPointRoots.ProjectiveTori

public import Theory.SpecificGroups.PSL3Even.FixedComponents
public import Theory.SpecificGroups.SU3.Quasisimplicity
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Tits.FiniteSimple

/-!
# Further involution-fixed Mathieu exclusions

A component covering M₂₂ forces a factor seven in the ambient order, excluding
Fermat-field PSL₄. In binary PSU₃, inner fixed groups lie in solvable Sylow
normalizers; outer fixed groups are the actual fixed-field SL₂. Their cyclic
Sylow three-subgroups cannot map onto M₂₂'s rank-two Sylow three-subgroups.

For binary PSL₃, the complete involution rows give a smaller PSL₃ component,
an SL₂ embedding, or a smaller PSU₃ component. The first contradicts the
order of M₂₂; the second uses the same cyclic Sylow argument; the third
contradicts the unitary two-rank and root-group order. The small derived
symplectic and G₂ models and the Tits presentation are excluded by order.
No arbitrary central quotient is assumed to preserve prime rank.

The remaining catalogue is applied to the unchanged exterior cubic in
Hall.OddNormalizer.PushingUpRemainingProperModels and to the literal Hall
counterexample in Hall.OddNormalizer. Source: Aschbacher--Smith 4.2.13,
printed p.612, Theorem B, p.33, and the model references in the imports.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterI.MathieuPumpup
open Sporadic.Mathieu

private theorem no_mathieu_quotient_binary_sl2 {F B : Type*} [Field F] [Finite F]
    [CharP F 2] [Group B] [Finite B]
    (j : B →* Matrix.SpecialLinearGroup (Fin 2) F) (hj : Function.Injective j)
    (f : B →* M22) (hf : Function.Surjective f) : False := by
  let P : Sylow 3 B := Sylow.nonempty.some
  let : IsCyclic P := Matrix.SL2.odd_pGroup_isCyclic_of_injective P.isPGroup' (by decide)
    (j.comp (P : Subgroup B).subtype) (hj.comp (P : Subgroup B).subtype_injective)
  let Q := P.mapSurjective hf
  let : IsCyclic Q := isCyclic_of_surjective (f.subgroupMap (P : Subgroup B))
    (f.subgroupMap_surjective _)
  have hr := Q.primeRank_le_one_of_isCyclic inferInstance
  rw [m22_primeRank_three] at hr
  omega

variable {S : Type*} [Group S]

theorem HasMathieuFixedComponent.not_fermat_linear_four (h : HasMathieuFixedComponent S)
    {p : ℕ} (hp : ∃ k : ℕ, p = 2 ^ (2 ^ k) + 1)
    (hm : ClassicalGroup.IsPSL S 4 p) : False := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  exact Theory.SpecificGroups.PSL4.fermat_seven_not_dvd hp hF
    ((by decide : 7 ∣ 443520).trans (h.of_mulEquiv e).card_dvd)

theorem HasMathieuFixedComponent.not_binary_unitary_three
    [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) {n : ℕ} (hn : 2 ≤ n)
    (hm : ClassicalGroup.IsPSU S 3 (2 ^ n)) : False := by
  classical
  obtain ⟨F,_,_,J,hF,hconj,⟨e⟩⟩ := hm
  have hfixed := FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n (by omega) hF hconj
  open HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport in
  obtain ⟨d⟩ := exists_projectiveEquiv J (2 ^ n) hF hfixed
  let J' := HermitianForm.OddPrimeSylow.NormalizedOuter.FormTransport.standardForm J
  let S' := ProjectiveSpecialUnitaryMatrixGroup J'
  let e' : S ≃* S' := e.trans d
  let : Finite S' := Finite.of_surjective J'.specialToProjective J'.specialToProjective_surjective
  let : IsSimpleGroup S' := e'.symm.isSimpleGroup
  let : Group.IsPerfect S' := Group.IsPerfect.ofSurjective (f := e'.toMonoidHom) e'.surjective
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e'
  let : IsQuasisimple B := hB.quasisimple
  let f := b.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hf : Function.Surjective f := b.surjective.comp (QuotientGroup.mk'_surjective _)
  let : Nontrivial B := (nontrivial_iff_ne_bot B).mpr hB.ne_bot
  by_cases hi : ∃ t : S', a = MulAut.conj t
  · obtain ⟨t,rfl⟩ := hi
    have ht : orderOf t = 2 :=
      (MulAut.conj_orderOf_of_center_eq_bot (center_eq_bot_of_simple_perfect (G := S')) t).symm.trans ha
    have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,ht]; rfl)
    obtain ⟨P,hP⟩ := hp.exists_le_sylow
    have htn : t ≠ 1 := by intro hh; simp [hh] at ht
    have hc := HermitianForm.SylowFixedInvolutions.projective_centralizer_le_normalizer
      J' hn rfl hF hfixed P t (hP (mem_zpowers t)) htn
    let : Group.IsSolvable (normalizer (P : Set S')) :=
      (BenderSuzuki.ZD.RankOneModelGeometry.unitary_projective_borel
        J' hn hF hfixed rfl P).1
    have hle : B ≤ normalizer (P : Set S') := hB.1.trans (by
      rw [MulAut.fixedSubgroup_conj]; exact hc)
    let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
      (f := inclusion hle) (inclusion_injective hle)
    exact Group.IsPerfect.not_isSolvable B inferInstance
  · let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 2) (by
      simpa [Nat.card_eq_fintype_card,pow_mul] using hF)
    obtain ⟨c,hc⟩ := J'.outer_involution_conjugate n hn rfl hF hfixed
      (J'.projectiveGraphAut_isEntrywiseConjugation rfl) a
      (ha ▸ pow_orderOf_eq_one a) hi
    let ef : a.fixedSubgroup ≃* Matrix.SpecialLinearGroup (Fin 2)
        (FixedBy.subfield F J'.conj) :=
      ((MulEquiv.subgroupCongr (congrArg MulAut.fixedSubgroup hc.symm)).trans
        (MulAut.fixedSubgroupCongr c (J'.projectiveGraphAut rfl)).symm).trans
        ((J'.projectiveGraphFixedEquivSpecial rfl).trans (J'.specialGraphFixedEquivSL2 rfl))
    exact no_mathieu_quotient_binary_sl2
      (ef.toMonoidHom.comp (inclusion hB.1)) (ef.injective.comp (inclusion_injective hB.1)) f hf


private theorem component_equiv_twoResidual {H : Type*} [Group H] [Finite H]
    [IsSimpleGroup (pResidual 2 H)] (D : Subgroup H) (hD : IsComponent H D) :
    Nonempty (D ≃* pResidual 2 H) := by
  let := hD.2
  let : Group.IsNilpotent (H ⧸ pResidual 2 H) :=
    (Subgroup.isPGroup_quotient_pResidual (G := H) 2).isNilpotent
  have hle : D ≤ pResidual 2 H := (le_solvableResidual_of_isPerfect D).trans
    (solvableResidual_le_of_solvable_quotient (pResidual 2 H))
  let e := subgroupOfEquivOfLe hle
  let : IsSimpleGroup (D ⧸ center D) := IsQuasisimple.simple
  let : Nontrivial D := (QuotientGroup.mk'_surjective (center D)).nontrivial
  let : Nontrivial (D.subgroupOf (pResidual 2 H)) := e.nontrivial
  have ht : D.subgroupOf (pResidual 2 H) = ⊤ := by
    rcases hD.1.subgroupOf.eq_bot_or_top_of_isSimpleGroup
      (inferInstance : IsSimpleGroup (pResidual 2 H)) with hb | ht
    · exact ((nontrivial_iff_ne_bot _).mp inferInstance hb).elim
    · exact ht
  exact ⟨e.symm.trans ((MulEquiv.subgroupCongr ht).trans topEquiv)⟩

private def centerlessMathieuEquiv {B : Type*} [Group B] [IsSimpleGroup B]
    [Group.IsPerfect B] (b : (B ⧸ center B) ≃* M22) : B ≃* M22 :=
  ((QuotientGroup.quotientMulEquivOfEq
    (center_eq_bot_of_simple_perfect (G := B))).trans QuotientGroup.quotientBot).symm.trans b

/-- The field, graph and graph-field rows of a binary linear-three involution
exclude a fixed component covering M₂₂, with the original central quotient. -/
theorem HasMathieuFixedComponent.not_binary_linear_three (h : HasMathieuFixedComponent S)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL S 3 (2 ^ n)) : False := by
  classical
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  obtain ⟨a,ha,B,hB,⟨b⟩⟩ := h.of_mulEquiv e
  let D := B.subgroupOf a.fixedSubgroup
  have hD : IsComponent a.fixedSubgroup D := hB.2
  let := hD.2
  let db : D ≃* B := subgroupOfEquivOfLe hB.1
  let f : D →* M22 := (b.toMonoidHom.comp (QuotientGroup.mk' (center B))).comp db.toMonoidHom
  have hf : Function.Surjective f := b.surjective.comp
    ((QuotientGroup.mk'_surjective _).comp db.surjective)
  have hle : D ≤ pResidual 2 a.fixedSubgroup := by
    let : Group.IsNilpotent (a.fixedSubgroup ⧸ pResidual 2 a.fixedSubgroup) :=
      (Subgroup.isPGroup_quotient_pResidual (G := a.fixedSubgroup) 2).isNilpotent
    exact (le_solvableResidual_of_isPerfect D).trans
      (solvableResidual_le_of_solvable_quotient (pResidual 2 a.fixedSubgroup))
  rcases Matrix.PSL3Even.InvolutionResidualRows.fixed_component_rows (by omega) hF a ha
    with hs | hfield | hgraph | hunitary
  · let := hs
    exact hD.isCComponent.not_isSolvable inferInstance
  · obtain ⟨_,σ,_,_,_,_,m,hm,_,hK,⟨er⟩⟩ := hfield
    let K := FixedBy.subfield F σ
    let : Group.IsPerfect PSL(3,K) := Atlas.psl_perfect 3 (by decide)
    let eR : pResidual 2 a.fixedSubgroup ≃* PSL(3,K) :=
      er.trans ((MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top).trans topEquiv)
    let : IsSimpleGroup PSL(3,K) := Atlas.psl_simple_high_rank 3 (by decide)
    let : IsSimpleGroup (pResidual 2 a.fixedSubgroup) := eR.isSimpleGroup
    obtain ⟨ed⟩ := component_equiv_twoResidual D hD
    let eD := ed.trans eR
    let : IsSimpleGroup B := (db.symm.trans eD).isSimpleGroup
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := db.toMonoidHom) db.surjective
    let em : PSL(3,K) ≃* M22 := eD.symm.trans (db.trans (centerlessMathieuEquiv b))
    have hc : Nat.card PSL(3,K) = 443520 := (Nat.card_congr em.toEquiv).trans m22_order
    have he := Matrix.PSL3.LinearThree.card_projective_mul_scalar K
    rw [hc,hK] at he
    by_cases hsmall : m ≤ 2
    · interval_cases m <;> norm_num at he
    · have hq : 8 ≤ 2 ^ m := show 2 ^ 3 ≤ 2 ^ m from
        Nat.pow_le_pow_right (by decide) (by omega)
      have hg : Nat.gcd 3 (2 ^ m - 1) ≤ 3 := Nat.gcd_le_left (2 ^ m - 1) (by decide : 0 < 3)
      have hbig : 16482816 ≤ (2 ^ m) ^ 3 * ((2 ^ m) ^ 3 - 1) * ((2 ^ m) ^ 2 - 1) := by
        calc
          16482816 = 8 ^ 3 * (8 ^ 3 - 1) * (8 ^ 2 - 1) := by norm_num
          _ ≤ _ := by gcongr
      omega
  · obtain ⟨_,_,_,⟨er⟩⟩ := hgraph
    let := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (by simpa [Nat.card_eq_fintype_card] using hF)
    let j := (Theory.PSL2.sl2QuotientEquiv F).symm.toMonoidHom.comp
      ((commutator PSL(2,F)).subtype.comp (er.toMonoidHom.comp (inclusion hle)))
    exact no_mathieu_quotient_binary_sl2 j
      ((Theory.PSL2.sl2QuotientEquiv F).symm.injective.comp
        (Subtype.val_injective.comp (er.injective.comp (inclusion_injective hle)))) f hf
  · obtain ⟨m,J,hm,_,hconj,hcard,hfixed,⟨er⟩⟩ := hunitary
    have hq : 2 < 2 ^ m := by
      calc
        2 < 2 ^ 2 := by decide
        _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
    let U := ProjectiveSpecialUnitaryMatrixGroup J
    let : Finite U := Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
    let : IsSimpleGroup U := BenderSuzuki.External.huppert_II_10_13 J (2 ^ m) hq hcard hfixed
    let : IsSimpleGroup (pResidual 2 a.fixedSubgroup) := er.isSimpleGroup
    obtain ⟨ed⟩ := component_equiv_twoResidual D hD
    let eD := ed.trans er
    let : IsSimpleGroup B := (db.symm.trans eD).isSimpleGroup
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := db.toMonoidHom) db.surjective
    let em : U ≃* M22 := eD.symm.trans (db.trans (centerlessMathieuEquiv b))
    have hc : Nat.card U = 443520 := (Nat.card_congr em.toEquiv).trans m22_order
    have hr := HermitianForm.EvenTwoRank.two_rank J (by omega : 0 < m) hcard hconj
    rw [primeRank_equiv 2 em] at hr
    have hm4 : 4 ≤ m := hr ▸ m22_four_le_twoRank
    have hd := J.cube_dvd_card_projective hcard hfixed
    change (2 ^ m) ^ 3 ∣ Nat.card U at hd
    rw [hc,←pow_mul] at hd
    have hdiv : 4096 ∣ 443520 := (Nat.pow_dvd_pow 2 (by omega : 12 ≤ m * 3)).trans hd
    norm_num at hdiv

/-- The small symplectic derived endpoint has order 360. -/
theorem HasMathieuFixedComponent.not_binary_symplectic_derived (h : HasMathieuFixedComponent S)
    (e : S ≃* commutator (ClassicalGroup.PSp 2 (ZMod 2))) : False := by
  have hd := (h.of_mulEquiv
    (e.trans Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix)).card_dvd
  rw [nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd

/-- The G₂(2) derived endpoint has order 6048. -/
theorem HasMathieuFixedComponent.not_binary_g2_derived (h : HasMathieuFixedComponent S)
    (e : S ≃* commutator (Atlas.G2.Model (ZMod 2))) : False := by
  have hd := (h.of_mulEquiv e).card_dvd
  rw [Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
  norm_num at hd

/-- The actual Tits presentation has order prime to eleven. -/
theorem HasMathieuFixedComponent.not_tits (h : HasMathieuFixedComponent S)
    (e : S ≃* Tits.ParrottGroup) : False := by
  have hd := (h.of_mulEquiv e).card_dvd
  rw [Tits.parrottGroup_card] at hd
  norm_num at hd

open ChapterA.Section02 ClassificationModels

/-- The three odd Lie rows still requiring a fixed-component exclusion. -/
@[expose] def RemainingMathieuLargeOddModel (S : Type*) [Group S] : Prop :=
  (∃ p, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSp S 2 p) ∨
  (∃ p, p.Prime ∧ Odd p ∧ IsG2At S p) ∨
  (∃ p, p.Prime ∧ (∃ b : ℕ, p + 1 = 2 ^ b) ∧ ClassicalGroup.IsPSU S 4 p)

/-- The six rank-two families remaining after the linear-three and small
endpoint exclusions. Every row retains its actual model isomorphism. -/
@[expose] def RemainingMathieuRankTwoModel (S : Type*) [Group S] : Prop :=
  (∃ n, 1 ≤ n ∧ ClassicalGroup.IsPSU S 4 (2 ^ n)) ∨
  ClassicalGroup.IsPSU S 5 4 ∨
  (∃ n, 2 ≤ n ∧ ClassicalGroup.IsPSp S 2 (2 ^ n)) ∨
  (∃ n, 2 ≤ n ∧ IsG2At S (2 ^ n)) ∨
  (∃ n, 1 ≤ n ∧ Triality.Standard.IsTrialityGroupAt (2 ^ n) S) ∨
  (∃ m, 1 ≤ m ∧ Nonempty (S ≃* ReeF4.Model m))

/-- The remaining proper overcomponents: three odd Lie families, six binary
rank-two families, and McL. -/
@[expose] def RemainingMathieuProperModel (S : Type*) [Group S] : Prop :=
  RemainingMathieuLargeOddModel S ∨ RemainingMathieuRankTwoModel S ∨
    Nonempty (S ≃* Sporadic.LeechRelated.McL.Carrier)

/-- Remove the binary linear-three and all small derived rank-two endpoints. -/
theorem HasMathieuFixedComponent.rank_two_rows (h : HasMathieuFixedComponent S)
    {n : ℕ} (hm : IsRankTwoModel S n) : RemainingMathieuRankTwoModel S := by
  cases hm with
  | linear hn he => exact (h.not_binary_linear_three hn he).elim
  | unitary_four hn he => exact Or.inl ⟨n,hn,he⟩
  | unitary_five hn he => exact Or.inr (Or.inl (by simpa only [hn,Nat.reducePow] using he))
  | symplectic hn he => exact Or.inr (Or.inr (Or.inl ⟨n,hn,he⟩))
  | g2 hn he => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n,hn,he⟩)))
  | triality hn he => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n,hn,he⟩))))
  | ree_f4 m hm _ he => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨m,hm,he⟩))))
  | symplectic_derived _ he => exact (h.not_binary_symplectic_derived he.some).elim
  | g2_derived _ he => exact (h.not_binary_g2_derived he.some).elim
  | tits _ he => exact (h.not_tits he.some).elim

/-- The same faithful involution and Mathieu fixed component exclude the
Fermat-linear, binary-unitary, binary-linear-three and small endpoint rows. -/
theorem HasMathieuFixedComponent.remaining_rows [IsSimpleGroup S] [Group.IsPerfect S]
    (h : HasMathieuFixedComponent S) (hm : IsTheoremBModel S) :
    RemainingMathieuProperModel S := by
  rcases h.reduced_rows hm with ho | ⟨n,hn,he⟩ | ⟨n,hr⟩ | hmcl
  · rcases ho with hsp | hg | ⟨p,_,hp,he⟩ | hu
    · exact Or.inl (Or.inl hsp)
    · exact Or.inl (Or.inr (Or.inl hg))
    · exact (h.not_fermat_linear_four hp he).elim
    · exact Or.inl (Or.inr (Or.inr hu))
  · exact (h.not_binary_unitary_three hn he).elim
  · exact Or.inr (Or.inl (h.rank_two_rows hr))
  · exact Or.inr (Or.inr hmcl)

end CFSG.Quasithin.ChapterI.MathieuPumpup
