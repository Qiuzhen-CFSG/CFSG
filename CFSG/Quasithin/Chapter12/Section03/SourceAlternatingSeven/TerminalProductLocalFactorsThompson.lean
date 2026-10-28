module
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.TerminalProductLocalFactorsIdentification
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd.SevenThompson
public import CFSG.Quasithin.ChapterB.Section03.Offenders.Odd

/-!
# Thompson generation of the literal second terminal factor

The original seven-letter action sends maximum elementary subgroups to
best offenders. Its nontrivial offender and the disjoint-transposition
classification put every Sylow transposition in the literal Thompson image.
At the selected weight-four point one such transposition interchanges two
complementary letters, so the second cubic factor has nontrivial commutator
image. Normality, simplicity of A₃ and two-perfection lift that image to
the whole original residual. This proves [L₂,J(T)]=L₂ and constructs all
fields of LocalFactorAnalysis.

ComponentAnalysis remains the explicit premise discharged by
qt-d-1231-terminal. The marked product and ProductAnalysis remain with
qt-d-1231-terminal-product.
Source: Aschbacher--Smith 12.3.7(1) and completion of 12.3.1, pp.809,812.
-/

@[expose] public noncomputable section
open scoped Pointwise

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Subgroup Theory.GroupTheory Stellmacher Section02 BinarySevenCode
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
namespace Setup.LocalAnalysis
variable (D : S.LocalAnalysis)
private theorem source_permutation_agrees
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (n : normalizer (V : Set G)) :
    (D.naturalCoordinates.sourceNormalizerModel structural).permutation n =
      D.model.permutation n := by
  have hs : ((D.naturalCoordinates.sourceNormalizerModel structural).permutation n).symm =
      (D.model.permutation n).symm := by
    apply Equiv.ext
    intro i
    apply coordinates_separated
    intro w hw
    let v : V := D.model.coordinates.symm
      (Multiplicative.ofAdd (⟨w,simplexCode_le_evenWords hw⟩ : EvenWord))
    have h₁ := (D.naturalCoordinates.sourceNormalizerModel structural).equivariant n v
    have h₂ := D.model.equivariant n v
    have h := h₁.symm.trans h₂
    change evenRepresentation
      ((D.naturalCoordinates.sourceNormalizerModel structural).permutation n)
        (D.model.coordinates v).toAdd =
      evenRepresentation (D.model.permutation n) (D.model.coordinates v).toAdd at h
    have he := congrArg (fun x : EvenWord => x.val i) h
    simpa only [v,D.model.coordinates.apply_symm_apply,toAdd_ofAdd,
      evenRepresentation_apply] using he
  simpa only [Equiv.symm_symm] using congrArg Equiv.symm hs


/-- Every transposition in the actual Sylow permutation image occurs in the
image of its actual maximum elementary Thompson subgroup. -/
theorem swap_mem_thompson_image
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) {s : Equiv.Perm (Fin 7)} (hs : s.IsSwap)
    (hsT : s ∈ ((T : Subgroup G).subgroupOf (normalizer (V : Set G))).map D.model.permutation) :
    s ∈ ((elementaryAbelianMaxJ (T : Subgroup G)).subgroupOf
      (normalizer (V : Set G))).map D.model.permutation := by
  classical
  let N := normalizer (V : Set G)
  let hTV := ((structural G T L S.hypothesis).2.2 V S.chosen).1
  let R := T.subtype hTV
  have he : (D.naturalCoordinates.sourceNormalizerModel structural).permutation = D.model.permutation :=
    MonoidHom.ext (D.source_permutation_agrees structural)
  have hex : ∃ A ∈ elementaryAbelianMaxSubgroups (T : Subgroup G),
      ¬ A ≤ centralizer (V : Set G) := by
    by_contra! hn
    exact D.naturalCoordinates.thompson_not_centralizes_of_generation
      (D.thompson_generation structural escape) (sSup_le hn)
  obtain ⟨A,hA,hAC⟩ := hex
  have hn : (A.subgroupOf N).map D.model.permutation ≠ ⊥ := by
    intro hz
    have hk := (Subgroup.map_eq_bot_iff _).mp hz
    rw [Setup.NaturalCoordinates.normalizerModel_kernel] at hk
    apply hAC
    intro a ha v hv
    exact congrArg (fun x : N => (x : G)) (hk
      (show (⟨a,hTV (hA.1 ha)⟩ : N) ∈ A.subgroupOf N from ha)
      ⟨v,V.le_normalizer hv⟩ hv)
  have hbest := D.naturalCoordinates.maxElementary_image_bestOffender structural A hA
    (by rwa [he])
  rw [he] at hbest
  have hA' : A.subgroupOf N ∈ elementaryAbelianMaxSubgroups (R : Subgroup N) := by
    apply (maxFamily_map_injective_iff N.subtype N.subtype_injective _ _).mp
    rwa [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV,
      map_subgroupOf_eq_of_le (hA.1.trans hTV)]
  have hh := ChapterB.Offenders.swap_mem_thompson_image_of_caseAFamily R D.model.permutation
    (MonoidHom.range_eq_top.mp (D.permutation_range_eq_top structural escape))
    (A.subgroupOf N) hA'
    ((ChapterB.Offenders.Odd.isBestOffender_natural_iff_caseAFamily (Or.inr rfl) _).mp hbest)
    hs hsT
  obtain ⟨j,hj,heq⟩ := hh
  refine ⟨j,?_,heq⟩
  have hmap : (elementaryAbelianMaxJ (R : Subgroup N)).map N.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTV]
  exact hmap ▸ mem_map_of_mem N.subtype hj
end Setup.LocalAnalysis

namespace TerminalPoint
variable {D : S.LocalAnalysis} (P : TerminalPoint S D)

private theorem weightFour_complement_swap (w : EvenWord) (hw : weight w.val = 4)
    (Q : Sylow 2 (Equiv.Perm (Fin 7)))
    (hQC : (Q : Subgroup (Equiv.Perm (Fin 7))) ≤ WeightTwoGeometry.symmetricStabilizer w) :
    ∃ i j : WeightTwoGeometry.Complement w, i ≠ j ∧ Equiv.swap i.val j.val ∈ Q := by
  open WeightTwoGeometry in
  have hn : Nontrivial (Complement w) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [Nat.card_eq_fintype_card,WeightFourLocal.complement_card w hw]; decide)
  obtain ⟨i,j,hij⟩ := exists_pair_ne (WeightTwoGeometry.Complement w)
  have ht : Equiv.swap i.val j.val ∈ WeightTwoGeometry.symmetricStabilizer w := by
    rw [WeightTwoGeometry.mem_symmetricStabilizer]
    apply Subtype.ext
    funext k
    change w.val ((Equiv.swap i.val j.val).symm k) = w.val k
    have hi : w.val i.val = 0 := by
      have h := Finset.mem_compl.mp i.property
      simpa only [WeightTwoGeometry.support,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using h
    have hj : w.val j.val = 0 := by
      have h := Finset.mem_compl.mp j.property
      simpa only [WeightTwoGeometry.support,Finset.mem_filter,Finset.mem_univ,true_and,not_not] using h
    simp only [Equiv.symm_swap,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  let t : WeightTwoGeometry.symmetricStabilizer w := ⟨Equiv.swap i.val j.val,ht⟩
  have hp : IsPGroup 2 (zpowers t) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers]
    apply orderOf_dvd_of_pow_eq_one
    exact Subtype.ext (by change (Equiv.swap i.val j.val)^2 = 1; simp [pow_two]))
  obtain ⟨R,hR⟩ := hp.exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (WeightTwoGeometry.symmetricStabilizer w) R (Q.subtype hQC)
  have htR : g * t * g⁻¹ ∈ Q.subtype hQC := by
    rw [←hg]
    exact mem_map_of_mem (MulAut.conj g).toMonoidHom (hR (mem_zpowers t))
  let a := WeightTwoGeometry.complementPermutation w g i
  let b := WeightTwoGeometry.complementPermutation w g j
  refine ⟨a,b,(WeightTwoGeometry.complementPermutation w g).injective.ne hij,?_⟩
  have he : Equiv.swap a.val b.val = g.val * t.val * g.val⁻¹ :=
    Equiv.swap_apply_apply g.val i.val j.val
  rw [he]
  exact htR

/-- The actual Thompson image has a nonidentity involution in the three-letter
block of the selected weight-four point. -/
theorem exists_thompson_second_involution
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) :
    ∃ j : P.pointNormalizer, (j : G) ∈ elementaryAbelianMaxJ (T : Subgroup G) ∧
      (P.pointBlockAction j).2 ^ 2 = 1 ∧ (P.pointBlockAction j).2 ≠ 1 := by
  let N := normalizer (V : Set G)
  let hTV := ((structural G T L S.hypothesis).2.2 V S.chosen).1
  let R := T.subtype hTV
  let Q := R.mapSurjective (MonoidHom.range_eq_top.mp (D.permutation_range_eq_top structural escape))
  have hQC : (Q : Subgroup (Equiv.Perm (Fin 7))) ≤
      WeightTwoGeometry.symmetricStabilizer (D.model.coordinates P.point).toAdd := by
    rintro g ⟨t,ht,rfl⟩
    exact (D.model.pointPermutation P.point ⟨t,P.sylow_le_pointNormalizer structural ht⟩).property
  obtain ⟨i,k,hik,hikQ⟩ := weightFour_complement_swap (D.model.coordinates P.point).toAdd
    P.weight_four Q hQC
  have hik' : i.val ≠ k.val := fun h => hik (Subtype.ext h)
  have hJ := D.swap_mem_thompson_image structural escape
    (show (Equiv.swap i.val k.val).IsSwap from ⟨i.val,k.val,hik',rfl⟩) hikQ
  obtain ⟨j,hj,hjπ⟩ := hJ
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) := sSup_le (fun _ h => h.1)
  have hjT : (j : G) ∈ (T : Subgroup G) := hJT hj
  let jP : P.pointNormalizer := ⟨j,P.sylow_le_pointNormalizer structural hjT⟩
  refine ⟨jP,hj,?_,?_⟩
  · have hpow : (D.model.pointPermutation P.point jP)^2 = 1 := by
      apply Subtype.ext
      change (D.model.permutation j)^2 = 1
      rw [hjπ]
      simp [pow_two]
    have hh : (P.pointBlockAction jP)^2 = 1 := by
      change (WeightFourLocal.pointEquiv _ P.weight_four (D.model.pointPermutation P.point jP))^2 = 1
      rw [←map_pow,hpow,map_one]
    exact congrArg Prod.snd hh
  · intro hz
    have h := P.pointBlockAction_second jP i
    rw [hz] at h
    have he : WeightTwoGeometry.complementPermutation (D.model.coordinates P.point).toAdd
        (D.model.pointPermutation P.point jP) i = k := by
      apply Subtype.ext
      change D.model.permutation j i.val = k.val
      rw [hjπ,Equiv.swap_apply_left]
    rw [he] at h
    exact hik ((WeightFourLocal.threeLetters _ P.weight_four).injective h)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven

namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Subgroup Theory.GroupTheory Stellmacher Section02 BinarySevenCode
open scoped commutatorElement
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V} {D : S.LocalAnalysis}
namespace TerminalPoint
variable (P : TerminalPoint S D)

private theorem involution_moves_three (s : Equiv.Perm (Fin 3))
    (hs : s^2 = 1) (hne : s ≠ 1) :
    ∃ a : alternatingGroup (Fin 3), a.val*s ≠ s*a.val := by
  revert s
  decide

/-- The literal second residual is generated by its commutators with J(T),
using its original three-letter action and two-group kernel. -/
theorem secondPointResidual_thompson
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ⁅P.secondPointResidual,elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.secondPointResidual := by
  let R := P.secondPointResidual
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  let B := ⁅R,J⁆
  have hJT : J ≤ (T : Subgroup G) := sSup_le (fun _ h => h.1)
  have hJN : J ≤ P.pointNormalizer := hJT.trans (P.sylow_le_pointNormalizer structural)
  have hBR : B ≤ R := le_normalizer_iff_commutator_le_left.mp
    (hJN.trans P.secondPointResidual_normalized)
  let N := B.subgroupOf R
  let : N.Normal := normal_subgroupOf_of_le_normalizer (normalizer_commutator_ge_left R J)
  let f := P.secondResidualProjection structural escape
  let : (N.map f).Normal := Normal.map inferInstance f
    (P.secondResidualProjection_surjective structural escape)
  have hcard : Nat.card (alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card,card_alternatingGroup]; decide
  let : IsSimpleGroup (alternatingGroup (Fin 3)) := isSimpleGroup_of_prime_card hcard
  have hi : N.map f = ⊤ := by
    rcases (inferInstance : (N.map f).Normal).eq_bot_or_eq_top with hz | ht
    · exfalso
      have hNk : N ≤ f.ker := (map_eq_bot_iff N).mp hz
      obtain ⟨j,hj,hs,hne⟩ := P.exists_thompson_second_involution structural escape
      obtain ⟨a,ha⟩ := involution_moves_three (P.pointBlockAction j).2 hs hne
      obtain ⟨r,hr⟩ := P.secondResidualProjection_surjective structural escape a
      let b : R := ⟨⁅(r : G),(j : G)⁆,hBR (commutator_mem_commutator r.property hj)⟩
      have hb : f b = 1 := hNk (commutator_mem_commutator r.property hj)
      let q := (MonoidHom.snd _ _).comp P.pointBlockAction
      let rP := inclusion P.secondPointResidual_le_pointNormalizer r
      have he : inclusion P.secondPointResidual_le_pointNormalizer b = ⁅rP,j⁆ := Subtype.ext rfl
      have hb' : q (inclusion P.secondPointResidual_le_pointNormalizer b) = 1 :=
        congrArg Subtype.val hb
      rw [he,map_commutatorElement,commutatorElement_eq_one_iff_mul_comm] at hb'
      have hr' : q rP = a.val := congrArg Subtype.val hr
      rw [hr'] at hb'
      exact ha hb'
    · exact ht
  have ht : (⊤ : Subgroup R) ≤ N := by
    apply isPPerfect_le_of_map_le_of_kernel_normalizes f ⊤ N
      (P.secondPointResidual_twoPerfect.of_surjective
        (topEquiv : (⊤ : Subgroup R) ≃* R).symm.toMonoidHom
        (topEquiv : (⊤ : Subgroup R) ≃* R).symm.surjective)
      (P.secondResidualProjection_twoKernel structural escape C) le_normalizer_of_normal
    rw [hi]
    exact le_top
  apply le_antisymm hBR
  intro x hx
  exact ht (show (⟨x,hx⟩ : R) ∈ (⊤ : Subgroup R) from mem_top _)

/-- Source p.812's second Thompson equality, on the published literal L₂. -/
theorem L2_thompson
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    ⁅P.L2,elementaryAbelianMaxJ (T : Subgroup G)⁆ = P.L2 := by
  rw [←P.secondPointResidual_eq_L2 structural escape C]
  exact P.secondPointResidual_thompson structural escape C

/-- All source local-factor conclusions are now constructed. The only
terminal premise is ComponentAnalysis, discharged by qt-d-1231-terminal. -/
theorem localFactorAnalysis
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (escape : CentralizerEscape T) (C : P.ComponentAnalysis) :
    Nonempty P.LocalFactorAnalysis :=
  P.localFactorAnalysis_of_second_thompson structural escape C (P.L2_thompson structural escape C)

end TerminalPoint
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
