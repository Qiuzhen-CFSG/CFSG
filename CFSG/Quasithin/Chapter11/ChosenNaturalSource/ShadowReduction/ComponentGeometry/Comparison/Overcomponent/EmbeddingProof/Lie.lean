module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.SplitQuotients
public import Theory.SpecificGroups.Triality.BinaryLocalSections
public import Theory.SpecificGroups.Triality.SylowComponentUnique

/-!
# Excluding all characteristic-two Lie point overcomponents

For triality, a proper local image is a parabolic residual. Its intrinsic
quotient is PSL₂(q) or PSL₂(q³); at q = 2 the marked arm quotient supplies
PSL₂(8). Thus its proper Sylow overgroups are solvable in every case.
Together with the split and Ree calculations this excludes all seven Lie
rows of the complete 11.1.1 catalogue: a point component with such a quotient
cannot properly contain the original seed.

The root placement argument follows the local proof in
LocalGeometry.Components.Embedding.Triality, with its seed-model premise
removed. The binary case uses the actual marked arm quotient. Both field
conventions and all quotient kernels are preserved. The chosen-flag
application and maximality outside q = 4 are in EmbeddingProof; its remaining
field-four sieve and final equality belong to
qt-d-1222-shadow-component-comparison. Earlier source inputs retain final
discharge by qt-d-1222-shadow-components.
Source: Aschbacher--Smith A.3.12, 11.1.1 and 11.4.2, printed pp.47--48,761,776;
triality root geometry is GLS3 §§2.3--2.6.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings Chapter1.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

private theorem triality_perfect_le_local (P : Parameters) (a : Node)
    (B : Subgroup (Carrier P)) [Group.IsPerfect B] (hp : P.prime = 2)
    (hB : B ≤ parabolic P a) : B ≤ localFactor P a := by
  let Y := B.subgroupOf (parabolic P a)
  let : Group.IsPerfect Y := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  let : IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    parabolic_quotient_isCyclic P hp a
  let : CommGroup (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    IsCyclic.commGroup
  have h := le_of_isPerfect_of_solvable_quotient Y
    ((localFactor P a).subgroupOf (parabolic P a))
  intro x hx
  exact h (show (⟨x,hB hx⟩ : parabolic P a) ∈ Y from hx)

private theorem triality_local_placement {m : ℕ} (hm : 1 < m)
    (S : Sylow 2 (BinaryCarrier m (by omega))) (B : Subgroup (BinaryCarrier m (by omega)))
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (htop : (⊤ : Subgroup (BinaryCarrier m (by omega))).IsCComponent) :
    ∃ (g : BinaryCarrier m (by omega)) (a : Node),
      B.map (MulAut.conj g).toMonoidHom = localFactor (binaryParameters m (by omega)) a := by
  let P := binaryParameters m (by omega : 0 < m)
  have hq : 2 < P.q := by
    change 2 < 2 ^ m
    exact (by norm_num : 2 = 2 ^ 1) ▸ Nat.pow_lt_pow_right (by decide) hm
  have hjoin : B ⊔ (S : Subgroup (Carrier P)) ≠ ⊤ := by
    intro he
    change (B.subgroupOf (B ⊔ (S : Subgroup (Carrier P)))).IsCComponent at hB
    rw [he] at hB
    exact hproper (le_antisymm le_top (subgroupOf_eq_top.mp (htop.eq_top_of_isCComponent hB)))
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Carrier P) S (unipotentSylow P rfl)
  let a := MulAut.conj g
  let S' := S.mapSurjective (f := a.toMonoidHom) a.surjective
  let B' := B.map a.toMonoidHom
  have hS : (S' : Subgroup (Carrier P)) = unipotent P := congrArg Sylow.toSubgroup hg
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [a.toMonoidHom.ker_eq_bot_iff.mpr a.injective]
    infer_instance
  have hl : B' ∈ localCComponents S' := localCComponents_map_of_solvable_ker hB a.toMonoidHom
  let := hl.perfect
  let : Group.IsPerfect B' := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B' ≤ B' ⊔ (S' : Subgroup (Carrier P)) from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hp : (B ⊔ (S : Subgroup (Carrier P))).map a.toMonoidHom ≠ ⊤ := by
    intro ht
    apply hjoin
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [ht,map_top_of_surjective _ a.surjective]
  have hU : unipotent P ≤ (B ⊔ (S : Subgroup (Carrier P))).map a.toMonoidHom := by
    rw [← hS]
    exact map_mono (show (S : Subgroup (Carrier P)) ≤ B ⊔ (S : Subgroup (Carrier P)) from le_sup_right)
  obtain ⟨b,hb⟩ := OddSupplement.le_parabolic m (by omega) _ hU hp
  have hBP : B' ≤ parabolic P b := (map_mono le_sup_left).trans hb
  have hSP : (S' : Subgroup (Carrier P)) ≤ parabolic P b := (map_mono le_sup_right).trans hb
  have hBK : B' ≤ localFactor P b := triality_perfect_le_local P b B' rfl hBP
  have hSK := sylow_le_localFactor P b S' hSP
  let := localFactor_isPerfect P rfl hq b
  refine ⟨g,b,?_⟩
  cases b with
  | arms =>
    apply SourceEmbeddings.FiveLocalFF.local_eq_of_sl2_core_quotient (localFactor P .arms) ?_
      ((localFactorArmsQuotientEquivPSL2 P rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
      S' B' hl hBK hSK
    rw [card_extensionField]
    exact lt_of_lt_of_le hq (Nat.le_pow (by decide))
  | central =>
    apply SourceEmbeddings.FiveLocalFF.local_eq_of_sl2_core_quotient (localFactor P .central) ?_
      ((localFactorCentralQuotientEquivPSL2 P rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
      S' B' hl hBK hSK
    simpa only [card_baseField] using hq

private theorem triality_local_solvable {m : ℕ} (hm : 0 < m)
    (S : Sylow 2 (BinaryCarrier m hm)) (B : Subgroup (BinaryCarrier m hm))
    (hB : B ∈ localCComponents S) (hp : B ≠ ⊤)
    (hn : (S : Subgroup (BinaryCarrier m hm)) ≤ normalizer (B : Set (BinaryCarrier m hm)))
    (htop : (⊤ : Subgroup (BinaryCarrier m hm)).IsCComponent) :
    SolvableSylowOvergroups (B ⧸ pCore 2 B) := by
  by_cases hm1 : m = 1
  · subst m
    let := hB.perfect
    let : Group.IsPerfect B := Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup _) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
    have hns : ¬ Group.IsSolvable B := by
      intro hs
      let := hs
      exact hB.not_isSolvable (Group.isSolvable_of_isSolvable_injective
        (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ (S : Subgroup _) from le_sup_left)).toMonoidHom)
        (subgroupOfEquivOfLe le_sup_left).injective)
    obtain ⟨_,_,_,e,_⟩ := BinaryLocalSections.marked_arm_quotient (MulEquiv.refl _) S B hp hns hn
    exact SolvableSylowOvergroups.of_equiv
      (e.trans ((localFactorArmsQuotientEquivPSL2 _ rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm))
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
  · obtain ⟨g,a,hg⟩ := triality_local_placement (by omega : 1 < m) S B hB hp htop
    let e := ((MulAut.conj g).subgroupMap B).trans (MulEquiv.subgroupCongr hg)
    let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
    apply SolvableSylowOvergroups.of_equiv eq
    cases a with
    | arms =>
      exact SolvableSylowOvergroups.of_equiv
        ((localFactorArmsQuotientEquivPSL2 _ rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
        Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
    | central =>
      exact SolvableSylowOvergroups.of_equiv
        ((localFactorCentralQuotientEquivPSL2 _ rfl).trans (Theory.PSL2.sl2QuotientEquiv _).symm)
        Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup

/-- Triality retains both local fields, including the arm quotient of ³D₄(2). -/
theorem triality_quotient_local_solvable {B J : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hBJ : B < J)
    {m : ℕ} (hm : 0 < m)
    (hmodel : IsTrialityGroupAt (2 ^ m) (J ⧸ pCore 2 J)) :
    SolvableSylowOvergroups (B ⧸ pCore 2 B) := by
  obtain ⟨e⟩ := (isTrialityGroupAt_binary_iff _ m hm).mp hmodel
  obtain ⟨S,C,hC,hp,hn,⟨a⟩,htop⟩ := proper_local_model_image hB hJ hTJ hTB hBJ e
  exact SolvableSylowOvergroups.of_equiv a (triality_local_solvable hm S C hC hp hn htop)

/-- Every characteristic-two rank-two container in 11.1.1 has only rank-one
proper local quotients. The triality cube-field row is retained literally. -/
theorem lie_quotient_local_solvable {B J : Subgroup G}
    (hB : B ∈ Chapter1.L G (T : Subgroup G))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G)) (hBJ : B < J)
    {n : ℕ} (hn : 1 < n)
    (hm : LocalGeometry.Components.LieOvergroup (J ⧸ pCore 2 J) n) :
    SolvableSylowOvergroups (B ⧸ pCore 2 B) := by
  cases hm with
  | sl3 hm => exact split_quotient_local_solvable hB hJ hTJ hTB hBJ hn (.inl hm)
  | psl3 hm => exact split_quotient_local_solvable hB hJ hTJ hTB hBJ hn (.inr (.inl hm))
  | sp4 hm => exact split_quotient_local_solvable hB hJ hTJ hTB hBJ hn (.inr (.inr (.inl hm)))
  | g2 hm => exact split_quotient_local_solvable hB hJ hTJ hTB hBJ hn (.inr (.inr (.inr hm)))
  | ree m hp _ hm => exact ree_quotient_local_solvable hB hJ hTJ hTB hBJ hp hm
  | triality hm => exact triality_quotient_local_solvable hB hJ hTJ hTB hBJ (by omega) hm
  | trialityCube m hp _ hm => exact triality_quotient_local_solvable hB hJ hTJ hTB hBJ hp hm

variable {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}
    {E : Closure.Geometry D}

/-- A strict seed--point--overcomponent chain excludes every Lie row in
11.1.1, without replacing the original quotient by a simple group. -/
theorem not_lie_overcomponent (h : EarlierGeometry E)
    (hf : V ⊓ centralizer (L : Set G) = ⊥) (hne : E.Kz ≠ E.K)
    (hseed : E.L₁ ∈ Chapter1.L G (T : Subgroup G)) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J) :
    ¬ LocalGeometry.Components.LieOvergroup (J ⧸ pCore 2 J) E.input.field.degree := by
  intro hm
  have hs := lie_quotient_local_solvable h.point_mem_local_family hJ
    (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt
    E.input.nonbinary hm
  have he := local_eq_of_quotient_sylow_solvable hseed h.point_mem_local_family
    (sylow_normalizes_point h) (le_conjugateSpanBy _ _) hs
  exact (h.strict_comparison hf hne).2.1.ne he

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
