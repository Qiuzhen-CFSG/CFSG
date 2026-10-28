module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeConstruction
public import CFSG.Quasithin.ChapterF.Section01.SourceLocalResidual
public import CFSG.Quasithin.ChapterF.Section01.SourceFaithfulTriple
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure
public import Theory.SpecificGroups.DihedralSolvable
public import BenderSuzuki.MatrixGroups.SuzukiZero
public import Theory.GroupTheory.SolvableResidual.Transport

/-!
# Literal zero-core parabolics in original 5.2.2

For the constructed prime pair, the quotient of DS is S₃ when the actor
has order three, and D₁₀ or Sz(2) when it has order five. The common Borel
is exactly S(B ∩ R), and its index in DSB₂ is the original prime. Both
parabolics have S as a Sylow subgroup, their intersection is this whole
Borel, and the pair is faithful. The first parabolic is solvable and the
second is not.

The selected R is the embedded solvable residual of RS. Consequently an
actual isomorphism of the right parabolic transports R/O₂(R) to the model's
solvable-residual quotient, with the original inclusion on representatives.
This is preparation for the zero-core model exclusions; no classification
of F.1.1 configurations or identification S = T is assumed.

Source: Aschbacher–Smith, 5.2.2, printed pp.647–648, and F.1.3, F.1.9,
printed pp.260–262 (`refs/quasithin.pdf`). Final source assembly remains
with qt-d-1222-rankone-cartan-local-to-global.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Prime index identifies the concrete quotient and retains which prime occurs. -/
theorem LocalData.prime_left_quotient_cases
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    let J := D ⊔ Global.sourceS L H
    (p = 3 ∧ Nonempty ((J ⧸ pCore 2 J) ≃* Equiv.Perm (Fin 3))) ∨
      (p = 5 ∧ (Nonempty ((J ⧸ pCore 2 J) ≃* DihedralGroup 5) ∨
        Nonempty ((J ⧸ pCore 2 J) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0))) := by
  let S := Global.sourceS L H
  let J := D ⊔ S
  obtain ⟨P,hP⟩ := Input.prime_left_sylow h hH c hd
  have hP' : (P : Subgroup J) = S.subgroupOf J := by
    apply map_injective J.subtype_injective
    rw [hP,map_subgroupOf_eq_of_le le_sup_right]
  have hi : P.index = p := by
    rw [hP']
    exact Input.prime_left_index h hH c hd
  have hproper : pCore 2 J < (P : Subgroup J) := by
    refine lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal P) ?_
    intro he
    have hn : (S.subgroupOf J).Normal := by rw [←hP',←he]; infer_instance
    exact zero_core_not_normalizes_sourceS h hH d.S_intersection_residual hd.zero_core
      (le_sup_left.trans ((normal_subgroupOf_iff_le_normalizer
        (show S ≤ J from le_sup_right)).mp hn))
  rcases hd.prime with hp | hp
  · exact Or.inl ⟨hp,sylow_index_three_core_quotient P (hi.trans hp) hproper⟩
  · exact Or.inr ⟨hp,sylow_index_five_core_quotient P (hi.trans hp) hproper⟩

/-- The literal prime-actor group DS is solvable in both prime cases. -/
theorem LocalData.prime_left_solvable
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    Group.IsSolvable (D ⊔ Global.sourceS L H : Subgroup G) := by
  let J := D ⊔ Global.sourceS L H
  rcases d.prime_left_quotient_cases h hH c hd with ⟨_,⟨e⟩⟩ | ⟨_,he⟩
  · exact SymmetricThreeTwoCore.solvable e
  · have hq : Group.IsSolvable (J ⧸ pCore 2 J) := by
      rcases he with he | he
      · let := GLS3.Chapter5.dihedralGroup_isSolvable 5
        exact Group.isSolvable_of_isSolvable_injective (f := he.some.toMonoidHom) he.some.injective
      · let := BenderSuzuki.MatrixGroups.suzukiZero_isSolvable
        exact Group.isSolvable_of_isSolvable_injective (f := he.some.toMonoidHom) he.some.injective
    let := hq
    let : Group.IsNilpotent (pCore 2 J) := pCore_isPGroup.isNilpotent
    exact (Group.isSolvable_iff_subgroup_quotient (pCore 2 J)).mpr
      ⟨inferInstance,inferInstance⟩

omit [Finite G] in
/-- The whole overlap is SB₂, with B₂ the original B ∩ R. -/
theorem LocalData.zeroCore_commonBorel
    {T : Sylow 2 G} {L H B D R : Subgroup G}
    (d : LocalData T L H B D R) (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    ChapterF.Source.commonBorel ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) =
      Global.sourceS L H ⊔ (B ⊓ R) := by
  change (ChapterF.Source.borel (D ⊔ Global.sourceS L H) (Global.sourceS L H) ⊔
    ChapterF.Source.borel R (Global.sourceS L H)) ⊔ Global.sourceS L H = _
  rw [d.left_borel hz,d.right_borel]
  rw [←sup_assoc,sup_inf_self,sup_right_comm,sup_idem]

omit [Finite G] in
/-- The first parabolic is the literal DSB₂ product. -/
theorem LocalData.zeroCore_parabolic_zero
    {T : Sylow 2 G} {L H B D R : Subgroup G}
    (d : LocalData T L H B D R) :
    ChapterF.Source.parabolic ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 0 =
      (D ⊔ Global.sourceS L H) ⊔ (B ⊓ R) := by
  change ((D ⊔ Global.sourceS L H) ⊔ Global.sourceS L H) ⊔
    ChapterF.Source.borel R (Global.sourceS L H) = _
  rw [d.right_borel]
  rw [sup_assoc D, sup_idem,←sup_assoc,
    sup_eq_left.mpr (inf_le_left.trans (show Global.sourceS L H ≤ D ⊔ Global.sourceS L H from le_sup_right))]

/-- The two literal parabolics intersect in precisely SB₂. -/
theorem LocalData.zeroCore_parabolic_intersection
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)) ⊓ (R ⊔ Global.sourceS L H) =
      Global.sourceS L H ⊔ (B ⊓ R) := by
  have hh := ChapterF.Source.lemma_F_1_3_6 (d.hypothesisF11 h hH c hd hz)
  rwa [d.zeroCore_parabolic_zero,d.parabolic_one hz,d.zeroCore_commonBorel hz] at hh

/-- The index of the whole overlap in the first parabolic is the chosen prime. -/
theorem LocalData.zeroCore_left_index
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    (Global.sourceS L H ⊔ (B ⊓ R)).relIndex
      ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R)) = p := by
  let S := Global.sourceS L H
  let J := D ⊔ S
  let C := S ⊔ (B ⊓ R)
  have hf := d.hypothesisF11 h hH c hd hz
  have hn : C ≤ normalizer (J : Set G) := by
    change Global.sourceS L H ⊔ (B ⊓ R) ≤ _
    rw [←d.zeroCore_commonBorel hz]
    exact hf.commonBorel_normalizes_local 0
  have hCJ : C ⊓ J = S := by
    have hnS : C ≤ normalizer (S : Set G) := by
      have hh := hf.commonBorel_normalizes_localSylow 0
      change ChapterF.Source.commonBorel ![J,R] S ≤ normalizer ((S ⊓ J : Subgroup G) : Set G) at hh
      rw [inf_eq_left.mpr (show S ≤ J from le_sup_right),d.zeroCore_commonBorel hz] at hh
      exact hh
    apply le_antisymm
    · have hh : C ⊓ J ≤ ChapterF.Source.borel J S := by
        rw [ChapterF.Source.borel,inf_eq_left.mpr (show S ≤ J from le_sup_right)]
        exact le_inf inf_le_right (inf_le_left.trans hnS)
      exact hh.trans (d.left_borel hz).le
    · exact le_inf le_sup_left le_sup_right
  have he : (D ⊔ S) ⊔ (B ⊓ R) = J ⊔ C := by
    dsimp [J,C]
    simp only [sup_assoc,sup_left_idem]
  change C.relIndex ((D ⊔ S) ⊔ (B ⊓ R)) = p
  rw [he,relIndex_sup_of_normalizes J C hn,←inf_relIndex_right,hCJ]
  exact Input.prime_left_index h hH c hd

/-- The original pair has a solvable left endpoint and nonsolvable right endpoint. -/
theorem LocalData.zeroCore_mixed_solvability
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    Group.IsSolvable ((D ⊔ Global.sourceS L H) ⊔ (B ⊓ R) : Subgroup G) ∧
      ¬ Group.IsSolvable (R ⊔ Global.sourceS L H : Subgroup G) := by
  have hf := d.hypothesisF11 h hH c hd hz
  have hs : Group.IsSolvable (ChapterF.Source.parabolic
      ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 0) := by
    apply (hf.parabolic_solvable_iff_local_quotient 0).mpr
    change Group.IsSolvable ((D ⊔ Global.sourceS L H : Subgroup G) ⧸
      pCore 2 (D ⊔ Global.sourceS L H : Subgroup G))
    let := d.prime_left_solvable h hH c hd
    infer_instance
  exact ⟨d.zeroCore_parabolic_zero ▸ hs,d.parabolic_one hz ▸ d.right_parabolic_not_solvable hz⟩

/-- Perfectness of the selected component identifies it with the right residual. -/
theorem LocalData.zeroCore_right_residual
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    (solvableResidual (R ⊔ Global.sourceS L H : Subgroup G)).map
      (R ⊔ Global.sourceS L H : Subgroup G).subtype = R := by
  let := d.right_component.perfect
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show R ≤ R ⊔ normalizingSylow T R from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective
  have hh := (d.hypothesisF11 h hH c hd hz).local_residual_eq_parabolic 1
  change (solvableResidual R).map R.subtype = _ at hh
  rw [solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype,d.parabolic_one hz] at hh
  exact hh.symm

/-- A right-parabolic isomorphism transports the original quotient, including representatives. -/
theorem LocalData.zeroCore_right_quotient_transport
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    {X : Type*} [Group X] (e : (R ⊔ Global.sourceS L H : Subgroup G) ≃* X) :
    ∃ f : (R ⧸ pCore 2 R) ≃* (solvableResidual X ⧸ pCore 2 (solvableResidual X)),
      ∀ x : R, ∃ y : solvableResidual X,
        (y : X) = e (inclusion (show R ≤ R ⊔ Global.sourceS L H from le_sup_left) x) ∧
        f (QuotientGroup.mk' (pCore 2 R) x) =
          QuotientGroup.mk' (pCore 2 (solvableResidual X)) y := by
  let P := R ⊔ Global.sourceS L H
  let a : solvableResidual P ≃* R :=
    ((solvableResidual P).equivMapOfInjective P.subtype P.subtype_injective).trans
      (MulEquiv.subgroupCongr (d.zeroCore_right_residual h hH c hd hz))
  let b := a.symm.trans e.solvableResidualEquiv
  refine ⟨QuotientGroup.congr _ _ b (pCore_map_iso 2 b),?_⟩
  intro x
  refine ⟨b x,?_,rfl⟩
  change e (a.symm x : P) = e (inclusion le_sup_left x)
  apply congrArg e
  apply Subtype.ext
  exact congrArg (fun z : R => (z : G)) (a.apply_symm_apply x)

/-- The literal S is Sylow in each endpoint and their overlap has trivial common normal kernel. -/
theorem LocalData.zeroCore_sylows_and_faithfulness
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥) :
    let S := Global.sourceS L H
    Chapter1.IsSylowIn 2 S ((D ⊔ S) ⊔ (B ⊓ R)) ∧
      Chapter1.IsSylowIn 2 S (R ⊔ S) ∧
      ∀ N : Subgroup G, N ≤ S ⊔ (B ⊓ R) →
        (D ⊔ S) ⊔ (B ⊓ R) ≤ normalizer (N : Set G) →
        R ⊔ S ≤ normalizer (N : Set G) → N = ⊥ := by
  have hf := d.hypothesisF11 h hH c hd hz
  have hs0 := hf.sylow_parabolic 0
  have hs1 := hf.sylow_parabolic 1
  rw [d.zeroCore_parabolic_zero] at hs0
  rw [d.parabolic_one hz] at hs1
  refine ⟨hs0,hs1,?_⟩
  intro N hN h0 h1
  apply hf.common_normal_eq_bot N
  · rwa [d.zeroCore_commonBorel hz]
  · intro i
    fin_cases i
    · change ChapterF.Source.parabolic ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 0 ≤ _
      rwa [d.zeroCore_parabolic_zero]
    · change ChapterF.Source.parabolic ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H) 1 ≤ _
      rwa [d.parabolic_one hz]

/-- A perfect right parabolic equals the original selected factor, so it contains S. -/
theorem LocalData.zeroCore_right_eq_of_perfect_parabolic
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 = ⊥)
    [Group.IsPerfect (R ⊔ Global.sourceS L H : Subgroup G)] :
    R = R ⊔ Global.sourceS L H := by
  have hh := d.zeroCore_right_residual h hH c hd hz
  rw [solvableResidual_eq_top,←MonoidHom.range_eq_map,range_subtype] at hh
  exact hh.symm

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
