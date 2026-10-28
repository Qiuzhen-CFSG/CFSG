module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeJankoFour
public import CFSG.Quasithin.ChapterF.Section01.RankOneOddPrime
public import CFSG.Quasithin.ChapterA.Section01.RankActions.PerfectActions.LinearRecognition

/-!
# Removing noncentral-Fitting containers without an A₅ premise

The selected right factor has simple intrinsic two-core quotient: an actual
H-component is moved by the original Sylow, while a selected diagram parabolic
has its marked binary PSL₂ quotient. A solvable homomorphism kernel therefore
preserves this same quotient. Prime-field perfect-subgroup recognition and the
source rank-one model intersection force PSL₂(4) whenever the factor maps with
solvable kernel into prime-field SL₂.

Both noncentral-Fitting alternatives have just such a map, through the literal
containing image and its Fitting quotient. Hence the already proved smaller-Sylow
A₅ exclusion removes both alternatives. The selected-pair consumer now retains
only ordinary J₄ and odd ternary containing components, including cubic covers.
The larger-Sylow, zero-core and higher-field branches are not discharged here.

Source: Aschbacher–Smith A.1.29, A.3.6(3–4), 1.2.1(3), and 5.2.2,
printed pp.27,43–45,504,648–649 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

/-- Both genuine source selections have simple intrinsic two-core quotient in
the nonzero generated-core branch. Only actual H-components use full-Sylow placement. -/
theorem LocalData.selected_right_simple
    {T : Sylow 2 G} {L W H A B D R : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R) :
    IsSimpleGroup (R ⧸ pCore 2 R) := by
  rcases hs with hC | ⟨f,hf,⟨F,_,_,hF,⟨e⟩⟩,_⟩
  · apply Chapter1.Section02.MovedMaximality.moved_local_simple_core_quotient h.qtke T
      (d.right_mem_original_local_family hH.1.1 hC)
    rw [←d.residual_eq_conjugateSpan]
    exact d.right_lt_residual hH.1.1.2 c hd hz
  · have hlarge : 3 < Nat.card F := by
      have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
      omega
    exact e.isSimpleGroup_congr.mpr (Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge)

private def primeSL2_core_equiv {p : ℕ} [Fact p.Prime] (hp : 3 < p) (ho : Odd p) :
    (SL(2,ZMod p) ⧸ pCore 2 SL(2,ZMod p)) ≃* PSL(2,ZMod p) := by
  let : IsSimpleGroup PSL(2,ZMod p) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by simpa using (show 4 ≤ p by omega))
  let f := GorensteinWalter.sl2ProjectiveProjection (ZMod p)
  let e := f.pCoreQuotientEquiv (GorensteinWalter.sl2ProjectiveProjection_surjective _)
    (GorensteinWalter.sl2ProjectiveProjection_ker_isPGroup _ (by simpa using ho))
  have hc : pCore 2 PSL(2,ZMod p) = ⊥ := by
    apply (inferInstance : (pCore 2 PSL(2,ZMod p)).Normal).eq_bot_or_eq_top.resolve_right
    intro he
    let : Group.IsNilpotent (⊤ : Subgroup PSL(2,ZMod p)) := he ▸ pCore_isNilpotent (p := 2)
    let : Group.IsPerfect SL(2,ZMod p) :=
      GorensteinWalter.sl2_isPerfect_of_card_gt_three _ (by simpa using hp)
    let : Group.IsPerfect PSL(2,ZMod p) :=
      Group.IsPerfect.ofSurjective (GorensteinWalter.sl2ProjectiveProjection_surjective _)
    exact Group.IsPerfect.not_isSolvable PSL(2,ZMod p)
      (Group.isSolvable_of_surjective (f := (topEquiv (G := PSL(2,ZMod p))).toMonoidHom)
        (topEquiv (G := PSL(2,ZMod p))).surjective)
  exact e.trans ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot)

private theorem four_of_solvable_kernel_primeSL2
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    [IsSimpleGroup (Y ⧸ pCore 2 Y)]
    (hm : ChapterF.Source.IsRankOneModel (Y ⧸ pCore 2 Y))
    {p : ℕ} [Fact p.Prime] (hp : 3 < p) (ho : Odd p)
    (f : Y →* SL(2,ZMod p)) [Group.IsSolvable f.ker] :
    ClassicalGroup.IsPSL (Y ⧸ pCore 2 Y) 2 4 := by
  let : Nontrivial Y := (QuotientGroup.mk'_surjective (pCore 2 Y)).nontrivial
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  let e := PerfectCoreTwoExtension.solvableKernelQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  let : Nontrivial (f.range ⧸ pCore 2 f.range) := e.injective.nontrivial
  let : Nontrivial f.range := (QuotientGroup.mk'_surjective (pCore 2 f.range)).nontrivial
  obtain ⟨r,hr,hro,hrlarge,⟨er⟩⟩ : ∃ r : ℕ, r.Prime ∧ Odd r ∧ 3 < r ∧
      Nonempty (f.range ≃* SL(2,ZMod r)) := by
    rcases ChapterA.RankActions.primePerfectSL2Recognition p hp f.range inferInstance inferInstance
      with hh | ⟨_,hh⟩
    · exact ⟨p,Fact.out,ho,hp,hh⟩
    · exact ⟨5,by decide,by decide,by decide,hh⟩
  let : Fact r.Prime := ⟨hr⟩
  let eq := QuotientGroup.congr _ _ er (pCore_map_iso 2 er)
  let a := e.trans (eq.trans (primeSL2_core_equiv hrlarge hro))
  have hns : ¬ Group.IsSolvable (Y ⧸ pCore 2 Y) := by
    let : Group.IsPerfect (Y ⧸ pCore 2 Y) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
    exact Group.IsPerfect.not_isSolvable _
  have hr5 := hm.odd_prime_parameter hns hr hro hrlarge
    ⟨ZMod r,inferInstance,inferInstance,by simp,⟨a⟩⟩
  subst r
  let a5 : PSL(2,ZMod 5) ≃* alternatingGroup (Fin 5) :=
    Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_five.some
  have hfour : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by decide)]; norm_num
  let a4 := (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hfour).some
  exact ⟨GaloisField 2 2,inferInstance,inferInstance,hfour,⟨a.trans (a5.trans a4.symm)⟩⟩

open Chapter1.Section02 LocalModels

/-- Either noncentral-Fitting container forces the selected right quotient to
be PSL₂(4), using its literal Fitting quotient and solvable kernel. -/
theorem LocalData.source_overcomponent_noncentral_right_four
    {T : Sylow 2 G} {L W H A B D R X K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (hRX : R ≤ X) (hRK : R ≤ K)
    (hm : let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      A36Natural I ∨ A36Nilpotent I) :
    ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map q
  let Kbar := (K.subgroupOf X).map q
  let r := q.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let a := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ a (pCore_map_iso 2 a)
  let e₂ := r.pCoreQuotientEquiv (q.subgroupMap_surjective _) hr
  let eR : (R ⧸ pCore 2 R) ≃* (Rbar ⧸ pCore 2 Rbar) := e₁.trans e₂
  let : IsSimpleGroup (R ⧸ pCore 2 R) := d.selected_right_simple h hH c hd hz hs
  let : IsSimpleGroup (Rbar ⧸ pCore 2 Rbar) := eR.symm.isSimpleGroup
  let : Group.IsPerfect R := Chapter1.mem_L_isPerfect (d.right_mem_local_family h hH)
  let : Group.IsPerfect (R.subgroupOf X) := Group.IsPerfect.ofSurjective
    (f := a.toMonoidHom) a.surjective
  let : Group.IsPerfect Rbar := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective _)
  obtain ⟨s,hsprime,hslarge,F,_,_,hF,⟨eF⟩⟩ : ∃ s : ℕ, s.Prime ∧ 3 < s ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = s ∧
        Nonempty ((Kbar ⧸ fittingSubgroup Kbar) ≃* SL(2,F)) := by
    rcases hm with hn | hn
    · obtain ⟨s,hsprime,hslarge,F,_,_,hF,v,e,_⟩ := hn.2
      exact ⟨s,hsprime,hslarge,F,inferInstance,inferInstance,hF,
        ⟨(QuotientGroup.quotientMulEquivOfEq hn.1.symm).trans e⟩⟩
    · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hn.2.2.1
      exact ⟨5,by decide,by decide,F,inferInstance,inferInstance,hF,
        ⟨(QuotientGroup.quotientMulEquivOfEq hn.1.symm).trans e⟩⟩
  let : Fact s.Prime := ⟨hsprime⟩
  let : Fintype F := Fintype.ofFinite F
  let efield : F ≃+* ZMod s := FiniteField.ringEquivOfCardEq (by
    rw [←Nat.card_eq_fintype_card,←Nat.card_eq_fintype_card,hF,Nat.card_zmod])
  let f := (eF.trans (GorensteinWalter.sl2RingEquiv efield)).toMonoidHom.comp
    (QuotientGroup.mk' (fittingSubgroup Kbar))
  have hk : f.ker = fittingSubgroup Kbar := by
    rw [MonoidHom.ker_comp_of_injective _ _ (eF.trans (GorensteinWalter.sl2RingEquiv efield)).injective,
      QuotientGroup.ker_mk']
  let : Group.IsSolvable f.ker := by rw [hk]; infer_instance
  let i : Rbar →* Kbar := inclusion (map_mono (comap_mono hRK))
  let : Group.IsSolvable (f.comp i).ker := by
    change Group.IsSolvable (f.ker.comap i)
    apply Group.isSolvable_of_isSolvable_injective (f := i.subgroupComap f.ker)
    intro x y hxy
    apply Subtype.ext
    apply (inclusion_injective (map_mono (comap_mono hRK)))
    exact congrArg Subtype.val hxy
  exact (four_of_solvable_kernel_primeSL2 (d.right_quotient.of_equiv eR.symm)
    hslarge (hsprime.odd_of_ne_two (by omega)) (f.comp i)).of_mulEquiv eR

/-- The remaining smaller-Sylow catalogue has an actual ordinary component.
The noncentral-Fitting alternatives have been excluded, while the cubic covers
remain distinct from their projective quotients. -/
@[expose] def RemainingQuasisimpleSourceContainer (X K : Subgroup G) : Prop :=
  let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  A36Common I ∧ IsComponent (X ⧸ pCore 2 X) I ∧
    ((IsSimpleGroup I ∧ (Nonempty (I ≃* Janko4.Model) ∨
      ∃ q : ℕ, q.Prime ∧ Odd q ∧ ∃ u : Bool, IsPSLSign I u 3 q)) ∨
    (Nonempty (center I ≃* Multiplicative (ZMod 3)) ∧
      ∃ q : ℕ, q.Prime ∧ Odd q ∧ ∃ u : Bool, IsSLSign I u 3 q))

/-- The non-A₅ source factor cannot lie in either noncentral-Fitting row.
This applies to selected parabolics and actual H-components alike. -/
theorem LocalData.remaining_nonA5_source_container
    {T : Sylow 2 G} {L W H A B D R X K : Subgroup G} {n p : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥) (hs : SelectedSourceModels H R)
    (hRX : R ≤ X) (hRK : R ≤ K)
    (hnot : ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : RemainingSourceContainer X K) : RemainingQuasisimpleSourceContainer X K := by
  obtain ⟨hcommon,hcases⟩ := hm
  rcases hcases with ⟨hc,hs,hm⟩ | ⟨hc,hz,hm⟩ | hn | hn
  · exact ⟨hcommon,hc,.inl ⟨hs,hm⟩⟩
  · exact ⟨hcommon,hc,.inr ⟨hz,hm⟩⟩
  · exact (hnot (d.source_overcomponent_noncentral_right_four h hH c hd hz hs hRX hRK (.inl hn))).elim
  · exact (hnot (d.source_overcomponent_noncentral_right_four h hH c hd hz hs hRX hRK (.inr hn))).elim

/-- On the same selected pair the smaller-Sylow alternatives now have an
ordinary containing component, with all original quotient and Hall data retained. -/
theorem source_prime_pair_quasisimple_containing_remainder
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R ≤ T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ((T₁ = normalizingSylow T R ∧
            let X := generated L H D R ⊔ normalizingSylow T R
            let q := QuotientGroup.mk' (pCore 2 X)
            ∃ K : Subgroup G, R < K ∧ K ≤ X ∧
              (K.subgroupOf X).IsCComponent ∧ (K.subgroupOf X).Normal ∧
              (R.subgroupOf X).map q < (K.subgroupOf X).map q ∧
              RemainingQuasisimpleSourceContainer X K ∧
              ¬ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4) ∨
            (∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
              normalizingSylow T R < T₁ ∧ RemainingLargerSource H R p n)))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_nonA5_containing_remainder h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hTP,hDT,hcases⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hTP,hDT,?_⟩
  rcases hcases with ⟨he,K,hRK,hKX,hK,hKn,hlt,hm,hn⟩ | ha
  · refine .inl ⟨he,K,hRK,hKX,hK,hKn,hlt,?_,hn⟩
    exact d.remaining_nonA5_source_container h hH c hd hz hs
      (le_sup_left.trans (le_sup_right.trans le_sup_left)) hRK.le hn hm
  · exact .inr ha

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
