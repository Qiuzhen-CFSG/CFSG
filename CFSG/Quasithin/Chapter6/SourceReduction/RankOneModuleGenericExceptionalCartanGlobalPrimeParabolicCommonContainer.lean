module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeLargerMoved
public import CFSG.Quasithin.ChapterA.Section02.OddModelTwoRank
public import Theory.SpecificGroups.PSL3Even.TwoRank
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Ordinary common containers for the original diagram residual

The original residual has binary PSL₃, SL₃ or Sp₄ two-core quotient.
Its solvable-radical quotient has two-rank at least four, including the
full cubic SL₃ case. This rank is preserved by every solvable kernel.
A perfect subgroup of prime-field SL₂ has radical quotient of two-rank
at most two. Thus the common component containing the original residual
cannot have noncentral Fitting subgroup: A.3.6 would give just such a
prime-field SL₂ image through its literal Fitting quotient.

The same selected source pair therefore has an ordinary common component,
normal relative to the original common overgroup and containing the whole
original residual. Both the simple and triple-cover catalogues are retained.
The changed orbit remains a proper subgroup of this component; no equality
of the original and changed residuals or of their field degrees is assumed.

Source: Aschbacher–Smith A.3.6 and 5.2.2, printed pp.43–45,648–649,
refs/quasithin.pdf. The matrix two-ranks are the table on printed p.356.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime

private def radicalQuotientCenter (Q : Type*) [Group Q] [Finite Q] [IsQuasisimple Q] :
    (Q ⧸ solvableRadical Q) ≃* (Q ⧸ center Q) := by
  have he : solvableRadical Q = center Q := le_antisymm
    IsQuasisimple.solvableRadical_le_center
    (le_solvableRadical _ inferInstance (Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp b.property a))))
  exact QuotientGroup.quotientMulEquivOfEq he

private def radicalQuotientSimple (Q : Type*) [Group Q] [Finite Q]
    [Group.IsPerfect Q] [IsSimpleGroup Q] : (Q ⧸ solvableRadical Q) ≃* Q := by
  have he : solvableRadical Q = ⊥ := by
    apply (inferInstance : (solvableRadical Q).Normal).eq_bot_or_eq_top.resolve_right
    intro ht
    let : Group.IsSolvable (⊤ : Subgroup Q) := ht ▸
      (inferInstance : Group.IsSolvable (solvableRadical Q))
    exact Group.IsPerfect.not_isSolvable Q
      (Group.isSolvable_of_surjective (f := (topEquiv (G := Q)).toMonoidHom)
        (topEquiv (G := Q)).surjective)
  exact (QuotientGroup.quotientMulEquivOfEq he).trans QuotientGroup.quotientBot

private theorem diagram_radical_two_rank
    {Q : Type*} [Group Q] [Finite Q] {f : ℕ} (hf : 1 < f)
    (hm : ClassicalGroup.IsPSL Q 3 (2^f) ∨
      Chapter1.Section02.LocalModels.IsSL Q 3 (2^f) ∨
      ClassicalGroup.IsPSp Q 2 (2^f)) :
    4 ≤ primeRank 2 (Q ⧸ solvableRadical Q) := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,hF,⟨e⟩⟩
  · let : Group.IsPerfect SL(3,F) := Atlas.sl_perfect 3 (by decide)
    let : Group.IsPerfect PSL(3,F) := Group.IsPerfect.ofSurjective
      (QuotientGroup.mk'_surjective (center SL(3,F)))
    let : IsSimpleGroup PSL(3,F) := Atlas.psl_simple_high_rank 3 (by decide)
    let a := (QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)).trans
      (radicalQuotientSimple PSL(3,F))
    rw [primeRank_equiv 2 a, Matrix.PSL3Even.two_rank F (by omega) hF]
    omega
  · let : IsQuasisimple SL(3,F) :=
      { toIsPerfect := Atlas.sl_perfect 3 (by decide)
        simple := Atlas.psl_simple_high_rank 3 (by decide) }
    let a := (QuotientGroup.congr _ _ e (map_solvableRadical_equiv e)).trans
      (radicalQuotientCenter SL(3,F))
    rw [primeRank_equiv 2 a]
    change 4 ≤ primeRank 2 PSL(3,F)
    rw [Matrix.PSL3Even.two_rank F (by omega) hF]
    omega
  · let : Fintype F := Fintype.ofFinite F
    let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f)
      (by simpa only [Nat.card_eq_fintype_card] using hF)
    have hlarge : 3 < Nat.card F := by
      have hh := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ f by omega)
      omega
    let : IsQuasisimple (Theory.SpecificGroups.SymplecticFour.Sp F) :=
      Theory.SpecificGroups.SymplecticFour.CentralCovers.Even.isQuasisimple hlarge
    let a := e.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv.symm
    let b := (QuotientGroup.congr _ _ a (map_solvableRadical_equiv a)).trans
      (radicalQuotientCenter (Theory.SpecificGroups.SymplecticFour.Sp F))
    rw [primeRank_equiv 2 b,
      Theory.SpecificGroups.SymplecticFour.EvenTwoRank.projective_rank hF (by omega)]
    omega

private theorem primeSL2_radical_two_rank
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    {p : ℕ} [Fact p.Prime] (hp : 3 < p)
    (f : Y →* SL(2,ZMod p)) [Group.IsSolvable f.ker]
    (hn : 2 < primeRank 2 (Y ⧸ solvableRadical Y)) :
    primeRank 2 (Y ⧸ solvableRadical Y) ≤ 2 := by
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  let : Group.IsSolvable f.rangeRestrict.ker := by
    rwa [MonoidHom.ker_rangeRestrict]
  let e := solvableRadicalQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  have hnrange : Nontrivial f.range := by
    by_contra! ht
    let : Subsingleton f.range := ht
    have hz := primeRank_le_nat_card (G := f.range ⧸ solvableRadical f.range) 2
    rw [Nat.card_unique] at hz
    rw [primeRank_equiv 2 e] at hn
    omega
  let := hnrange
  obtain ⟨r,hr,hrlarge,⟨er⟩⟩ : ∃ r : ℕ, r.Prime ∧ 3 < r ∧
      Nonempty (f.range ≃* SL(2,ZMod r)) := by
    rcases ChapterA.RankActions.primePerfectSL2Recognition p hp f.range inferInstance inferInstance
      with hh | ⟨_,hh⟩
    · exact ⟨p,Fact.out,hp,hh⟩
    · exact ⟨5,by decide,by decide,hh⟩
  let : Fact r.Prime := ⟨hr⟩
  let a := e.trans (Theory.SpecificGroups.SL2.ResidualTwoExtension.radicalQuotientEquiv
    (by simpa using hrlarge) er)
  rw [primeRank_equiv 2 a]
  apply ChapterA.Section02.IsTheoremCOddModel.twoRank_le_two
  exact .linear_two r 1 hr (hr.odd_of_ne_two (by omega)) (by decide)
    ⟨ZMod r,inferInstance,inferInstance,by simp,⟨MulEquiv.refl _⟩⟩

variable {G : Type*} [Group G] [Finite G]

/-- The original diagram residual, including the full cubic linear cover,
has radical quotient of two-rank at least four. -/
theorem SelectedSourceModels.original_residual_radical_two_rank
    {H R : Subgroup G} (hs : SelectedSourceModels H R)
    (hn : ¬ (R.subgroupOf H).IsCComponent) :
    4 ≤ primeRank 2 ((residual H) ⧸ solvableRadical (residual H)) := by
  obtain ⟨f,hf,_,hm⟩ := hs.resolve_left hn
  let : Group.IsNilpotent (pCore 2 (pResidual 2 H)) := pCore_isNilpotent
  let q := QuotientGroup.mk' (pCore 2 (pResidual 2 H))
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let e := solvableRadicalQuotientEquiv q (QuotientGroup.mk'_surjective _)
  let a : pResidual 2 H ≃* residual H :=
    (pResidual 2 H).equivMapOfInjective H.subtype H.subtype_injective
  let b := QuotientGroup.congr _ _ a (map_solvableRadical_equiv a)
  rw [←primeRank_equiv 2 b,primeRank_equiv 2 e]
  exact diagram_radical_two_rank hf hm

private theorem quasisimple_of_large_radical_section
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y]
    (hQ : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    {I : Subgroup G} (hI : I.IsCComponent)
    (j : Y →* I) [Group.IsSolvable j.ker]
    (hr : 4 ≤ primeRank 2 (Y ⧸ solvableRadical Y)) : IsQuasisimple I := by
  have hc : fittingSubgroup I ≤ center I := by
    by_contra hn
    obtain ⟨p,hp,hp3,⟨ep⟩⟩ :=
      ChapterA.Section03.NoncentralFitting.primeSL2FittingQuotient_of_noncentral
        ChapterA.RankActions.primeSL2CoverRigidity hQ hO hI hn
    let : Fact p.Prime := ⟨hp⟩
    let f := ep.toMonoidHom.comp (QuotientGroup.mk' (fittingSubgroup I))
    have hk : f.ker = fittingSubgroup I := by
      rw [MonoidHom.ker_comp_of_injective _ _ ep.injective,QuotientGroup.ker_mk']
    let : Group.IsSolvable f.ker := by rw [hk]; infer_instance
    let : Group.IsSolvable (f.comp j).ker := by
      rw [←MonoidHom.comap_ker]
      exact isSolvable_comap_of_solvable_ker j f.ker
    have hb := primeSL2_radical_two_rank hp3 (f.comp j) (by omega)
    omega
  have he : solvableRadical I = center I := le_antisymm
    (solvableRadical_le_center_of_fitting_le_center hc)
    (le_solvableRadical _ inferInstance (Group.isSolvable_of_comm
      (fun a b => Subtype.ext (mem_center_iff.mp b.property a))))
  let := hI.perfect
  let := hI.isSimpleGroup_quotient_solvableRadical
  exact ⟨(QuotientGroup.quotientMulEquivOfEq he).symm.isSimpleGroup⟩

open Chapter1.Section02 LocalModels

/-- Any common component containing the original diagram residual has an
ordinary image in the literal ambient two-core quotient. No two-rank is
transported through a two-group kernel without first factoring the radical. -/
theorem SelectedSourceModels.parabolic_containing_component_models
    {T : Sylow 2 G} {L W H R X I : Subgroup G} {n : ℕ}
    (hs : SelectedSourceModels H R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hn : ¬ (R.subgroupOf H).IsCComponent)
    (hX : X ∈ Chapter1.H G)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    IsQuasisimple Ibar ∧
      ((IsSimpleGroup Ibar ∧ TheoremCModel Ibar) ∨
        (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel Ibar)) := by
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hl : K ∈ Chapter1.L G (T : Subgroup G) :=
    Chapter1.mem_L_of_cComponent hH.1.1.1
      ⟨T.subtype hH.1.1.2,map_subgroupOf_eq_of_le hH.1.1.2⟩ hKH
      (hs.residual_component_of_not_right hn)
  let : Group.IsPerfect K := Chapter1.mem_L_isPerfect hl
  let q := QuotientGroup.mk' (pCore 2 X)
  let Ibar := (I.subgroupOf X).map q
  let r := q.subgroupMap (I.subgroupOf X)
  let a := (subgroupOfEquivOfLe hIX).symm
  let j := (r.comp a.toMonoidHom).comp (inclusion hKI)
  have hk : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent r.ker := hk.isNilpotent
  let : Group.IsSolvable r.ker := inferInstance
  let : Group.IsSolvable (r.comp a.toMonoidHom).ker := by
    change Group.IsSolvable (r.ker.comap a.toMonoidHom)
    exact Group.isSolvable_of_isSolvable_injective
      (f := a.toMonoidHom.subgroupComap r.ker)
      (by intro x y hh; exact Subtype.ext (a.injective (congrArg Subtype.val hh)))
  let : Group.IsSolvable j.ker := by
    change Group.IsSolvable ((r.comp a.toMonoidHom).ker.comap (inclusion hKI))
    exact Group.isSolvable_of_isSolvable_injective
      (f := (inclusion hKI).subgroupComap (r.comp a.toMonoidHom).ker)
      (by intro x y hh; exact Subtype.ext ((inclusion_injective hKI) (congrArg Subtype.val hh)))
  have hQ := Chapter3.sqtk_of_mem_H h.qtke hX
  have hQbar : IsSQTK KnownSimple.IsKnownSimple (X ⧸ pCore 2 X) := by
    refine ⟨?_,hQ.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 X) pCore_isPGroup).trans
      (hQ.stronglyQuasithin p hp ho)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  have hi : Ibar.IsCComponent := hI.map_quotient (pCore 2 X)
  have hquasi := quasisimple_of_large_radical_section hQbar (pCore_quotient_pCore_eq_bot 2)
    hi j (hs.original_residual_radical_two_rank hn)
  let : IsQuasisimple Ibar := hquasi
  have hfit : generalizedFitting Ibar ≠ fittingSubgroup Ibar := by
    intro he
    have ht : fittingSubgroup Ibar = ⊤ := he.symm.trans generalizedFitting_eq_top_of_quasisimple
    let : Group.IsSolvable (⊤ : Subgroup Ibar) := ht ▸
      (inferInstance : Group.IsSolvable (fittingSubgroup Ibar))
    exact hi.not_isSolvable
      (Group.isSolvable_of_surjective (f := (topEquiv (G := Ibar)).toMonoidHom)
        (topEquiv (G := Ibar)).surjective)
  have hsource := ChapterA.SQTKStructure.a36Input_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple)
    (X ⧸ pCore 2 X) hQbar (pCore_quotient_pCore_eq_bot 2) Ibar hi
  refine ⟨hquasi,?_⟩
  cases hsource.1 with
  | simple _ hs hm => exact .inl ⟨hs,hm⟩
  | cover _ hc hm => exact .inr ⟨hc,hm⟩
  | natural h => exact (hfit h.1).elim
  | nilpotent h => exact (hfit h.1).elim

/-- The same selected pair has either zero generated two-core or a larger
Sylow parabolic inside an ordinary common component. The full original
residual and changed orbit retain their literal placements. -/
theorem source_prime_pair_parabolic_ordinary_common_container
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
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧ TheoremCModel Ibar) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel Ibar)))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_zero_or_larger_parabolic h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hm⟩
  · exact .inl hz
  refine .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hm,?_⟩
  let X := normalizer (normalizingSylow T R : Set G) ⊔ H
  obtain ⟨I,_,hIX,hI,_,hu,_,_,_,_,horbit⟩ :=
    d.changedSylow_common_orbit_strict h hH c hd hz P hlt.le hU
  obtain ⟨hKI,hIn⟩ := d.common_component_original_residual h hH c hd hz
    (hs.residual_component_of_not_right hn) hu
  have hTX : (T : Subgroup G) ≤ X :=
    (show (T : Subgroup G) ≤ H from hH.1.1.2).trans le_sup_right
  have hTI := hTX.trans ((normal_subgroupOf_iff_le_normalizer hIX).mp hIn)
  have he : conjugateSpanBy I (T : Subgroup G) = I :=
    le_antisymm (conjugateSpanBy_le le_rfl hTI) (le_conjugateSpanBy I _)
  refine ⟨I,hKI,hIX,hI,hIn,he ▸ horbit,?_⟩
  exact hs.parabolic_containing_component_models h hH hn
    (d.common_normal_overgroup h hH c hd hz).1 hIX hI hKI

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
