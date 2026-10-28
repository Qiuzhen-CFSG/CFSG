module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalOvercomponent
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingFiveShortlist
public import Theory.GroupAction.QuotientConjugation
public import Theory.GroupTheory.SmallNonabelianTwoGroupAutomorphismOrderCoarse

/-!
# The L₃(4) branch of source 5.2.8

Let K = O²(H). The preceding core comparison gives O₂(J) = O₂(K) for
any local overcomponent J in either linear amalgam orientation. The affine
coordinates make this core elementary abelian, and characteristic two gives
a faithful action of J/O₂(J) on it, with the original conjugation equation.

At original exponent two the core has order sixteen. Its automorphism order
20160 excludes the triple cover of A₇, J₁, PSL₂(25), and all exceptional prime
PSL₂ rows. To apply the proved A₅ shortlist we construct the literal image
of K in J/O₂(J), its injective quotient map, its full Sylow normalization,
properness, and the containing quotient's SQTK and quasisimple hypotheses.
The only proper overcomponent quotient left is the actual A₇ carrier.

The original affine action also proves that the common core is an irreducible
J-module with zero fixed subgroup. It equals U(J), so the resulting J is an
exceptional A₇ block, including shortness and the cardinal of its literal
block module. Choosing a maximal overcomponent proves the complete 5.2.8
alternative for this row. The Chapter12 extension applies it to the actual pair.

Exhaustive F.1.12 comparison, the other 5.2.8 rows, and ambient recognition
remain open. This uses neither a universal A.3.12 premise nor a new module
classification premise, and asserts no ambient completion isomorphism.
Source: Aschbacher–Smith 5.2.8 and A.3.14(3), printed pp.652 and49–50
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem abelian_core_action (h : HasCharacteristicTwo G)
    [IsMulCommutative (pCore 2 G)] :
    ∃ f : (G ⧸ pCore 2 G) →* MulAut (pCore 2 G), Function.Injective f ∧
      ∀ (g : G) (x : pCore 2 G),
        (f (QuotientGroup.mk' (pCore 2 G) g) x : G) = g * (x : G) * g⁻¹ := by
  have hc : pCore 2 G ≤ centralizer (pCore 2 G : Set G) := by
    intro x hx
    exact mem_centralizer_iff.mpr (fun y hy => setLike_mul_comm hy hx)
  let f := MulAut.quotientConjNormal (pCore 2 G) (pCore 2 G) hc
  refine ⟨f, ?_, fun _ _ => rfl⟩
  apply (QuotientGroup.injective_lift_iff _ _ _).mpr
  rw [MulAut.conjNormal_ker_eq_centralizer]
  exact le_antisymm hc h

private def coreEquivOfAmbientEq {K J : Subgroup G}
    (hc : J.pCoreIn 2 = K.pCoreIn 2) : pCore 2 J ≃* pCore 2 K :=
  ((pCore 2 J).equivMapOfInjective J.subtype J.subtype_injective).trans
    ((MulEquiv.subgroupCongr hc).trans
      ((pCore 2 K).equivMapOfInjective K.subtype K.subtype_injective).symm)

private theorem linear_factor_affine
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)) :
    Nonempty (residual H ≃* Matrix.SL2.Affine F) := by
  rcases he with he | he <;> obtain ⟨e⟩ := he
  · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hTH hp F hm hF 1 false e.right).2.1
    exact ⟨a.trans (Matrix.PSL3.LinearThree.lineLocalEquivAffine F)⟩
  · obtain ⟨a⟩ := (BlockComparison.linear_parabolic_factor d h hTH hp F hm hF 1 true e.right).2.1
    exact ⟨a.trans (Matrix.PSL3.LinearThree.pointLocalEquivAffine F)⟩

private theorem affine_overcomponent_action {T : Sylow 2 G} {K J : Subgroup G}
    (hE : IsEvenCharacteristicAt T) (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hc : J.pCoreIn 2 = K.pCoreIn 2)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : K ≃* Matrix.SL2.Affine F) :
    IsElementaryAbelian 2 (pCore 2 J) ∧ Nat.card (pCore 2 J) = Nat.card F ^ 2 ∧
    ∃ f : (J ⧸ pCore 2 J) →* MulAut (pCore 2 J), Function.Injective f ∧
      ∀ (g : J) (x : pCore 2 J),
        (f (QuotientGroup.mk' (pCore 2 J) g) x : J) = g * (x : J) * g⁻¹ := by
  let a := (coreEquivOfAmbientEq hc).trans (ChapterC.SL2Affine.coreEquiv e).symm
  let : IsElementaryAbelian 2 (pCore 2 J) :=
    IsElementaryAbelian.of_injective a.toMonoidHom a.injective
  refine ⟨inferInstance, ?_, abelian_core_action
    (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T hE hJ)⟩
  rw [Nat.card_congr a.toEquiv]
  change Nat.card (Fin 2 → F) = _
  simp only [Nat.card_fun, Nat.card_fin]


/-- Every local overcomponent in either linear orientation acts faithfully
on its elementary two-core. The cardinal uses the original exponent, and
the quotient action retains literal conjugation on representatives. -/
theorem Preparation.linear_overcomponent_action
    {T : Sylow 2 G} {L W H A B J : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H ≤ J) :
    IsElementaryAbelian 2 (pCore 2 J) ∧ Nat.card (pCore 2 J) = 2^(2*n) ∧
    ∃ f : (J ⧸ pCore 2 J) →* MulAut (pCore 2 J), Function.Injective f ∧
      ∀ (g : J) (x : pCore 2 J),
        (f (QuotientGroup.mk' (pCore 2 J) g) x : J) = g * (x : J) * g⁻¹ := by
  have hc := (d.linear_overcomponent_core h hTH hp F hm hF he hJ hKJ).1
  obtain ⟨e⟩ := linear_factor_affine d h hTH hp F hm hF he
  obtain ⟨ha,hcard,hact⟩ := affine_overcomponent_action (h.qtke.evenCharacteristic T) hJ hc F e
  have hmn := (d.linear_amalgam_blocks h hTH hp F hm hF he).1
  refine ⟨ha,?_,hact⟩
  rw [hcard,hF,hmn,←pow_mul,Nat.mul_comm]

omit [Finite G] in
private theorem shortlist_of_card_dvd
    (hm : ChapterA.Section03.SourceEmbeddings.AlternatingFive.Shortlist G)
    (hd : Nat.card G ∣ 20160) :
    Nonempty (G ≃* alternatingGroup (Fin 7)) := by
  rcases hm with hm | hm | hm | hm | ⟨p,hp,hm⟩
  · exact hm
  · obtain ⟨_,⟨ez⟩,⟨eq⟩⟩ := hm
    have hz : Nat.card (center G) = 3 := by
      rw [Nat.card_congr ez.toEquiv]
      exact Nat.card_zmod 3
    have hq : Nat.card (G ⧸ center G) = 2520 := by
      rw [Nat.card_congr eq.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hc : Nat.card G = 7560 := by
      rw [← (center G).card_mul_index, (center G).index_eq_card,hz,hq]
    rw [hc] at hd
    norm_num at hd
  · obtain ⟨e⟩ := hm
    rw [Nat.card_congr e.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice
      (F := F) (hF ▸ (by decide : Odd 25))
    rw [hF,← Nat.card_congr e.toEquiv] at hc
    have he : Nat.card G = 7800 := by omega
    rw [he] at hd
    norm_num at hd
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    have hc := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF ▸ hp.2.1)
    rw [hF,← Nat.card_congr e.toEquiv] at hc
    have hd' : p ∣ 40320 := by
      have hh : 2 * Nat.card G ∣ 2 * 20160 := Nat.mul_dvd_mul_left 2 hd
      rw [Nat.mul_comm 2 (Nat.card G),hc] at hh
      exact (dvd_mul_right p (p^2-1)).trans hh
    have hps : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
      have hh : p ∣ 2^7 * 3^2 * 5 * 7 := hd'
      rcases hp.1.dvd_mul.mp hh with hh | hh
      · rcases hp.1.dvd_mul.mp hh with hh | hh
        · rcases hp.1.dvd_mul.mp hh with hh | hh
          · exact .inl ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp
              (hp.1.dvd_of_dvd_pow hh))
          · exact .inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_three).mp
              (hp.1.dvd_of_dvd_pow hh)))
        · exact .inr (.inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp hh)))
      · exact .inr (.inr (.inr ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp hh)))
    rcases hps with rfl | rfl | rfl | rfl <;>
      norm_num [Chapter1.Section02.A312ExceptionalPrime] at hp


open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
private theorem local_five_shortlist_of_core_eq
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKJ : K < J) (hc : J.pCoreIn 2 = K.pCoreIn 2)
    (hbinary : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^2))
    (efive : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5)) :
    AlternatingFive.Shortlist (J ⧸ pCore 2 J) := by
  let X := J ⊔ (T : Subgroup G)
  let JX := J.subgroupOf X
  let eJ : JX ≃* J := subgroupOfEquivOfLe le_sup_left
  let TX := T.subtype (show (T : Subgroup G) ≤ X from le_sup_right)
  obtain ⟨P,hP⟩ := TX.exists_subgroupOf_eq_of_subnormal JX hJ.1.subnormal
  let S := P.mapSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hSJ : (S : Subgroup J) ≤ (T : Subgroup G).subgroupOf J := by
    change (P : Subgroup JX).map eJ.toMonoidHom ≤ _
    rw [hP]
    rintro y ⟨x,hx,rfl⟩
    exact hx
  have hSK : (S : Subgroup J) ≤ normalizer (K.subgroupOf J : Set J) := by
    rw [← subgroupOf_normalizer_eq hKJ.le]
    exact hSJ.trans (comap_mono hTK)
  let q := QuotientGroup.mk' (pCore 2 J)
  let f := q.comp (inclusion hKJ.le)
  let B := f.range
  have hBmap : B = (K.subgroupOf J).map q := by
    change (q.comp (inclusion hKJ.le)).range = _
    rw [MonoidHom.range_comp,inclusion_range]
  have hker : f.ker = pCore 2 K := by
    ext x
    change (QuotientGroup.mk (inclusion hKJ.le x) : J ⧸ pCore 2 J) = 1 ↔ x ∈ pCore 2 K
    rw [QuotientGroup.eq_one_iff,←mem_map_iff_mem J.subtype_injective,
      ←mem_map_iff_mem K.subtype_injective]
    change (x : G) ∈ J.pCoreIn 2 ↔ (x : G) ∈ K.pCoreIn 2
    rw [hc]
  let eB : B ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans efive)
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : Group.IsPerfect (alternatingGroup (Fin 5)) := inferInstance
  let : IsSimpleGroup B := eB.isSimpleGroup
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hn : (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (B : Set _) := by
    rw [hBmap]
    exact (map_mono hSK).trans (le_normalizer_map q)
  have hb : B ∈ localCComponents Sb := by
    let e := subgroupOfEquivOfLe (show B ≤ B ⊔ (Sb : Subgroup _) from le_sup_left)
    let : IsSimpleGroup (B.subgroupOf (B ⊔ (Sb : Subgroup _))) := e.isSimpleGroup
    let : Group.IsPerfect (B.subgroupOf (B ⊔ (Sb : Subgroup _))) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hn' : (B.subgroupOf (B ⊔ (Sb : Subgroup _))).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hn)
    exact isCComponent_of_isSimpleGroup_of_isPerfect hn'.isSubnormal
  have hne : B ≠ ⊤ := by
    intro ht
    have hQK : pCore 2 J ≤ K.subgroupOf J := by
      intro x hx
      have hx' : (x : G) ∈ J.pCoreIn 2 := mem_map_of_mem J.subtype hx
      rw [hc] at hx'
      exact map_subtype_le (pCore 2 K) hx'
    have hh : K.subgroupOf J = ⊤ := by
      have he := congrArg (Subgroup.comap q) ht
      rw [hBmap,comap_map_eq,QuotientGroup.ker_mk',sup_eq_left.mpr hQK,comap_top] at he
      exact he
    exact hKJ.ne (le_antisymm hKJ.le (subgroupOf_eq_top.mp hh))
  let qX := QuotientGroup.mk' (pCore 2 X)
  have hsq := Chapter1.Section02.uniqueness_local_quotient_sqtk hG hJ.2.2
  let eqJ : JX.map qX ≃* (J ⧸ pCore 2 J) :=
    (cComponentTwoCoreQuotientEquiv hJ.1).symm.trans
      (QuotientGroup.congr _ _ eJ (pCore_map_iso 2 eJ))
  have hsqJ : IsSQTK KnownSimple.IsKnownSimple (J ⧸ pCore 2 J) :=
    (IsSQTK.equiv eqJ).mp (hsq.subgroup _)
  have htop : (⊤ : Subgroup (J ⧸ pCore 2 J)).IsCComponent := by
    let := pCore_isNilpotent (p := 2) (G := X)
    have hh : (⊤ : Subgroup (JX.map qX)).IsCComponent := by
      simpa only [subgroupOf_self] using (hJ.1.map_quotient (pCore 2 X)).subgroupOf le_rfl
    simpa only [map_top_of_surjective eqJ.toMonoidHom eqJ.surjective] using hh.map_equiv eqJ
  have hbin : ClassicalGroup.IsPSL B 2 (2^2) := by
    obtain ⟨F,_,_,hF,⟨e⟩⟩ :=
      hbinary
    exact ⟨F,inferInstance,inferInstance,hF,⟨eB.trans (efive.symm.trans e)⟩⟩
  have hq := binary_containing_component_quasisimple hsqJ (pCore_quotient_pCore_eq_bot 2)
    htop (show B ≤ ⊤ from le_top) (by decide : 1 < 2) hbin
  let : IsQuasisimple (⊤ : Subgroup (J ⧸ pCore 2 J)) := hq
  let : IsQuasisimple (J ⧸ pCore 2 J) := IsQuasisimple.of_mulEquiv topEquiv
  exact AlternatingFive.shortlist_knownSimple hsqJ (pCore_quotient_pCore_eq_bot 2) Sb hb hn eB hne

private theorem affine_overcomponent_short
    {T : Sylow 2 G} {K J : Subgroup G}
    (hE : IsEvenCharacteristicAt T) (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : K ≤ J) (hc : J.pCoreIn 2 = K.pCoreIn 2)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    (e : K ≃* Matrix.SL2.Affine F) (hq : IsQuasisimple (J ⧸ pCore 2 J)) :
    ChapterC.IsShort J ∧ ChapterC.blockU J = pCore 2 J ∧
      ChapterC.blockFixed J = ⊥ := by
  let i := inclusion hKJ
  have hm : (pCore 2 K).map i = pCore 2 J := by
    apply map_injective J.subtype_injective
    rw [map_map]
    exact hc.symm
  have hpre : (pCore 2 J).comap i = pCore 2 K := by
    rw [←hm,comap_map_eq, (MonoidHom.ker_eq_bot_iff i).mpr (inclusion_injective hKJ),sup_bot_eq]
  have hd (N : Subgroup J) (hn : N.Normal) (hle : N ≤ pCore 2 J) :
      N = ⊥ ∨ N = pCore 2 J := by
    let := hn
    have hle' : N.comap i ≤ pCore 2 K := hpre ▸ comap_mono hle
    have hNi : N ≤ i.range := hle.trans (hm ▸ map_le_range i (pCore 2 K))
    rcases ChapterC.SL2Affine.normal_core_dichotomy e (N.comap i) hle' with hz | he
    · left
      have hh := congrArg (map i) hz
      simpa only [map_comap_eq_self hNi,Subgroup.map_bot] using hh
    · right
      have hh := congrArg (map i) he
      simpa only [map_comap_eq_self hNi,hm] using hh
  have hnot : ¬ pCore 2 J ≤ center J := by
    intro hh
    apply ChapterC.SL2Affine.core_not_le_center e
    intro x hx
    apply mem_center_iff.mpr
    intro y
    apply (inclusion_injective hKJ)
    simpa only [map_mul] using mem_center_iff.mp
      (hh (hm ▸ mem_map_of_mem i hx)) (i y)
  have hcenter : pCore 2 J ⊓ center J = ⊥ := by
    rcases hd (pCore 2 J ⊓ center J) inferInstance inf_le_left with hh | hh
    · exact hh
    · exact (hnot (hh ▸ inf_le_right)).elim
  have hu : ChapterC.blockU J = pCore 2 J := by
    rcases hd (ChapterC.blockU J) inferInstance ChapterC.blockU_le_core with hh | hh
    · exact (hnot ((commutator_top_right_eq_bot_iff_le_center).mp hh)).elim
    · exact hh
  have hfix : ChapterC.blockFixed J = ⊥ := by
    apply map_injective (ChapterC.blockU J).subtype_injective
    rw [ChapterC.blockFixed_map,hu,hcenter,Subgroup.map_bot]
  obtain ⟨ha,_,_⟩ := affine_overcomponent_action hE hJ hc F e
  let := ha
  let := Chapter1.mem_L_isPerfect hJ
  refine ⟨⟨inferInstance,Chapter1.Section02.Adequate.mem_L_isPPerfect hJ,
    generalizedFitting_eq_pCore_of_selfCentralizing 2
      (Chapter1.Section02.Adequate.mem_L_hasCharacteristicTwo T hE hJ),
    hu ▸ ha,?_,.inl hq,?_⟩,hu,hfix⟩
  · rw [hu]
    intro x hx
    exact mem_centralizer_iff.mpr (fun y hy => setLike_mul_comm hy hx)
  · constructor
    · rw [hu,hcenter,bot_lt_iff_ne_bot]
      intro hz
      exact hnot (hz ▸ bot_le)
    · intro N hn _ hle
      rw [hu] at hle ⊢
      rw [hcenter]
      exact hd N hn hle


private theorem alternating_quasisimple {X : Type*} [Group X] {k : ℕ}
    (hk : 5 ≤ k) (e : X ≃* alternatingGroup (Fin k)) : IsQuasisimple X := by
  let : IsSimpleGroup (alternatingGroup (Fin k)) := alternatingGroup.isSimpleGroup (by simpa using hk)
  let : Group.IsPerfect (alternatingGroup (Fin k)) := ⟨commutator_alternatingGroup_eq_top (by simpa using hk)⟩
  let : IsSimpleGroup X := e.isSimpleGroup
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hz : center X = ⊥ :=
    (inferInstance : (center X).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp ht))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩

/-- At original exponent two, every proper local overcomponent in the
linear row is an exceptional A₇ block, including its actual block module. -/
theorem Preparation.linear_four_overcomponent_exceptional
    {T : Sylow 2 G} {L W H A B J : Subgroup G}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hKJ : residual H < J) :
    ChapterC.IsExceptionalA7Block J := by
  have hc := (d.linear_overcomponent_core h hTH hp F hm hF he hJ hKJ.le).1
  obtain ⟨ha,hcard,f,hf,_⟩ := d.linear_overcomponent_action h hTH hp F hm hF he hJ hKJ.le
  let := ha
  have hdiv : Nat.card (J ⧸ pCore 2 J) ∣ 20160 := by
    have hh := card_dvd_of_injective f hf
    rw [SmallNonabelianTwoGroup.card_mulAut_elementary_two_pow _ 4 hcard] at hh
    norm_num [Fin.prod_univ_succ] at hh ⊢
    exact hh
  obtain ⟨_,_,hblock⟩ := d.linear_amalgam_blocks h hTH hp F hm hF he
  obtain ⟨_,_,_,_,_,_,hbinary,_⟩ := hblock
  have hfive : Nonempty ((residual H ⧸ pCore 2 (residual H)) ≃* alternatingGroup (Fin 5)) := by
    obtain ⟨E,_,_,hE,⟨e⟩⟩ := hbinary
    obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE
    exact ⟨e.trans a⟩
  have hlist := local_five_shortlist_of_core_eq h.qtke hJ
    (hTH.trans (le_normalizer_residual H)) hKJ hc hbinary hfive.some
  obtain ⟨eJ⟩ := shortlist_of_card_dvd hlist hdiv
  obtain ⟨e⟩ := linear_factor_affine d h hTH hp F hm hF he
  obtain ⟨hshort,hU,hfix⟩ := affine_overcomponent_short (h.qtke.evenCharacteristic T)
    hJ hKJ.le hc F e (alternating_quasisimple (by decide) eJ)
  refine ⟨hshort,⟨eJ⟩,?_⟩
  rw [ChapterC.BlockModule,hfix,Nat.card_congr (QuotientGroup.quotientBot
    (G := ChapterC.blockU J)).toEquiv,hU]
  exact hcard

private theorem residual_mem_local_of_quasisimple
    {T : Sylow 2 G} {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hq : IsQuasisimple (residual H ⧸ pCore 2 (residual H))) :
    residual H ∈ Chapter1.L G (T : Subgroup G) := by
  let := hq
  have hTH : (T : Subgroup G) ≤ H := hH.2
  have hRH : residual H ≤ H := map_subtype_le _
  let e := (subgroupOfEquivOfLe hRH).symm
  let q := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let : IsQuasisimple (((residual H).subgroupOf H) ⧸ pCore 2 ((residual H).subgroupOf H)) :=
    IsQuasisimple.of_mulEquiv q
  have hn : ((residual H).subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_residual H)
  have hc := isCComponent_of_isPPerfect_of_quasisimple_core_quotient hn.isSubnormal
    ((isPPerfect_embedded_pResidual 2 H).of_surjective e.toMonoidHom e.surjective)
  change ((residual H).subgroupOf (residual H ⊔ (T : Subgroup G))).IsCComponent ∧ _
  rw [residual_sup_sylow T H hTH]
  refine ⟨hc,⟨T.subtype hTH,?_⟩,hH.1⟩
  simp only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH]

/-- The complete 5.2.8 alternative for the L₃(4) row, in both orientations.
The maximal exceptional overcomponent is constructed in the original group. -/
theorem Preparation.linear_four_maximal_or_exceptional
    {T : Sylow 2 G} {L W H A B : Subgroup G}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W 2)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)) :
    m = 2 ∧ (residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
        residual H < J ∧ ChapterC.IsExceptionalA7Block J) := by
  have hTH := hH.1.1.2
  refine ⟨(d.linear_amalgam_blocks h hTH hp F hm hF he).1,?_⟩
  by_cases hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G)
  · exact .inl hmax
  right
  obtain ⟨_,_,hblock⟩ := d.linear_amalgam_blocks h hTH hp F hm hF he
  obtain ⟨_,_,_,_,_,_,hbinary,_⟩ := hblock
  obtain ⟨E,_,_,hE,⟨e⟩⟩ := hbinary
  obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hE
  have hl := residual_mem_local_of_quasisimple hH.1.1
    (alternating_quasisimple (by decide) (e.trans a))
  obtain ⟨J,hJ,hKJ⟩ := Chapter1.exists_mem_LStar_ge hl
  have hlt : residual H < J := lt_of_le_of_ne hKJ (fun he => hmax (he ▸ hJ))
  exact ⟨J,hJ,hlt,d.linear_four_overcomponent_exceptional h hTH hp F hm hF he hJ.1 hlt⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
