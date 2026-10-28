module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearFourMaximal
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalSylow
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizer
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.LargerSource.BinaryKnownSimple

/-!
# Right maximality for the linear and symplectic block rows

The preceding core comparison identifies O₂(J) with O₂(K) for every
local overcomponent J of K = O²(H). The literal image of K in J/O₂(J)
is therefore its original PSL₂ quotient. A full Sylow of J normalizes this
image: it is obtained by restricting the ambient T through J subnormal in JT.
The known-simple binary embedding theorem now forces the original exponent
to be two whenever K < J, and supplies the five actual quotient models.

Consequently K is maximal in L(G,T) in both block rows when n ≠ 2.
Combining this with the checked field-four argument proves the entire
linear-row maximality-or-exceptional-A₇ alternative. The normalizer application
also discharges the common-Sylow and enlarged-core premises using the same
compatible comparison. The Chapter12 extension uses the actual source pair.

The symplectic field-four and nonblock rows, exhaustive F.1.12 comparison,
original uniqueness and ambient completion recognition remain separate
obligations. No ambient completion isomorphism follows from these local data.
Source: Aschbacher–Smith 5.2.8 and A.3.12–14, printed pp.652–653 and47–50
(`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open ChapterC.Section05.NormalizerControl.EmbeddingSelection
variable {G : Type*} [Group G] [Finite G]

private theorem simple_perfect_quasisimple {X : Type*} [Group X]
    [IsSimpleGroup X] [Group.IsPerfect X] : IsQuasisimple X := by
  have hz : center X = ⊥ :=
    (inferInstance : (center X).Normal).eq_bot_or_eq_top.resolve_right
      (fun ht => Group.IsPerfect.not_isMulCommutative X (center_eq_top_iff.mp ht))
  exact ⟨((QuotientGroup.quotientMulEquivOfEq hz).trans QuotientGroup.quotientBot).isSimpleGroup⟩

private theorem local_binary_parameter_of_core_eq
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKJ : K < J) (hc : J.pCoreIn 2 = K.pCoreIn 2)
    {n : ℕ} (hn : 1 < n) (hpK : Group.IsPerfect K)
    (hbinary : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n)) :
    n = 2 ∧ AlternatingFive.Shortlist (J ⧸ pCore 2 J) := by
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
  let eB : B ≃* (K ⧸ pCore 2 K) :=
    (QuotientGroup.quotientKerEquivRange f).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hker)
  let := hpK
  let : IsSimpleGroup (K ⧸ pCore 2 K) := binary_simple hn hbinary
  let : IsSimpleGroup B := eB.isSimpleGroup
  let : Group.IsPerfect B := Group.IsPerfect.ofSurjective (f := eB.symm.toMonoidHom) eB.symm.surjective
  let : IsQuasisimple B := simple_perfect_quasisimple
  let Sb := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 J))
  have hnorm : (Sb : Subgroup (J ⧸ pCore 2 J)) ≤ normalizer (B : Set _) := by
    rw [hBmap]
    exact (map_mono hSK).trans (le_normalizer_map q)
  have hb : B ∈ localCComponents Sb := by
    let e := subgroupOfEquivOfLe (show B ≤ B ⊔ (Sb : Subgroup _) from le_sup_left)
    let : IsSimpleGroup (B.subgroupOf (B ⊔ (Sb : Subgroup _))) := e.isSimpleGroup
    let : Group.IsPerfect (B.subgroupOf (B ⊔ (Sb : Subgroup _))) :=
      Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hn' : (B.subgroupOf (B ⊔ (Sb : Subgroup _))).Normal :=
      normal_subgroupOf_of_le_normalizer (sup_le B.le_normalizer hnorm)
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
  have hbin : ClassicalGroup.IsPSL B 2 (2^n) := hbinary.of_mulEquiv eB
  rcases binary_larger_selection_knownSimple hsqJ (pCore_quotient_pCore_eq_bot 2)
      Sb hb htop (show B ≤ ⊤ from le_top) hnorm hn hbin with he | ⟨hn2,hm⟩
  · exact (hne he).elim
  · exact ⟨hn2, AlternatingFive.Shortlist.of_equiv hm
      (topEquiv (G := J ⧸ pCore 2 J)).symm⟩

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

/-- The actual inclusion in a local overcomponent with the same two-core
forces exponent two and the precise A.3.14 quotient shortlist. This also
applies to the different right exponent in a unitary comparison. -/
theorem local_binary_overcomponent_of_core_eq
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {K J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hKJ : K < J) (hc : J.pCoreIn 2 = K.pCoreIn 2)
    {n : ℕ} (hn : 1 < n) (hpK : Group.IsPerfect K)
    (hbinary : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2^n)) :
    n = 2 ∧ AlternatingFive.Shortlist (J ⧸ pCore 2 J) :=
  local_binary_parameter_of_core_eq hG hJ hTK hKJ hc hn hpK hbinary

/-- A perfect binary residual of a Sylow-containing local group belongs
to the actual local-component family, before its maximality is known. -/
theorem residual_binary_mem_local
    {T : Sylow 2 G} {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hp : Group.IsPerfect (residual H))
    {f : ℕ} (hf : 1 < f)
    (hb : ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^f)) :
    residual H ∈ Chapter1.L G (T : Subgroup G) := by
  let := hp
  let : IsSimpleGroup (residual H ⧸ pCore 2 (residual H)) := binary_simple hf hb
  exact residual_mem_local_of_quasisimple hH
    (simple_perfect_quasisimple (X := residual H ⧸ pCore 2 (residual H)))

/-- A normalized binary residual away from PSL₂(4) is maximal when every
local overcomponent has the same core. This also applies when its binary
exponent differs from that of the original left factor, as in triality. -/
theorem residual_binary_maximal_of_overcomponent_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    {T : Sylow 2 G} {H : Subgroup G}
    (hH : H ∈ Chapter1.HOver G (T : Set G))
    (hp : Group.IsPerfect (residual H))
    {f : ℕ} (hf : 1 < f) (hf2 : f ≠ 2)
    (hbinary : ClassicalGroup.IsPSL (residual H ⧸ pCore 2 (residual H)) 2 (2^f))
    (hc : ∀ J ∈ Chapter1.L G (T : Subgroup G), residual H ≤ J →
      J.pCoreIn 2 = (residual H).pCoreIn 2) :
    residual H ∈ Chapter1.LStar G (T : Subgroup G) := by
  let := hp
  let : IsSimpleGroup (residual H ⧸ pCore 2 (residual H)) := binary_simple hf hbinary
  have hmem := residual_mem_local_of_quasisimple hH
    (simple_perfect_quasisimple (X := residual H ⧸ pCore 2 (residual H)))
  refine ⟨hmem,?_⟩
  intro J hJ hKJ
  by_contra hne
  exact hf2 (local_binary_parameter_of_core_eq hG hJ
    (hH.2.trans (le_normalizer_residual H))
    (lt_of_le_of_ne hKJ (Ne.symm hne)) (hc J hJ hKJ) hf hp hbinary).1

/-- A proper overcomponent in either block row forces the original exponent
to be two and gives the actual A.3.14 quotient models. -/
theorem Preparation.block_overcomponent_parameter
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hTH : (T : Subgroup G) ≤ H) (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he :
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)))
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hKJ : residual H < J) :
    n = 2 ∧ AlternatingFive.Shortlist (J ⧸ pCore 2 J) := by
  obtain ⟨hc,_,hbinary,_⟩ := d.block_overcomponent_quotient h hTH hp F hm hF he hJ hKJ.le
  exact local_binary_parameter_of_core_eq h.qtke hJ
    (hTH.trans (le_normalizer_residual H)) hKJ hc h.exponent hp hbinary

/-- Away from original exponent two, both linear and symplectic rows have
maximal right factor. No right-maximality or embedding-list premise is assumed. -/
theorem Preparation.block_right_maximal_of_exponent_ne_two
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (hn : n ≠ 2)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he :
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)))
    : residual H ∈ Chapter1.LStar G (T : Subgroup G) := by
  have hTH := hH.1.1.2
  have hb : ChapterC.IsL2EvenBlock (residual H) n := by
    rcases he with he | he
    · exact (d.linear_amalgam_blocks h hTH hp F hm hF he).2.2
    · exact (d.symplectic_amalgam_blocks h hTH hp F hm hF he).2.2
  obtain ⟨_,_,_,_,_,_,hbinary,_⟩ := hb
  let := hp
  let : IsSimpleGroup (residual H ⧸ pCore 2 (residual H)) := binary_simple h.exponent hbinary
  have hmem := residual_mem_local_of_quasisimple hH.1.1
    (simple_perfect_quasisimple (X := residual H ⧸ pCore 2 (residual H)))
  refine ⟨hmem,?_⟩
  intro J hJ hKJ
  by_contra hne
  exact hn (d.block_overcomponent_parameter h hTH hp F hm hF he hJ
    (lt_of_le_of_ne hKJ (Ne.symm hne))).1

/-- The complete linear-row alternative of 5.2.8 at every original exponent,
including the exceptional maximal A₇ block at field order four. -/
theorem Preparation.linear_maximal_or_exceptional
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he :
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))) :
    m = n ∧ (residual H ∈ Chapter1.LStar G (T : Subgroup G) ∨
      n = 2 ∧ ∃ J ∈ Chapter1.LStar G (T : Subgroup G),
        residual H < J ∧ ChapterC.IsExceptionalA7Block J) := by
  refine ⟨(d.linear_amalgam_blocks h hH.1.1.2 hp F hm hF he).1,?_⟩
  by_cases hn : n = 2
  · subst n
    rcases (d.linear_four_maximal_or_exceptional h hH hp F hm hF he).2 with hh | hh
    · exact .inl hh
    · exact .inr ⟨rfl,hh⟩
  · exact .inl (d.block_right_maximal_of_exponent_ne_two h hH hp hn F hm hF (.inl he))

/-- For either block row away from exponent two, the actual ambient
normalizer pair satisfies the source local conditions with right maximality,
the common Sylow and both enlarged cores all discharged. -/
theorem Preparation.block_normalizer_local_conditions
    {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H)) (hn : n ≠ 2)
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he :
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse)) ∨
      (Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F)) ∨
       Nonempty (RankTwoAmalgam.Iso
        (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
        (ChapterF.GreenBook.LieModels.SymplecticFour.amalgam F).reverse)))
    : Chapter5.Section03GreenExtension.SourceLocalConditions
      (normalizerAmalgam L (residual H)) L (residual H) ((T : Subgroup G) ⊓ L) := by
  have hmax := d.block_right_maximal_of_exponent_ne_two h hH hp hn F hm hF he
  have hc : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := by
    rcases he with he | he
    · exact .linear F m hm hF he
    · exact .symplectic F m hm hF he
  exact d.normalizer_local_conditions h hH hmax rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hc)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hc)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
