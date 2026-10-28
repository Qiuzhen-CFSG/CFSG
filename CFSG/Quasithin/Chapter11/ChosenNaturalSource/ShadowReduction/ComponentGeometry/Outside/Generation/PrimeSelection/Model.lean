module
public import Theory.SpecificGroups.PSL2.PrimeInvolutionCentralizerMaximal
public import Theory.SpecificGroups.PSL2.InvolutionCentralizerSolvable
public import Theory.SpecificGroups.PSL2.PrimeNonsolvableSubgroups
public import Theory.SpecificGroups.PSL2.PGL2SylowNormalizedFive
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLTwoGeneration.PrimeGeometry.LinearModels
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.GeneralizedFitting.SimpleTwoQuotient
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.SolvableRadical.SolvableKernel
public import Theory.GroupTheory.PResidual.NormalSubgroup

/-!
# Solvable Sylow overgroups escaping the marked A₅ normalizer

In prime PSL₂(p), p ≥ 11, a Sylow-normalized A₅ contains the Sylow
subgroup. A central involution therefore has a centralizer containing
that Sylow. This centralizer is solvable and maximal, so it cannot lie
in the proper nonsolvable A₅ normalizer. The prime PGL₂ model is excluded
by its actual Sylow-normalized A₅ calculation.

The final theorem lifts this solvable overgroup through the full two-core.
It identifies the seed image using the literal restricted quotient map;
neither splitting nor uniqueness of A₅ Sylow overgroups is assumed.
PrimeSelection applies this construction to the original KT and L₁.
Source: Dickson's theorem, Huppert II.8.27; Aschbacher--Smith E.1.14(6)
and the H choice in 11.4--11.5, printed pp.214,778--779 of refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeSelection

private theorem alternating_five_nonsolvable {A : Type*} [Group A]
    (e : A ≃* alternatingGroup (Fin 5)) : ¬ Group.IsSolvable A := by
  intro hs
  let := hs
  let : Group.IsSolvable (alternatingGroup (Fin 5)) :=
    Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  let : Group.IsPerfect (alternatingGroup (Fin 5)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 5)) inferInstance

/-- A full Sylow subgroup normalizing A₅ in prime PSL₂ has a solvable
overgroup which does not normalize that same A₅. -/
theorem prime_solvable_escape
    {F : Type*} [Field F] [Finite F] {p : ℕ} [Fact p.Prime]
    (ho : Odd p) (hF : Nat.card F = p) (hp : 9 < p)
    (S : Sylow 2 (GorensteinWalter.PSL2 F)) (A : Subgroup (GorensteinWalter.PSL2 F))
    (eA : A ≃* alternatingGroup (Fin 5))
    (hSA : (S : Subgroup _) ≤ normalizer (A : Set (GorensteinWalter.PSL2 F))) :
    ∃ C : Subgroup (GorensteinWalter.PSL2 F), (S : Subgroup _) ≤ C ∧
      Group.IsSolvable C ∧ ¬ C ≤ normalizer (A : Set (GorensteinWalter.PSL2 F)) := by
  let : IsSimpleGroup (GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  have hAne : A ≠ ⊥ := by
    intro he
    have hc : Nat.card A = 60 := by
      rw [Nat.card_congr eA.toEquiv,nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    norm_num [he] at hc
  have hAt : A ≠ ⊤ := by
    intro he
    have hc : Nat.card (GorensteinWalter.PSL2 F) = 60 := by
      rw [← card_top (G := GorensteinWalter.PSL2 F),←he,Nat.card_congr eA.toEquiv,
        nat_card_alternatingGroup]
      norm_num [Nat.factorial]
    have hh := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := F) (hF.symm ▸ ho)
    rw [hF,hc] at hh
    have hl : 99 ≤ p ^ 2 - 1 := by
      have : 100 ≤ p ^ 2 := by nlinarith
      omega
    nlinarith
  have hNt : normalizer (A : Set (GorensteinWalter.PSL2 F)) ≠ ⊤ := by
    intro he
    let : A.Normal := normalizer_eq_top_iff.mp he
    exact ((inferInstance : A.Normal).eq_bot_or_eq_top).elim hAne hAt
  have hNns : ¬ Group.IsSolvable (normalizer (A : Set (GorensteinWalter.PSL2 F))) := by
    intro hs
    let := hs
    exact alternating_five_nonsolvable eA
      (Group.isSolvable_of_isSolvable_injective (inclusion_injective A.le_normalizer))
  obtain ⟨_,_,⟨eN⟩⟩ := Theory.PSL2.prime_nonsolvable_proper_is_alternating_five
    ho hF (normalizer (A : Set (GorensteinWalter.PSL2 F))) hNt hNns
  have hAN : A = normalizer (A : Set (GorensteinWalter.PSL2 F)) :=
    eq_of_le_of_card_ge A.le_normalizer (by rw [Nat.card_congr eA.toEquiv,
      Nat.card_congr eN.toEquiv])
  have hSle : (S : Subgroup _) ≤ A := hSA.trans_eq hAN.symm
  let SA := S.subtype hSle
  let S5 := SA.mapSurjective (f := eA.toMonoidHom) eA.surjective
  have h4 : Nat.card S = 4 := by
    calc
      Nat.card S = Nat.card SA := (Nat.card_congr (subgroupOfEquivOfLe hSle).toEquiv).symm
      _ = Nat.card S5 := Nat.card_congr
        ((SA : Subgroup A).equivMapOfInjective eA.toMonoidHom eA.injective).toEquiv
      _ = 4 := Theory.PSL2.SylowFixedQuotients.alternating_sylow_card S5
  have hcomm : IsMulCommutative S := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) h4
  let := hcomm
  obtain ⟨t,ht⟩ := exists_prime_orderOf_dvd_card' (G := S) 2 (show 2 ∣ Nat.card S by rw [h4]; decide)
  have hto : orderOf (t : GorensteinWalter.PSL2 F) = 2 :=
    (orderOf_injective (S : Subgroup (GorensteinWalter.PSL2 F)).subtype (S : Subgroup (GorensteinWalter.PSL2 F)).subtype_injective t).trans ht
  have hti : GorensteinWalter.IsInvolution (t : GorensteinWalter.PSL2 F) :=
    (orderOf_eq_prime_iff.mp hto).symm
  let C := centralizer ({(t : GorensteinWalter.PSL2 F)} : Set _)
  have hSC : (S : Subgroup _) ≤ C := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm (⟨s,hs⟩ : S) t))
  have hCs : Group.IsSolvable C := Theory.PSL2.involution_centralizer_isSolvable
    ⟨p,1,Fact.out,ho,by decide,by simpa using hF⟩ t hti
  refine ⟨C,hSC,hCs,?_⟩
  intro hCN
  have hmax := Theory.PSL2.prime_involution_centralizer_isCoatom_of_nine_lt ho hF hp t hti
  have he : normalizer (A : Set (GorensteinWalter.PSL2 F)) = C := le_antisymm
    ((isCoatom_iff_ge_of_le.mp hmax).2 _ hNt hCN) hCN
  exact hNns (he.symm ▸ hCs)

/-- The same construction in a two-reduced group with a normal prime PSL₂
socle. An actual Sylow-normalized A₅ excludes the diagonal PGL₂ model. -/
theorem normal_prime_solvable_escape
    {J : Type*} [Group J] [Finite J]
    (K : Subgroup J) [K.Normal] (hC : centralizer (K : Set J) = ⊥)
    {p : ℕ} (hp : p.Prime) (hbig : 9 < p)
    (hm : ClassicalGroup.IsPSL K 2 p)
    (S : Sylow 2 J) (A : Subgroup J) (eA : A ≃* alternatingGroup (Fin 5))
    (hSA : (S : Subgroup J) ≤ normalizer (A : Set J)) :
    ∃ C : Subgroup J, (S : Subgroup J) ≤ C ∧ Group.IsSolvable C ∧
      ¬ C ≤ normalizer (A : Set J) := by
  obtain ⟨F,_,_,hF,⟨eK⟩⟩ := hm
  have ho : Odd p := hp.odd_of_ne_two (by omega)
  let : Fact p.Prime := ⟨hp⟩
  have he := ChapterE.ValuesOdd.PSLTwoGeneration.PrimeGeometry.linear_models_of_normal_prime_psl
    K hp ho hF (by omega) eK hC
  rcases he with he | he
  · obtain ⟨e⟩ := he
    let A' := A.map e.toMonoidHom
    let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
    let eA' : A' ≃* alternatingGroup (Fin 5) :=
      (A.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eA
    have hn : (S' : Subgroup (GorensteinWalter.PSL2 F)) ≤ normalizer (A' : Set (GorensteinWalter.PSL2 F)) :=
      (map_mono hSA).trans (A.le_normalizer_map e.toMonoidHom)
    obtain ⟨C,hSC,hCs,hCn⟩ := prime_solvable_escape ho hF hbig S' A' eA' hn
    let C' := C.comap e.toMonoidHom
    have hCs' : Group.IsSolvable C' := by
      let := hCs
      exact Group.isSolvable_of_isSolvable_injective
        (f := e.toMonoidHom.subgroupComap C) (by
          intro x y hh
          exact Subtype.ext (e.injective (congrArg Subtype.val hh)))
    refine ⟨C',?_,hCs',?_⟩
    · exact map_le_iff_le_comap.mp hSC
    · intro hh
      apply hCn
      have hmap := (map_mono (f := e.toMonoidHom) hh).trans (A.le_normalizer_map e.toMonoidHom)
      rwa [map_comap_eq_self_of_surjective e.surjective] at hmap
  · obtain ⟨e⟩ := he
    let A' := A.map e.toMonoidHom
    let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
    have hfive := Theory.PSL2.pgl2_prime_eq_five_of_sylow_normalizes_alternating_five
      ho hF S' A' ⟨(A.equivMapOfInjective e.toMonoidHom e.injective).symm.trans eA⟩
      ((map_mono hSA).trans (A.le_normalizer_map e.toMonoidHom))
    omega

/-- Lift the actual solvable Sylow overgroup through the full two-core.
The seed's two-core is retained in the kernel, so its image is the specified A₅. -/
theorem solvable_escape_above_twoCore
    {J : Type*} [Group J] [Finite J]
    (K : Subgroup J) [K.Normal] [Group.IsPerfect K]
    {p : ℕ} (hp : p.Prime) (hbig : 9 < p)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 p)
    (S : Sylow 2 J) (hgen : K ⊔ (S : Subgroup J) = ⊤)
    (A : Subgroup J) (eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (hAcore : A.pCoreIn 2 ≤ pCore 2 J)
    (hSA : (S : Subgroup J) ≤ normalizer (A : Set J)) :
    ∃ C : Subgroup J, (S : Subgroup J) ≤ C ∧ Group.IsSolvable C ∧
      ¬ C ≤ normalizer (A : Set J) := by
  let q := QuotientGroup.mk' (pCore 2 J)
  let K' := K.map q
  let A' := A.map q
  let S' := S.mapSurjective (f := q) (QuotientGroup.mk'_surjective _)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  let : K'.Normal := (inferInstance : K.Normal).map q hq
  let : Group.IsPerfect K' := Group.IsPerfect.map q
  obtain ⟨F,_,_,hF,⟨eK⟩⟩ := hm
  let eK' : K' ≃* GorensteinWalter.PSL2 F := (coreQuotientEquivImage 2 K).symm.trans eK
  let : IsSimpleGroup (GorensteinWalter.PSL2 F) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup K' := eK'.isSimpleGroup
  have hnon : ¬ IsMulCommutative K' := by
    intro hh
    let := hh
    exact Group.IsPerfect.not_isSolvable K' inferInstance
  have hgen' : K' ⊔ (S' : Subgroup _) = ⊤ := by
    change K.map q ⊔ (S : Subgroup J).map q = ⊤
    rw [←Subgroup.map_sup,hgen,map_top_of_surjective q hq]
  have hquot := isPGroup_quotient_of_sup_eq_top K' S' S'.isPGroup' hgen'
  have hcentral := (simple_two_quotient_structure K' hnon hquot
    (pCore_quotient_pCore_eq_bot 2)).2.1
  have hkA : (q.subgroupMap A).ker = pCore 2 A := by
    apply le_antisymm
    · apply le_sSup
      refine ⟨inferInstance,?_⟩
      rw [ker_subgroupMap,QuotientGroup.ker_mk']
      exact pCore_isPGroup.comap_subtype
    · intro a ha
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff a.val).mpr
        (hAcore (mem_map_of_mem A.subtype ha))
  let eA' : A' ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.liftEquiv (pCore 2 A) (q.subgroupMap_surjective A) hkA.symm).symm.trans eA
  obtain ⟨C,hSC,hCs,hCn⟩ := normal_prime_solvable_escape K' hcentral hp hbig
    ⟨F,inferInstance,inferInstance,hF,⟨eK'⟩⟩ S' A' eA'
    ((map_mono hSA).trans (A.le_normalizer_map q))
  let : Group.IsNilpotent q.ker := by
    rw [show q.ker = pCore 2 J from QuotientGroup.ker_mk' _]
    exact pCore_isPGroup.isNilpotent
  let := hCs
  refine ⟨C.comap q,map_le_iff_le_comap.mp hSC,isSolvable_comap_of_solvable_ker q C,?_⟩
  intro hh
  apply hCn
  have hm := (map_mono (f := q) hh).trans (A.le_normalizer_map q)
  rwa [map_comap_eq_self_of_surjective hq] at hm


end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Outside.Generation.PrimeSelection
