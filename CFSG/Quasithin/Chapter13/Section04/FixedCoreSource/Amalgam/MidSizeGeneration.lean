module
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.ModelQuotients
public import CFSG.Quasithin.ChapterF.Section06.Elementary.PrimeToThree
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentReduction
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Noncyclic
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentRigidity.RemainingBranch
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentSieve.SourceComponent
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.ComponentProduct.PrimeSource
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.Rigidity.Complete
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.QuasisimpleResidual
public import Theory.SpecificGroups.SymmetricFourSolvable
public import Theory.GroupTheory.PResidual.CommutatorImage
public import Theory.GroupTheory.CComponent.QuotientLifting

/-!
# Mid-size components in a Goldschmidt pair

A normal C-component with an actual mid-size quotient loses exactly its
two-core in the literal prime-to-three quotient. F.6 places one vertex
residual in its image. The single-residual case would force a prime PSL₂
model of order incompatible with every mid-size quotient; hence both
residuals lie in the component and it is the whole two-residual.

An actor moving the first vertex residual therefore moves the whole
component. This extends the quotient argument in PrimeStructure and
Generation to the second pair, whose first vertex centralizes the seed
and so does not satisfy the first pair's fixed-index hypotheses.
The application to the original second join is in SecondGeneration.
Source: Aschbacher--Smith F.6.10,13,16--18, pp.306--310;
13.4.7(3), printed p.903, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration
open Section03.Noncentrality.SupercriticalSource ChapterF.SourceAssembly

private theorem small_order_not_prime_row {n p : ℕ}
    (hn : n = 60 ∨ n = 168 ∨ n = 360 ∨ n = 1080 ∨ n = 6048)
    (hp : p % 24 = 11 ∨ p % 24 = 13)
    (hc : n * 2 = p * (p ^ 2 - 1)) : False := by
  have hnle : n ≤ 6048 := by rcases hn with h | h | h | h | h <;> omega
  have hp24 : p < 24 := by
    by_contra hh
    have h24 : 24 ≤ p := by omega
    have hsq : 576 ≤ p ^ 2 := by nlinarith
    have hs : 575 ≤ p ^ 2 - 1 := by omega
    have hb := Nat.mul_le_mul h24 hs
    omega
  rw [Nat.mod_eq_of_lt hp24] at hp
  rcases hp with hp | hp <;> rcases hn with hn | hn | hn | hn | hn <;>
    norm_num [hp,hn] at hc

universe v
private theorem single_residual_not_midSize_order
    {H Q : Type v} [Group H] [Finite H] [Group Q] [Finite Q]
    {A B : Subgroup Q} (hs : IsSQTK KnownSimple.IsKnownSimple H)
    (e : Q ≃* (H ⧸ pPrimeCore 3 H)) (hg : ChapterF.IsGoldschmidtTriple A B)
    (d : SingleResidualComponent A B)
    (hcards : Nat.card d.component = 60 ∨ Nat.card d.component = 168 ∨
      Nat.card d.component = 360 ∨ Nat.card d.component = 1080 ∨ Nat.card d.component = 6048) :
    False := by
  have hz : pCore 2 Q = ⊥ := le_bot_iff.mp (ChapterF.twoCore_le_primeToThreeCore.trans
    (ChapterF.Noncyclic.primeToThreeCore_eq_bot_of_quotient e).le)
  obtain ⟨p,hp,ho,h8,hm⟩ := d.prime_psl2_of_either_exceptional
    ChapterA.Section02.theoremA_knownSimple ChapterA.Section02.theoremC_knownSimple
    hs e hg hz (Or.inl (d.left_not_characteristic_two hg hz))
  let : Fact p.Prime := ⟨hp⟩
  let : d.component.Normal := d.normal
  have hthree := left_residual_card_three_of_normal_subgroup hg hz d.component
    d.left_contains d.right_escapes
  have h24 := d.source_prime_congruence e hg ho h8 hm hthree
  obtain ⟨_,_,⟨ep⟩⟩ := prime_psl_component_center_and_outer e d.isComponent ho hm
  have hc : Nat.card d.component * 2 = p * (p ^ 2 - 1) := by
    rw [Nat.card_congr ep.toEquiv]
    simpa using Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (F := ZMod p) (by simpa using ho)
  exact small_order_not_prime_row hcards h24 hc

private theorem twoResidual_eq_component_of_prime_image
    {X : Type*} [Group X] [Finite X] (K : Subgroup X) [K.Normal]
    [Group.IsPerfect K]
    (hr : pResidual 2 X = primeToResidual 3 X)
    (hq : pResidual 2 (X ⧸ pPrimeCore 3 X) =
      K.map (QuotientGroup.mk' (pPrimeCore 3 X))) : pResidual 2 X = K := by
  let N := pPrimeCore 3 X
  let q := QuotientGroup.mk' N
  have hm : (pResidual 2 X).map q = K.map q :=
    (map_pResidual_of_surjective 2 q (QuotientGroup.mk'_surjective _)).trans hq
  have hle : pResidual 2 X ≤ K ⊔ N := by
    have hh := map_le_iff_le_comap.mp hm.le
    simpa only [comap_map_eq,q,QuotientGroup.ker_mk'] using hh
  have hidxR : Nat.Coprime 3 (pResidual 2 X).index := by
    obtain ⟨n,hn⟩ := (isPGroup_quotient_pResidual (G := X) 2).exists_card_eq
    rw [index_eq_card,hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hrel : Nat.Coprime 3 (K.relIndex (K ⊔ N)) := by
    rw [relIndex_sup_left]
    exact pPrimeCore_coprime_card.of_dvd_right (relIndex_dvd_card K N)
  have hidx := hrel.mul_right (hidxR.of_dvd_right (index_dvd_of_le hle))
  rw [relIndex_mul_index (show K ≤ K ⊔ N from le_sup_left)] at hidx
  apply le_antisymm
  · rw [hr]
    exact primeToResidual_le K hidx
  · let : Group.IsNilpotent (X ⧸ pResidual 2 X) := (isPGroup_quotient_pResidual 2).isNilpotent
    exact le_of_isPerfect_of_solvable_quotient K (pResidual 2 X)


/-- Transport the actual five-model catalogue along an isomorphism. -/
theorem midSize_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (hm : MidSizeModel A) (e : A ≃* B) : MidSizeModel B := by
  rcases hm with ⟨⟨f⟩⟩ | ⟨F,hF,hfin,hcard,⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨hq,⟨z⟩,⟨f⟩⟩ |
    ⟨F,hF,hfin,J,hcard,hJ,⟨f⟩⟩
  · exact Or.inl ⟨e.symm.trans f⟩
  · exact Or.inr (Or.inl ⟨F,hF,hfin,hcard,⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨e.symm.trans f⟩))
  · let := hq
    have he : (center A).map e.toMonoidHom = center B := by
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        exact (centerCongr e ⟨y,hy⟩).property
      · intro hx
        exact ⟨e.symm x,(centerCongr e.symm ⟨x,hx⟩).property,e.apply_symm_apply x⟩
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨IsQuasisimple.of_mulEquiv e,
      ⟨(centerCongr e).symm.trans z⟩,
      ⟨(QuotientGroup.congr _ _ e he).symm.trans f⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨F,hF,hfin,J,hcard,hJ,⟨e.symm.trans f⟩⟩)))

variable {X : Type*} [Group X] [Finite X]

/-- The literal three-prime quotient removes exactly the two-core of a
normal component with one of the actual mid-size quotient models. -/
theorem component_prime_image (K : Subgroup X) (hK : K.IsCComponent)
    [K.Normal] (hm : MidSizeModel (K ⧸ pCore 2 K)) :
    let q := QuotientGroup.mk' (pPrimeCore 3 X)
    (q.subgroupMap K).ker = pCore 2 K ∧
      IsComponent (X ⧸ pPrimeCore 3 X) (K.map q) ∧ (K.map q).Normal ∧
      ∃ e : (K ⧸ pCore 2 K) ≃* K.map q,
        ∀ k : K, e (QuotientGroup.mk' (pCore 2 K) k) = q.subgroupMap K k := by
  let q := QuotientGroup.mk' (pPrimeCore 3 X)
  let := hK.perfect
  let : Group.IsPerfect (K ⧸ pCore 2 K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (K ⧸ pCore 2 K) := midSize_quasisimple hm
  have hk : (q.subgroupMap K).ker = pCore 2 K := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact CComponentExceptionalQuotient.core_comap K hK.subnormal
      (midSize_primeToThreeCore_eq_bot hm)
  let e : (K ⧸ pCore 2 K) ≃* K.map q :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (q.subgroupMap K)
        (q.subgroupMap_surjective K))
  let : IsQuasisimple (K.map q) := IsQuasisimple.of_mulEquiv e
  exact ⟨hk,⟨hK.subnormal.map (QuotientGroup.mk'_surjective _),inferInstance⟩,
    (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _),e,fun _ => rfl⟩

/-- F.6 excludes a component containing just one of the original residuals:
its prime PSL₂ order is incompatible with every actual mid-size model. -/
theorem component_is_residual {P Q : Subgroup X}
    (hs : IsSQTK KnownSimple.IsKnownSimple X)
    (hg : ChapterF.IsGoldschmidtTriple P Q)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hm : MidSizeModel (K ⧸ pCore 2 K)) :
    let q := QuotientGroup.mk' (pPrimeCore 3 X)
    pResidual 2 (X ⧸ pPrimeCore 3 X) = K.map q ∧
      generalizedFitting (X ⧸ pPrimeCore 3 X) = K.map q ∧
      pResidual 2 X = K := by
  let R := X ⧸ pPrimeCore 3 X
  let q := QuotientGroup.mk' (pPrimeCore 3 X)
  let Pp := P.map q
  let Qp := Q.map q
  let Kp := K.map q
  have hns : ¬ Group.IsSolvable X := by
    intro hh
    let := hh
    exact hK.not_isSolvable inferInstance
  have hqns : ¬ Group.IsSolvable R := by
    intro hh
    exact hns ((Group.isSolvable_iff_subgroup_quotient (pPrimeCore 3 X)).mpr
      ⟨hg.primeToThreeCore_solvable,hh⟩)
  have hp : ChapterF.IsGoldschmidtTriple Pp Qp := by
    rcases hg.primeToThreeCore_dichotomy with hh | hh
    · exact hh.2.1
    obtain ⟨e⟩ := hh.2.2.1
    let : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable_fin_four
    let : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
      Group.isSolvable_of_isSolvable_injective
        (Equiv.Perm.viaEmbeddingHom_injective (Fin.castLEEmb (by decide : 3 ≤ 4)))
    exact (hqns (Group.isSolvable_of_isSolvable_injective
      (f := e.toMonoidHom) e.injective)).elim
  obtain ⟨_,hc,hn,⟨e,he⟩⟩ := component_prime_image K hK hm
  let : Kp.Normal := hn
  let : IsQuasisimple Kp := hc.2
  have hz : pCore 2 R = ⊥ := hg.primeToThreeCore_quotient_twoCore_eq_bot
  have hcyclic : IsCyclic (pCore 3 R) := by
    by_contra hh
    have hr := residual_isThreeGroup_of_cover hs (MulEquiv.refl R) hp hh
    let : Group.IsNilpotent (pResidual 2 R) := hr.isNilpotent
    let : Group.IsNilpotent (R ⧸ pResidual 2 R) :=
      (isPGroup_quotient_pResidual 2).isNilpotent
    exact hqns ((Group.isSolvable_iff_subgroup_quotient (pResidual 2 R)).mpr
      ⟨inferInstance,inferInstance⟩)
  have hcards : Nat.card Kp = 60 ∨ Nat.card Kp = 168 ∨
      Nat.card Kp = 360 ∨ Nat.card Kp = 1080 ∨ Nat.card Kp = 6048 := by
    rw [←Nat.card_congr e.toEquiv]
    exact hm.card
  have both (hP : (pResidual 2 Pp).map Pp.subtype ≤ Kp)
      (hQ : (pResidual 2 Qp).map Qp.subtype ≤ Kp) :
      pResidual 2 R = Kp ∧ generalizedFitting R = Kp := by
    obtain ⟨hr,hf,_⟩ := quasisimple_residual_of_both_local_containments hp
      (pPrimeCore_quotient_pPrimeCore_eq_bot 3) Kp hP hQ
    exact ⟨hr,hf⟩
  have hr : pResidual 2 R = Kp ∧ generalizedFitting R = Kp := by
    rcases normal_component_contains_residual hp hz hc with ⟨hP,hgen⟩ | ⟨hQ,hgen⟩
    · by_cases hQ : (pResidual 2 Qp).map Qp.subtype ≤ Kp
      · exact both hP hQ
      obtain ⟨_,hj,hS⟩ := normal_subgroup_rigidity_setup hp Kp hP hQ
      let d : SingleResidualComponent Pp Qp := ⟨Kp,hc,hn,hP,hQ,hgen,hj,hS⟩
      exact (single_residual_not_midSize_order hs (MulEquiv.refl R) hp d hcards).elim
    · by_cases hP : (pResidual 2 Pp).map Pp.subtype ≤ Kp
      · exact both hP hQ
      obtain ⟨_,hj,hS⟩ := normal_subgroup_rigidity_setup hp.symm Kp hQ hP
      let d : SingleResidualComponent Qp Pp := ⟨Kp,hc,hn,hQ,hP,hgen,hj,hS⟩
      exact (single_residual_not_midSize_order hs (MulEquiv.refl R) hp.symm d hcards).elim
  let := hK.perfect
  exact ⟨hr.1,hr.2,twoResidual_eq_component_of_prime_image K
    hg.twoResidual_eq_primeToThreeResidual hr.1⟩

/-- Movement of one original residual by an actor forces movement of the
whole normal component, with the original two-core kernel retained. -/
theorem component_commutator {P Q : Subgroup X}
    (hg : ChapterF.IsGoldschmidtTriple P Q)
    (K : Subgroup X) (hK : K.IsCComponent) [K.Normal]
    (hm : MidSizeModel (K ⧸ pCore 2 K)) (hr : pResidual 2 X = K)
    (J : Subgroup X) (hmov : ⁅(pResidual 2 P).map P.subtype,J⁆ =
      (pResidual 2 P).map P.subtype) : ⁅K,J⁆ = K := by
  let R := (pResidual 2 P).map P.subtype
  change ⁅R,J⁆ = R at hmov
  have hRK : R ≤ K := (map_pResidual_le 2 P.subtype).trans_eq hr
  have hRnot : ¬ R ≤ pCore 2 X := by
    apply (hg.left_subnormal_core_iff_not_residual_le (pCore 2 X)
      (inferInstance : (pCore 2 X).Normal).isSubnormal).mp
    intro x hx
    have hi : (pCore 2 X).subgroupOf P ≤ pCore 2 P :=
      le_sSup ⟨inferInstance,pCore_isPGroup.comap_subtype⟩
    exact mem_map_of_mem P.subtype
      (hi (show (⟨x,hx.1⟩ : P) ∈ (pCore 2 X).subgroupOf P from hx.2))
  let q := QuotientGroup.mk' (pCore 2 X)
  let Kq := K.map q
  let : Kq.Normal := (inferInstance : K.Normal).map q (QuotientGroup.mk'_surjective _)
  let := hK.perfect
  let : Group.IsPerfect (K ⧸ pCore 2 K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  let : IsQuasisimple (K ⧸ pCore 2 K) := midSize_quasisimple hm
  let : IsQuasisimple Kq := IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hK)
  have hc : IsComponent (X ⧸ pCore 2 X) Kq :=
    ⟨(inferInstance : Kq.Normal).isSubnormal,inferInstance⟩
  have hqmov : ⁅Kq,J.map q⁆ = Kq := by
    apply le_antisymm (commutator_le_left _ _)
    rcases hc.commutator_dichotomy (J.map q) with hh | hh
    · have hz : R.map q = ⊥ := by
        apply le_bot_iff.mp
        rw [←hmov,map_commutator]
        exact (commutator_mono (map_mono hRK) le_rfl).trans_eq hh
      exact (hRnot (by simpa only [Subgroup.map_eq_bot_iff,q,QuotientGroup.ker_mk'] using hz)).elim
    · rw [hh]
      exact le_iSup_conjugates _ _
  exact (eq_commutator_of_isPPerfect_of_map_eq K J
    (hr ▸ isPPerfect_pResidual 2) le_normalizer_of_normal q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hqmov.symm).symm

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SecondGeneration
