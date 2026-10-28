module
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationUnitary
public import Theory.SpecificGroups.SU3.FiveSylow
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SemidihedralControl
public import Theory.SpecificGroups.Classical.SylowMarkedSL2.SignedThree
public import Theory.GroupTheory.SolvableSemidihedralInvolution
public import Theory.GroupTheory.CoprimeProductIntersection
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanPermutability
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.SourceOldResidualCartanNormalizationCases

/-!
# Actual Cartan normalization in the PSU₃(5) containing row

After the line-normalizer two-core quotient, the smaller local section is
SL₂(5). The original Cartan and full Sylow permute. Their solvable join
meets the normal PSU₃(5) container in a group of order forty-eight with a
semidihedral Sylow subgroup of order sixteen. Its characteristic central
involution is therefore fixed by the whole join. The embedded SL₂(5) is
the derived centralizer of that involution and is consequently normalized.

Perfectness lifts this normalization through the original ambient two-core.
The source theorem retains the literal old residual and its A₅ quotient;
the final application removes PSU₃(5) from the existing source reduction.
No invariant-Sylow assumption or model-shortlist premise is imposed.

Source: Aschbacher--Smith, Proposition 9.3.1, printed pp.732--733, with the
embedding and Sylow rows A.3.14 and A.3.21(a), pp.49--50,55.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups Pointwise
open CFSG.Quasithin CFSG.Quasithin.ChapterA.Section03
namespace CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalizationUnitary
variable {G : Type*} [Group G] [Finite G]

private theorem unitary_inputs (hm : ClassicalGroup.IsPSU G 3 5) (S : Sylow 2 G) :
    (Nat.card S = 16 ∧ Stellmacher.IsSemidihedralGroup S) ∧
      (∀ z : G, orderOf z=2 → Nat.card (commutator (centralizer ({z} : Set G))) ≤ 120) := by
  obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
  let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Finite.of_surjective J.specialToProjective J.specialToProjective_surjective
  let R := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let d : S ≃* R := (S : Subgroup G).equivMapOfInjective e.toMonoidHom e.injective
  obtain ⟨hRc,hRs⟩ := HermitianForm.FiveSylow.sylow_semidihedral J hF hc R
  refine ⟨⟨(Nat.card_congr d.toEquiv).trans hRc,Semidihedral.of_mulEquiv d.symm hRs⟩,?_⟩
  have hbound := Theory.SpecificGroups.Classical.SylowMarkedSL2.derived_centralizer_bound_of_central_cube_cover
    J.specialToProjective J.specialToProjective_surjective J.specialToProjective_ker_le_center
    (fun x hx => congrArg Subtype.val (J.specialToProjective_ker_cube ⟨x,hx⟩))
    (Theory.SpecificGroups.Classical.SylowMarkedSL2.unitary_derived_centralizer_card_le J hF hc)
  intro z hz
  let eC := Theory.GroupTheory.CentralizerSmallKernelTransport.centralizerEquiv e z
  have hcard : Nat.card (commutator (centralizer ({z} : Set G))) =
      Nat.card (commutator (centralizer ({e z} : Set (ProjectiveSpecialUnitaryMatrixGroup J)))) := by
    rw [←card_map_of_injective (K := commutator (centralizer ({z} : Set G)))
      (f := eC.toMonoidHom) eC.injective,map_commutator_eq,
      MonoidHom.range_eq_top.mpr eC.surjective,←commutator_def]
  rw [hcard]
  exact hbound (e z) ((e.orderOf_eq z).trans hz)

private theorem control_of_solvable_intersection
    (hm : ClassicalGroup.IsPSU G 3 5) (S : Sylow 2 G)
    (K : Subgroup G) (hK : Chapter1.Section02.LocalModels.IsSL K 2 5)
    (hSK : (S : Subgroup G) ≤ normalizer (K : Set G))
    (X : Subgroup G) [Group.IsSolvable X] (hcard : Nat.card X=48)
    (hSX : (S : Subgroup G) ≤ X) (c : MulAut G)
    (hc : X.map c.toMonoidHom=X) : K.map c.toMonoidHom=K := by
  obtain ⟨⟨hSc,hSs⟩,hbound⟩ := unitary_inputs hm S
  let R := S.subtype hSX
  let d : R ≃* S := subgroupOfEquivOfLe hSX
  have hRs := Semidihedral.of_mulEquiv d.symm hSs
  obtain ⟨n,hn,hncard,a,b,ha,hb,hab,hgen⟩ := hRs
  have hn4 : n=4 := by
    have he : 2^n=2^4 := by rw [←hncard,Nat.card_congr d.toEquiv,hSc]; norm_num
    exact Nat.pow_right_injective (by decide : 1<2) he
  have ha8 : orderOf a=8 := by simpa [hn4] using ha
  have hab3 : b*a*b⁻¹=a^3 := by simpa [hn4] using hab
  let cX : MulAut X := (c.subgroupMap X).trans (MulEquiv.subgroupCongr hc)
  have hfix := Semidihedral.automorphism_fix_fourth_of_solvable_card_forty_eight
    (inferInstance : Group.IsSolvable X) hcard R a b ha8 hb hab3 hgen cX
  have hfixG : c ((d a : G)^4)=(d a : G)^4 := congrArg X.subtype hfix
  have hgenS : closure ({d a,d b} : Set S)=⊤ := by
    rw [←Set.image_pair]
    change closure (d.toMonoidHom '' ({a,b} : Set R))=⊤
    rw [←MonoidHom.map_closure,hgen,map_top_of_surjective _ d.surjective]
  obtain ⟨E,_,_,hE,⟨eK⟩⟩ := hK
  apply Theory.SpecificGroups.Classical.SylowMarkedSL2.automorphism_preserves_sl2_five_of_fix_fourth
    hbound K eK hE S hSK (d a) (d b) ((d.orderOf_eq a).trans ha8)
    ((d.orderOf_eq b).trans hb) _ hgenS c hfixG
  simpa only [map_mul,map_inv,map_pow] using congrArg d hab3

private theorem normalizes_of_solvable_intersection
    (I Y : Subgroup G) [I.Normal] [Group.IsSolvable Y]
    (hm : ClassicalGroup.IsPSU I 3 5) (S : Sylow 2 I)
    (K : Subgroup I) (hK : Chapter1.Section02.LocalModels.IsSL K 2 5)
    (hSK : (S : Subgroup I) ≤ normalizer (K : Set I))
    (hSY : (S : Subgroup I).map I.subtype ≤ Y)
    (hcard : Nat.card (Y.subgroupOf I)=48) :
    Y ≤ normalizer (K.map I.subtype : Set G) := by
  let X := Y.subgroupOf I
  let f : X →* Y := (I.subtype.comp X.subtype).codRestrict Y (fun x => x.property)
  let : Group.IsSolvable X := Group.isSolvable_of_isSolvable_injective (f := f) (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : Y => (t : G)) he)
  have hSX : (S : Subgroup I) ≤ X := fun x hx => hSY (mem_map_of_mem I.subtype hx)
  intro y hy
  let c : MulAut I := MulAut.conjNormal y
  have hc : X.map c.toMonoidHom=X := by
    apply le_antisymm
    · rintro x ⟨a,ha,rfl⟩
      exact Y.mul_mem (Y.mul_mem hy ha) (Y.inv_mem hy)
    · intro x hx
      refine ⟨c.symm x,?_,c.apply_symm_apply x⟩
      change ((MulAut.conjNormal y).symm x : G) ∈ Y
      rw [MulAut.conjNormal_symm_apply]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hx) hy
  have hcontrol := control_of_solvable_intersection hm S K hK hSK X hcard hSX c hc
  apply mem_normalizer_iff_map_conj_eq.mpr
  change (K.map I.subtype).map (MulAut.conj y).toMonoidHom=K.map I.subtype
  have hh := congrArg (map I.subtype) hcontrol
  have hfun : I.subtype.comp c.toMonoidHom = (MulAut.conj y).toMonoidHom.comp I.subtype := by
    ext x
    rfl
  simpa only [Subgroup.map_map,hfun] using hh

/-- In an actual PSU₃(5) container the permuting cubic subgroup normalizes
its marked perfect local subgroup, including a possible original two-core. -/
theorem cartan_normalizes_in_unitary_container
    (P : Sylow 2 G) (K J A : Subgroup G) [J.Normal]
    [Group.IsSolvable (A ⊔ (P : Subgroup G) : Subgroup G)]
    (hJ : J.IsCComponent) (hK : K ∈ localCComponents P)
    (hKJ : K ≤ J) (hPK : (P : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5))
    (hA : IsPGroup 3 A) (hAJ : Nat.card (A ⊓ J : Subgroup G)=3)
    (hperm : (A : Set G)*((P : Subgroup G) : Set G)=((P : Subgroup G) : Set G)*(A : Set G))
    (hm : ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 5) :
    A ≤ normalizer (K : Set G) := by
  let Q := pCore 2 G
  let q := QuotientGroup.mk' Q
  let : Group.IsNilpotent Q := pCore_isNilpotent
  let : Group.IsSolvable q.ker := by
    rw [QuotientGroup.ker_mk']
    infer_instance
  let : Group.IsPerfect K := by
    let := hK.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show K ≤ K ⊔ (P : Subgroup G) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  have hQK : Q ≤ normalizer (K : Set G) :=
    (pCore_isPGroup.le_sylow_of_normal P).trans hPK
  let S := P.mapSurjective (f := q) (QuotientGroup.mk'_surjective Q)
  let I := J.map q
  let KB := K.map q
  let Z := A.map q ⊔ (S : Subgroup (G ⧸ Q))
  let : I.Normal := inferInstance
  have hBI : KB ≤ I := map_mono hKJ
  have hlocal : KB ∈ localCComponents S :=
    Chapter1.Section02.localCComponents_map_of_solvable_ker hK q
  have hSK : (S : Subgroup (G ⧸ Q)) ≤ normalizer (KB : Set (G ⧸ Q)) :=
    (map_mono hPK).trans (le_normalizer_map q)
  obtain ⟨R,hR,_,hRK⟩ := SourceEmbeddings.exists_local_sylow_normalizing S hlocal
    (hJ.map_quotient Q).subnormal hBI hSK
  have hmI : ClassicalGroup.IsPSU I 3 5 :=
    hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hJ).symm
  have hKSL := local_image_isSL_two_five P K J hJ hK hKJ hPK eK hm
  have hRc : Nat.card R=16 := (unitary_inputs hmI R).1.1
  have hSI : Nat.card ((S : Subgroup (G ⧸ Q)) ⊓ I : Subgroup (G ⧸ Q))=16 := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe
      (show (S : Subgroup (G ⧸ Q)) ⊓ I ≤ I from inf_le_right)).toEquiv,
      inf_subgroupOf_right,←hR]
    exact hRc
  have hpbar : (A.map q : Set (G ⧸ Q))*((S : Subgroup (G ⧸ Q)) : Set (G ⧸ Q)) =
      ((S : Subgroup (G ⧸ Q)) : Set (G ⧸ Q))*(A.map q : Set (G ⧸ Q)) := by
    have he := congrArg (Set.image q) hperm
    simpa only [Set.image_mul,←coe_map,S,Sylow.coe_mapSurjective] using he
  have hZc : Nat.card (Z.subgroupOf I)=48 :=
    card_subgroupOf_sup_twoCore_eq_fortyEight A J hA S hpbar hAJ hSI
  have hZ : (A ⊔ (P : Subgroup G)).map q=Z := by
    rw [Subgroup.map_sup]
    rfl
  let : Group.IsSolvable Z := hZ ▸
    Group.isSolvable_of_surjective (q.subgroupMap_surjective (A ⊔ (P : Subgroup G)))
  have hnZ := normalizes_of_solvable_intersection I Z hmI R (KB.subgroupOf I)
    hKSL hRK (by rw [hR,subgroupOf_map_subtype]; exact inf_le_left.trans le_sup_right) hZc
  rw [map_subgroupOf_eq_of_le hBI] at hnZ
  have hnA : A.map q ≤ normalizer (KB : Set (G ⧸ Q)) := le_sup_left.trans hnZ
  have hh := map_le_iff_le_comap.mp hnA
  rwa [normalizer_perfect_image_comap K Q pCore_isPGroup hQK] at hh

end CFSG.Quasithin.Chapter10.SourceOldResidualCartanNormalizationUnitary

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterA.Section03
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original order-nine Cartan normalizes the literal old residual in
its PSU₃(5) containing-component row. -/
theorem cartan_normalizes_old_residual_of_unitary_three_container
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (eK : ((pResidual 2 H).map H.subtype ⧸
      pCore 2 ((pResidual 2 H).map H.subtype)) ≃* alternatingGroup (Fin 5))
    (A J : Subgroup G) [IsElementaryAbelian 3 A]
    (hAB : A ≤ sourceOrbitBorel T L) (hA9 : Nat.card A=9)
    (hAJ : Nat.card (A ⊓ J : Subgroup G)=3)
    (hJU : J ≤ normalizer (m.tensorLine : Set G))
    (hJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent)
    (hnJ : (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal)
    (hKJ : (pResidual 2 H).map H.subtype ≤ J)
    (hm : ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 5) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  let N := normalizer (m.tensorLine : Set G)
  let K0 := (pResidual 2 H).map H.subtype
  have hKN : K0 ≤ N := hKJ.trans hJU
  have hAN : A ≤ N := hAB.trans m.borel_normalizes_tensorLine
  let P := T.subtype m.tensorLine_normalized
  let K := K0.subgroupOf N
  let JN := J.subgroupOf N
  let AN := A.subgroupOf N
  let Y := (A ⊔ (T : Subgroup G)).subgroupOf N
  let : JN.Normal := hnJ
  let : Group.IsSolvable (A ⊔ (T : Subgroup G) : Subgroup G) :=
    m.cartan_sylow_join_isSolvable A hAB
  let : Group.IsSolvable Y := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (sup_le hAN m.tensorLine_normalized)).toMonoidHom)
    (subgroupOfEquivOfLe (sup_le hAN m.tensorLine_normalized)).injective
  have hAY : AN ⊔ (P : Subgroup N) ≤ Y :=
    sup_le (comap_mono le_sup_left) (comap_mono le_sup_right)
  let : Group.IsSolvable (AN ⊔ (P : Subgroup N) : Subgroup N) :=
    Group.isSolvable_of_isSolvable_injective (f := inclusion hAY) (inclusion_injective hAY)
  have hlocal : K ∈ localCComponents P := SourceEmbeddings.local_restrict
    (source_hstar_residual_mem_local_of_a5 hH eK).1 hKN
  have hPK : (P : Subgroup N) ≤ normalizer (K : Set N) := by
    rw [←subgroupOf_normalizer_eq hKN]
    exact comap_mono (hH.1.1.2.trans (le_normalizer_embedded_pResidual 2 H))
  let b : JN ≃* J := subgroupOfEquivOfLe hJU
  let eJN : (JN ⧸ pCore 2 JN) ≃* (J ⧸ pCore 2 J) :=
    QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  have hmJN := hm.of_mulEquiv eJN
  let k : K ≃* K0 := subgroupOfEquivOfLe hKN
  let eKN : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ k (pCore_map_iso 2 k)).trans eK
  have hAJN : Nat.card (AN ⊓ JN : Subgroup N)=3 := by
    change Nat.card ((A ⊓ J).subgroupOf N)=3
    rw [Nat.card_congr (subgroupOfEquivOfLe
      (show A ⊓ J ≤ N from inf_le_left.trans hAN)).toEquiv,hAJ]
  have hp : (AN : Set N)*((P : Subgroup N) : Set N)=((P : Subgroup N) : Set N)*(AN : Set N) := by
    simpa only [Subgroup.map_id] using
      m.cartan_sylow_image_permute A N hAB hA9 hAN m.tensorLine_normalized (MonoidHom.id N)
  have hn := SourceOldResidualCartanNormalizationUnitary.cartan_normalizes_in_unitary_container
    P K JN AN hJ hlocal (comap_mono hKJ) hPK eKN
    (IsElementaryAbelian.isPGroup 3 A).comap_subtype hAJN hp hmJN
  rw [←subgroupOf_normalizer_eq hKN] at hn
  exact fun a ha => hn (show (⟨a,hAN ha⟩ : N) ∈ AN from ha)

end CFSG.Quasithin.Chapter10.SourceA5TensorModel

namespace CFSG.Quasithin.Chapter10.SourceA5TensorModel
open Chapter3.Section02 ChapterE
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5)}
  (m : SourceA5TensorModel D e)

/-- The original containing-component reduction excludes the actual PSU₃(5)
row as well as the previously established outer-two and PSL₃(4) rows. -/
theorem nonzero_core_cartan_normalization_remaining_nonunitary_cases
    {H : Subgroup G} (hH : H ∈ Chapter3.HStar (T : Subgroup G) D.maximalLocal)
    (hlarge : 1 < generationParameter H)
    (A B : Subgroup G) (hAB : A ≤ sourceOrbitBorel T L)
    (hA9 : Nat.card A = 9) (hAe : IsElementaryAbelian 3 A)
    (hB3 : Nat.card B = 3) (hBK : B ≤ (pResidual 2 H).map H.subtype)
    (hBC : B = A ⊓ centralizer (m.tensorLine : Set G))
    (hcore : pCore 2 (H ⊔ A : Subgroup G) ≠ ⊥) :
    A ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) ∨
    ∃ J : Subgroup G,
      J ≤ normalizer (m.tensorLine : Set G) ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).IsCComponent ∧
      (J.subgroupOf (normalizer (m.tensorLine : Set G))).Normal ∧
      (pResidual 2 H).map H.subtype < J ∧
      A ≤ normalizer (J : Set G) ∧
      J ≤ centralizer (m.tensorLine : Set G) ∧
      J.pCoreIn 2 ≤ (T : Subgroup G) ∧
      A ⊓ J = B ∧ primeRank 3 J ≤ 2 ∧
      ¬ (IsQuasisimple (J ⧸ pCore 2 J) ∧ center (J ⧸ pCore 2 J) = ⊥ ∧
        IsPGroup 2 (MulAut.Outer (J ⧸ pCore 2 J))) ∧
      ¬ ClassicalGroup.IsPSL (J ⧸ pCore 2 J) 3 4 ∧
      ¬ ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 5 := by
  rcases m.nonzero_core_cartan_normalization_remaining_cases hH hlarge A B hAB hA9
    hAe hB3 hBK hBC hcore with hnorm | ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,ho,hl⟩
  · exact Or.inl hnorm
  by_cases hm : ClassicalGroup.IsPSU (J ⧸ pCore 2 J) 3 5
  · let := hAe
    obtain ⟨eK⟩ := m.old_residual_a5 hH hlarge
    exact Or.inl (m.cartan_normalizes_old_residual_of_unitary_three_container hH eK A J
      hAB hA9 (by rw [hAJB,hB3]) hJU hJ hnJ hKJ.le hm)
  · exact Or.inr ⟨J,hJU,hJ,hnJ,hKJ,hAJ,hJC,hQT,hAJB,hr,ho,hl,hm⟩

end CFSG.Quasithin.Chapter10.SourceA5TensorModel
