module
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.AbelianSeven
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.BinaryUpper.CompatibleFlags
public import Theory.GroupTheory.NormalSubgroupCoreQuotient
public import Theory.GroupTheory.SolvableRadical.SolvableKernel

/-!
# Excluding the binary four-dimensional component in the abelian branch

For a T-invariant K with K/O₂(K) ≅ PSL₄(2), pass to the literal two-core
quotient of KT. Its normal component image has two compatible generating
flag overgroups containing the same Sylow image. Both are solvable, also
when that Sylow acts by the graph automorphism. Their full preimages are
solvable overgroups of the original T, hence lie in M by12.6.29. Generation
and the retained two-core kernel then force K ≤ M.

The final application strengthens the original reduced-actor catalogue by
excluding A₇ and PSL₄(2). No general E.1.14 equality across a two-core is
used. The PSL₅(2), larger-field and module alternatives remain open.
Source: Aschbacher--Smith12.6.31, p.836, and E.1.14(1), p.214.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section06
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.Components Chapter13.Section08.Components.SourceModels
open ChapterE.ValuesEvenClassical.BinaryUpper
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]
  (S : SourceHypothesis KnownSimple.IsKnownSimple T L V)
  (D : OrthogonalMarking L V S.chosen.normalizes) (hZ : ZV L V = ⊥) (z : V)
  (hz : z ≠ 1) (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
  (hTz : (T : Subgroup G) ≤ normalizer ((D.fullSetup hZ T z).V₁ : Set G))
  (hbound : ∀ g : G, g ∉ normalizer (V : Set G) →
    Nat.card (V ⊓ V.map (MulAut.conj g).toMonoidHom : Subgroup G) ≤ 2 ^ 3)
  (hTI : CentralLine.HasTIConjugatesIn V (M L))
  (hns : ∀ w : V, D.Nonsingular w → Gv w.val ≤ M L)

include hz hTV hTz hbound hTI hns in
/-- Compatible solvable flags exclude PSL₄(2) for the original escaping
T-invariant subgroup, retaining both intrinsic and ambient two-core quotients. -/
theorem SourceHypothesis.original_escaping_binaryFour_impossible
    {K : Subgroup G} (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (hout : ¬ K ≤ M L) (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2) : False := by
  classical
  obtain ⟨F,hF,hfin,hcard,⟨e₀⟩⟩ := hm
  let := hF
  let := hfin
  let := Fintype.ofFinite F
  let eF : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq (by
    simpa only [←Nat.card_eq_fintype_card,Nat.card_zmod] using hcard)
  let e : (K ⧸ pCore 2 K) ≃* PSL 4 := e₀.trans (Atlas.fieldEquivPSL 4 eF)
  let J := K ⊔ (T : Subgroup G)
  let Ki := K.subgroupOf J
  let : Ki.Normal := normal_subgroupOf_of_le_normalizer (sup_le K.le_normalizer hTK)
  let q := QuotientGroup.mk' (pCore 2 J)
  let C := Ki.map q
  let : C.Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let P := (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).mapSurjective
    (QuotientGroup.mk'_surjective (pCore 2 J))
  let eKi : Ki ≃* K := subgroupOfEquivOfLe (show K ≤ J from le_sup_left)
  let eC : C ≃* PSL 4 := (coreQuotientEquivImage 2 Ki).symm.trans
    ((QuotientGroup.congr _ _ eKi (pCore_map_iso 2 eKi)).trans e)
  have hCP : C ⊔ (P : Subgroup (J ⧸ pCore 2 J)) = ⊤ := by
    change (K.subgroupOf J).map q ⊔ ((T : Subgroup G).subgroupOf J).map q = ⊤
    rw [←Subgroup.map_sup,←subgroupOf_sup le_sup_left le_sup_right,subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  obtain ⟨e',he',ho,hm,hT,hgen⟩ := exists_sylowAligned_structured_generating_flags
    (Or.inl rfl : 4 = 4 ∨ 4 = 5) C P eC hCP
  have hmid : Group.IsSolvable (ambientFlag C P e' (middleRoots 4)) :=
    hm.elim And.right (fun h => by omega)
  have hsolv (Q : Subgroup (J ⧸ pCore 2 J)) (hQ : Q ∈ binaryFlagFamily C P e') :
      Group.IsSolvable Q := by
    rcases hQ with rfl | hQ
    · exact ho
    · obtain rfl := hQ
      exact hmid
  let N := (M L).subgroupOf J
  let : Group.IsNilpotent q.ker := by
    rw [QuotientGroup.ker_mk']
    exact pCore_isPGroup.isNilpotent
  have hpre (Q : Subgroup (J ⧸ pCore 2 J)) (hQ : Q ∈ binaryFlagFamily C P e') :
      Q.comap q ≤ N := by
    let U := Q.comap q
    let := hsolv Q hQ
    let : Group.IsSolvable U := isSolvable_comap_of_solvable_ker q Q
    let : Group.IsSolvable (U.map J.subtype) :=
      Group.isSolvable_of_surjective (J.subtype.subgroupMap_surjective U)
    have hTU : (T : Subgroup G) ≤ U.map J.subtype := by
      intro t ht
      refine ⟨⟨t,mem_sup_right ht⟩,?_,rfl⟩
      exact hT Q hQ (mem_map_of_mem q ht)
    exact map_le_iff_le_comap.mp
      (S.original_solvable_overgroup_le D hZ z hz hTV hTz hbound hTI hns hTU)
  have hk : q.ker ≤ N := by
    apply le_trans _ (hpre (ambientFlag C P e' (outerRoots 4)) (by left; rfl))
    intro x hx
    change q x ∈ ambientFlag C P e' (outerRoots 4)
    rw [show q x = 1 from hx]
    exact one_mem _
  have htop : (⊤ : Subgroup (J ⧸ pCore 2 J)) ≤ N.map q := by
    rw [←hgen]
    apply sSup_le
    intro Q hQ
    have hh := map_mono (f := q) (hpre Q hQ)
    have hqr : q.range = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _)
    rwa [map_comap_eq,hqr,inf_eq_right.mpr (le_top : Q ≤ ⊤)] at hh
  have hc := comap_mono (f := q) htop
  rw [comap_top,comap_map_eq,sup_eq_left.mpr hk] at hc
  exact hout (fun k hk => hc (mem_top (⟨k,mem_sup_left hk⟩ : J)))

include hz hTV hTz hbound hTI hns in
/-- The normal reduced component satisfies both small-row exclusions on its
literal intrinsic quotient. -/
theorem SourceHypothesis.original_abelian_normal_component_small_exclusions
    {H K : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz)
    (hKH : K ≤ H) (hout : ¬ K ≤ M L) (hn : (K.subgroupOf H).Normal) :
    ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2 := by
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (show (T : Subgroup G) ≤ H from fun x hx => hH.1.2 (Or.inr hx)).trans
      ((normal_subgroupOf_iff_le_normalizer hKH).mp hn)
  exact ⟨fun ⟨e⟩ => S.original_escaping_alternatingSeven_impossible D hZ z hz hTV hTz hbound hTI hns hTK hout e,
    S.original_escaping_binaryFour_impossible D hZ z hz hTV hTz hbound hTI hns hTK hout⟩

include hz hTV hTz hbound hTI hns in
/-- The constructed escaping component has the exhaustive normal/exchanged
catalogue, with both small normal rows removed, in its actual reduced actor. -/
theorem SourceHypothesis.original_abelian_reduced_catalogue_small_exclusions
    {H : Subgroup G} (hH : H ∈ (D.fullSetup hZ T z).Hz) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧ ¬ K ≤ M L ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧
      (D.fullSetup hZ T z).L₁ ≤ normalizer (K : Set G) ∧
      let K₀ := conjugateSpanBy K (T : Subgroup G)
      let J := K₀ ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)
      (K₀.subgroupOf H).Normal ∧ J ≤ H ∧ J ∈ (D.fullSetup hZ T z).Hz ∧
      (((K.subgroupOf J).Normal ∧ Models.F918Models (actorImage J K) ∧
          Models.ComponentModelOrSuzuki (actorImage J K) ∧
          Models.ComponentModelOrSuzuki (K ⧸ pCore 2 K) ∧
          ¬ Nonempty ((K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7)) ∧
          ¬ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 4 2) ∨
        (¬ (K.subgroupOf J).Normal ∧ (normalizer (K.subgroupOf J : Set J)).index = 2 ∧
          NonnormalF918Models (actorImage J K) ∧ NonnormalF918Models (K ⧸ pCore 2 K))) := by
  obtain ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,hm⟩ :=
    S.original_abelian_reduced_component_catalogue D hZ z hz hTV hTz hbound hTI hns hH
  refine ⟨K,hKH,hK,hout,hq,hL,hK₀,hJH,hJ,?_⟩
  rcases hm with ⟨hn,hF,hcat,hcati,h₇⟩ | hm
  · have hKle := (le_conjugateSpanBy K (T : Subgroup G)).trans
      (le_sup_left.trans (le_sup_left :
        conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ≤
          conjugateSpanBy K (T : Subgroup G) ⊔ (D.fullSetup hZ T z).L₁ ⊔ (T : Subgroup G)))
    exact Or.inl ⟨hn,hF,hcat,hcati,h₇,
      (S.original_abelian_normal_component_small_exclusions D hZ z hz hTV hTz hbound hTI hns
        hJ hKle hout hn).2⟩
  · exact Or.inr hm

end CFSG.Quasithin.Chapter12.Section06
