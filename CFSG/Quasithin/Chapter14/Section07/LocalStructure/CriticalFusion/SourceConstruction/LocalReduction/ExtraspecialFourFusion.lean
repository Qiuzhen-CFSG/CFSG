module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction.ExtraspecialCentralFour
public import CFSG.Quasithin.Chapter1.Section01Overgroups.Sylow
public import Theory.GroupTheory.SylowCentralizerOfNormalizer
public import Theory.GroupTheory.RelativeSylowNormalizer
public import Theory.GroupTheory.NormalFourCentralizer
/-!
# Sylow control and fusion of the extraspecial central four-group

For the subgroup D selected after 14.7.25, take x in D outside V₁.
Its centralizer in H is exactly C_G(D). This is normal in H and has
characteristic two. Its Sylow subgroup is the literal C_T(x).

The established centrality of Z(O₂(K)) makes K centralize the center of
O₂(C_H(x)), by residual commutator idempotence. Consequently H normalizes
Z(C_T(x)); maximal two-local uniqueness gives its exact normalizer H.
This promotes C_T(x) to Sylow in C_G(x). In the noncentral branch it has
index two in T, separating x from the point conjugacy class. The two
outside involutions form one T-orbit, so H controls fusion in D.

The final application uses the original selected D. It reduces its remaining
TI assertion to containment of the outside involution centralizers; it does
not assume that containment or assert completion of 14.7.26.

Source: Aschbacher–Smith, refs/quasithin.pdf, 14.7.26, printed p.1052,
and I.6.1(1), printed p.424.
-/

public noncomputable section
open Subgroup Representation Theory.GroupTheory
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
open Chapter12.Section08 CriticalFusion.Source Chapter1
open Chapter14.Section04.LargerDimension.LocalAction.Components
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open ChapterI.Section06To08
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem four_sup_point (D Z : Subgroup G) (hD : Nat.card D = 4)
    (hZ : Nat.card Z = 2) (hZD : Z ≤ D) {x : G} (hx : x ∈ D) (hxZ : x ∉ Z) :
    Z ⊔ zpowers x = D := by
  have hle : Z ⊔ zpowers x ≤ D := sup_le hZD (zpowers_le.mpr hx)
  have hlt : Z < Z ⊔ zpowers x := lt_of_le_of_ne le_sup_left (by
    intro he
    exact hxZ (he ▸ (le_sup_right : zpowers x ≤ Z ⊔ zpowers x) (mem_zpowers x)))
  have hh : 2 < Nat.card (Z ⊔ zpowers x : Subgroup G) := by
    by_contra! hh
    exact hlt.ne (eq_of_le_of_card_ge le_sup_left (by rwa [hZ]))
  apply eq_of_le_of_card_ge hle
  have hd := card_dvd_of_le hle
  rw [hD] at hd ⊢
  have heq : 4 = Nat.card (Z ⊔ zpowers x : Subgroup G) :=
    Nat.eq_of_dvd_of_lt_two_mul (by decide : 4 ≠ 0) hd (by omega)
  exact heq.le

private theorem coreCenter_centralized (J A : Subgroup G)
    (hAJ : A ≤ J) (hJA : J ≤ normalizer (A : Set G)) (hA : IsPPerfect 2 A)
    (hc : (center (A.pCoreIn 2)).map (A.pCoreIn 2).subtype ≤
      centralizer (A : Set G)) :
    (center (J.pCoreIn 2)).map (J.pCoreIn 2).subtype ≤ centralizer (A : Set G) := by
  let Q := J.pCoreIn 2
  let P := A.pCoreIn 2
  let Z := (center Q).map Q.subtype
  have hPQ : P ≤ Q := pCoreIn_mono_of_normalizes hAJ hJA
  have hZQ : Z ≤ Q := map_subtype_le _
  have hZC : Z ≤ centralizer (P : Set G) := by
    rw [show Z = Q ⊓ centralizer (Q : Set G) from map_center_subtype_eq_inf_centralizer Q]
    exact inf_le_right.trans (centralizer_le hPQ)
  have hAZ : A ≤ normalizer (Z : Set G) := hAJ.trans
    (J.le_normalizer.trans ((normalizer_le_normalizer_characteristic_image J (pCore 2 J)).trans
      (normalizer_le_normalizer_characteristic_image Q (center Q))))
  have hmove : ⁅Z,A⁆ ≤ (center P).map P.subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    have hz := le_normalizer_iff_commutator_le_left.mp hAZ
    refine le_inf ?_ (hz.trans hZC)
    apply (le_inf ?_ (hz.trans hZQ)).trans (inf_pCoreIn_le_of_le 2 hAJ)
    exact le_normalizer_iff_commutator_le_right.mp ((hZQ.trans (pCoreIn_le 2 J)).trans hJA)
  apply commutator_eq_bot_iff_le_centralizer.mp
  apply le_bot_iff.mp
  rw [← commutator_isPPerfect_idempotent A Z hA ((isPGroup_pCoreIn 2 J).to_le hZQ) hAZ]
  exact (commutator_mono hmove le_rfl).trans
    (commutator_eq_bot_iff_le_centralizer.mpr hc).le

variable {T : Sylow 2 G} {L V : Subgroup G} {F : InvariantFlag T V 3}

private theorem four_point_centralizer (D Z H : Subgroup G)
    (hD : Nat.card D = 4) (hZ : Nat.card Z = 2) (hZD : Z ≤ D)
    (hHC : H ≤ centralizer (Z : Set G))
    (hCH : centralizer (D : Set G) ≤ H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ Z) :
    H ⊓ centralizer ({x} : Set G) = centralizer (D : Set G) := by
  apply le_antisymm
  · intro a ha
    have hZa : Z ≤ centralizer ({a} : Set G) := by
      intro z hz
      exact mem_centralizer_singleton_iff.mpr (hHC ha.1 z hz)
    have hxa : x ∈ centralizer ({a} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp ha.2).symm
    have hDa : D ≤ centralizer ({a} : Set G) := by
      rw [← four_sup_point D Z hD hZ hZD hx hxZ]
      exact sup_le hZa (zpowers_le.mpr hxa)
    intro z hz
    exact mem_centralizer_singleton_iff.mp (hDa hz)
  · intro a ha
    exact ⟨hCH ha,mem_centralizer_singleton_iff.mpr (ha x hx).symm⟩

/-- The centralizer in H of every nonpoint element of the source four-group
is characteristic two. Its Sylow center has normalizer exactly H, and the
same Sylow subgroup is Sylow in the full element centralizer. -/
theorem extraspecial_four_centralizer_sylow
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H)
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    let J := F.H ⊓ centralizer ({x} : Set G)
    let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
    J = centralizer (D : Set G) ∧ J ∈ He G ∧
      normalizer ((center S).map S.subtype : Set G) = F.H ∧
      normalizer (S : Set G) ≤ F.H ∧
      (∃ P : Sylow 2 J, (P : Subgroup J).map J.subtype = S) ∧
      (∃ P : Sylow 2 (centralizer ({x} : Set G)),
        (P : Subgroup (centralizer ({x} : Set G))).map
          (centralizer ({x} : Set G)).subtype = S) := by
  let J := F.H ⊓ centralizer ({x} : Set G)
  let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
  let ZS := (center S).map S.subtype
  obtain ⟨hNK,hHC,hmax,hcore⟩ := extraspecial_source_14721
    d h hab structural previous faithful earlier he
  have hHC' : F.H ≤ centralizer (F.Vi 1 : Set G) := hHC.le
  have hCH : centralizer (D : Set G) ≤ F.H :=
    (Subgroup.centralizer_le_normalizer _).trans hND.le
  have hJ : J = centralizer (D : Set G) := four_point_centralizer D (F.Vi 1) F.H
    hcard (by simpa using F.card 1 (by decide)) hZD hHC' hCH hx hxZ
  have hS : S = (T : Subgroup G) ⊓ centralizer (D : Set G) := by
    calc
      S = (T : Subgroup G) ⊓ J := by
        dsimp [S,J]
        rw [← inf_assoc,inf_eq_left.mpr (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
      _ = _ := by rw [hJ]
  have hHnD : F.H ≤ normalizer (D : Set G) := hND.ge
  have hHnJ : F.H ≤ normalizer (J : Set G) := by
    rw [hJ]
    exact hHnD.trans (normalizer_le_normalizer_centralizer D)
  have hx1 : x ≠ 1 := fun he => hxZ (he ▸ (F.Vi 1).one_mem)
  have hxJ : x ∈ J := by
    rw [hJ]
    exact D.le_centralizer hx
  have hJne : J ≠ ⊥ := fun he => hx1 (show x ∈ (⊥ : Subgroup G) from he ▸ hxJ)
  have hJHe : J ∈ He G := lemma_1_1_3_1
    (mem_He_iff.mpr (d.qtke.evenCharacteristic T F.H hmax (F.invariant 1)))
    hJne inf_le_left (normal_subgroupOf_of_le_normalizer hHnJ).isSubnormal
  obtain ⟨P,hP⟩ := T.exists_centralizer_sylow_of_normalizes D
    ((F.invariant 1).trans hHnD)
  have hPS : ∃ P : Sylow 2 J, (P : Subgroup J).map J.subtype = S := by
    rw [hJ,hS]
    exact ⟨P,hP⟩
  have hQS : J.pCoreIn 2 ≤ S := by
    obtain ⟨P,hP⟩ := hPS
    exact hP ▸ pCoreIn_le_sylow J P
  have hZSC : ZS ≤ centralizer (S : Set G) := by
    rw [show ZS = S ⊓ centralizer (S : Set G) from map_center_subtype_eq_inf_centralizer S]
    exact inf_le_right
  have hZSJ : ZS ≤ J := (map_subtype_le _).trans
    (le_inf (inf_le_left.trans (F.invariant 1)) inf_le_right)
  have hZSQ : ZS ≤ (center (J.pCoreIn 2)).map (J.pCoreIn 2).subtype := by
    rw [map_center_subtype_eq_inf_centralizer]
    exact le_inf ((le_inf hZSJ (hZSC.trans (centralizer_le hQS))).trans hJHe)
      (hZSC.trans (centralizer_le hQS))
  have hKJ : K F ≤ J := by
    rw [hJ]
    apply le_centralizer_iff.mp
    rw [map_center_subtype_eq_inf_centralizer] at hDK
    exact hDK.trans inf_le_right
  have hKC : K F ≤ centralizer (ZS : Set G) := le_centralizer_iff.mp
    (hZSQ.trans (coreCenter_centralized J (K F) hKJ
      (inf_le_left.trans (H_normalizes_K F)) (K_twoPerfect F)
      (hcore.trans (by rw [map_center_subtype_eq_inf_centralizer]; exact inf_le_right))))
  have hTnS : (T : Subgroup G) ≤ normalizer (S : Set G) := by
    rw [hS]
    exact (le_inf (T : Subgroup G).le_normalizer
      (((F.invariant 1).trans hHnD).trans (normalizer_le_normalizer_centralizer D))).trans
      inf_normalizer_le_normalizer_inf
  have hHnZS : F.H ≤ normalizer (ZS : Set G) := by
    rw [residual_product F]
    exact sup_le (hKC.trans (Subgroup.centralizer_le_normalizer _))
      (hTnS.trans (normalizer_le_normalizer_characteristic_image S (center S)))
  have hxZS : x ∈ ZS := by
    rw [show ZS = S ⊓ centralizer (S : Set G) from map_center_subtype_eq_inf_centralizer S]
    refine ⟨⟨hDT hx,mem_centralizer_singleton_iff.mpr rfl⟩,?_⟩
    intro s hs
    exact mem_centralizer_singleton_iff.mp hs.2
  have hZSne : ZS ≠ ⊥ := fun he => hx1 (show x ∈ (⊥ : Subgroup G) from he ▸ hxZS)
  have hN : normalizer (ZS : Set G) = F.H := le_antisymm
    (hmax.2 ⟨ZS,hZSne,T.isPGroup'.to_le ((map_subtype_le _).trans inf_le_left),rfl⟩ hHnZS)
    hHnZS
  have hNS : normalizer (S : Set G) ≤ F.H :=
    (normalizer_le_normalizer_characteristic_image S (center S)).trans hN.le
  exact ⟨hJ,hJHe,hN,hNS,hPS,exists_sylow_eq_of_relative_normalizer_le hPS inf_le_right
    (le_inf (inf_le_right.trans hNS) inf_le_left)⟩

private theorem not_isConj_of_proper_sylow_centralizer
    (T : Sylow 2 G) {x z : G}
    (hx : ¬ (T : Subgroup G) ≤ centralizer ({x} : Set G))
    (hz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hs : ∃ P : Sylow 2 (centralizer ({x} : Set G)),
      (P : Subgroup (centralizer ({x} : Set G))).map
        (centralizer ({x} : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer ({x} : Set G)) : ¬ IsConj x z := by
  intro hc
  obtain ⟨g,hg⟩ := isConj_iff.mp hc
  let f : G ≃* G := MulAut.conj (g : G)
  have hf : f x = z := hg
  have hcard : Nat.card (centralizer ({x} : Set G)) =
      Nat.card (centralizer ({z} : Set G)) := by
    apply Nat.card_congr (Equiv.subtypeEquiv f.toEquiv ?_)
    intro a
    have hfa : f.toEquiv a = f a := rfl
    rw [hfa]
    simp only [mem_centralizer_singleton_iff]
    constructor
    · intro ha
      simpa only [map_mul,hf] using congrArg f ha
    · intro ha
      apply f.injective
      simpa only [map_mul,hf] using ha
  obtain ⟨P,hP⟩ := hs
  have hsz : Nat.card P = Nat.card (T.subtype hz) := by
    rw [P.card_eq_multiplicity,(T.subtype hz).card_eq_multiplicity,hcard]
  have hst : Nat.card ((T : Subgroup G) ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card T := by
    rw [←hP,card_map_of_injective (centralizer ({x} : Set G)).subtype_injective,hsz]
    exact Nat.card_congr (subgroupOfEquivOfLe hz).toEquiv
  have heq : (T : Subgroup G) ⊓ centralizer ({x} : Set G) = (T : Subgroup G) :=
    eq_of_le_of_card_ge inf_le_left hst.ge
  exact hx (heq ▸ (inf_le_right : (T : Subgroup G) ⊓ centralizer ({x} : Set G) ≤ _))

private theorem four_outside_orbit (T D Z : Subgroup G)
    (hD : Nat.card D = 4) (hZ : Nat.card Z = 2) (hZD : Z ≤ D)
    (hTD : T ≤ normalizer (D : Set G)) (hTZ : T ≤ normalizer (Z : Set G))
    (x y : G) (hx : x ∈ D) (hxZ : x ∉ Z) (hy : y ∈ D) (hyZ : y ∉ Z)
    (hm : ¬ T ≤ centralizer ({x} : Set G)) :
    ∃ t : T, (t : G) * x * (t : G)⁻¹ = y := by
  classical
  let E := {a : D // (a : G) ∉ Z}
  let : Fintype D := Fintype.ofFinite D
  have hZi : Nat.card {a : D // (a : G) ∈ Z} = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZD).toEquiv).trans hZ
  have hE : Nat.card E = 2 := by
    change Nat.card {a : D // ¬ (a : G) ∈ Z} = 2
    simp only [Nat.card_eq_fintype_card] at hD hZi ⊢
    rw [Fintype.card_subtype_compl,hD,hZi]
  let a : E := ⟨⟨x,hx⟩,hxZ⟩
  let b : E := ⟨⟨y,hy⟩,hyZ⟩
  obtain ⟨t,ht,htc⟩ := SetLike.not_le_iff_exists.mp hm
  have hmove : t * x * t⁻¹ ≠ x := fun he => htc
    (mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he))
  let c : E := ⟨⟨t*x*t⁻¹,(mem_normalizer_iff.mp (hTD ht) x).mp hx⟩,
    fun he => hxZ ((mem_normalizer_iff.mp (hTZ ht) x).mpr he)⟩
  have hca : c ≠ a := fun he => hmove (congrArg (fun e : E => ((e : D) : G)) he)
  by_cases hba : b = a
  · refine ⟨1,?_⟩
    simpa only [OneMemClass.coe_one,mul_one,one_mul,inv_one] using
      (show x = y from (congrArg (fun e : E => ((e : D) : G)) hba).symm)
  obtain ⟨r,_,hr⟩ := (Nat.card_eq_two_iff' a).mp hE
  have hcb : c = b := (hr c hca).trans (hr b hba).symm
  exact ⟨⟨t,ht⟩,congrArg (fun e : E => ((e : D) : G)) hcb⟩

/-- The original H controls fusion in the noncentral elementary four-group.
The two outside involutions form one T-orbit, disjoint from the point class. -/
theorem extraspecial_four_controls_fusion
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G)) :
    (∀ x ∈ D, x ∉ F.Vi 1 → ∀ z ∈ F.Vi 1, ¬ IsConj x z) ∧
    (∀ x y : G, x ∈ D → y ∈ D → IsConj x y →
      ∃ m : F.H, (m : G) * x * (m : G)⁻¹ = y) := by
  have hZcard : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hHC : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    (extraspecial_source_14721 d h hab structural previous faithful earlier he).2.1.le
  have hm (x : G) (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
      ¬ (T : Subgroup G) ≤ centralizer ({x} : Set G) := by
    intro htx
    apply hnc
    apply le_centralizer_iff.mp
    have hC := four_point_centralizer D (F.Vi 1) F.H hcard hZcard hZD hHC
      ((Subgroup.centralizer_le_normalizer _).trans hND.le) hx hxZ
    exact (le_inf (F.invariant 1) htx).trans hC.le
  have hn (x : G) (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) (z : G) (hz : z ∈ F.Vi 1) :
      ¬ IsConj x z := by
    apply not_isConj_of_proper_sylow_centralizer T (hm x hx hxZ) ?_
      (extraspecial_four_centralizer_sylow d h hab structural previous faithful earlier he
        D hZD hDK hcard hDT hND hx hxZ).2.2.2.2.2
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hHC (F.invariant 1 ht) z hz).symm
  refine ⟨hn,?_⟩
  intro x y hx hy hxy
  by_cases hxZ : x ∈ F.Vi 1
  · have hyZ : y ∈ F.Vi 1 := by
      by_contra hyZ
      exact hn y hy hyZ x hxZ hxy.symm
    have heq : x = y := by
      by_cases hx1 : x = 1
      · exact hx1.trans ((isConj_one_right.mp (hx1 ▸ hxy)).symm)
      have hy1 : y ≠ 1 := fun hy1 => hx1 (isConj_one_left.mp (hy1 ▸ hxy))
      obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hZcard
      exact congrArg Subtype.val ((hz ⟨x,hxZ⟩ (fun hh => hx1 (congrArg Subtype.val hh))).trans
        (hz ⟨y,hyZ⟩ (fun hh => hy1 (congrArg Subtype.val hh))).symm)
    exact ⟨1,by simpa using heq⟩
  · have hyZ : y ∉ F.Vi 1 := fun hyZ => hn x hx hxZ y hyZ hxy
    obtain ⟨t,ht⟩ := four_outside_orbit (T : Subgroup G) D (F.Vi 1) hcard hZcard hZD
      ((F.invariant 1).trans hND.ge) (F.invariant 1) x y hx hxZ hy hyZ (hm x hx hxZ)
    exact ⟨⟨t,F.invariant 1 t.property⟩,ht⟩

private theorem four_centralizer_index (T D : Subgroup G) [IsElementaryAbelian 2 D]
    (hT : IsPGroup 2 T) (hDT : D ≤ T) (hn : T ≤ normalizer (D : Set G))
    (hD : Nat.card D = 4) (hnc : ¬ D ≤ centralizer (T : Set G)) :
    (T ⊓ centralizer (D : Set G)).relIndex T = 2 := by
  let E := D.subgroupOf T
  let : E.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.subgroupOf hDT
  have he : Nat.card E = 4 := (Nat.card_congr (subgroupOfEquivOfLe hDT).toEquiv).trans hD
  have hc : centralizer (E : Set T) = (centralizer (D : Set G)).subgroupOf T := by
    ext t
    constructor
    · intro ht x hx
      exact congrArg Subtype.val (ht ⟨x,hDT hx⟩ hx)
    · intro ht x hx
      exact Subtype.ext (ht x hx)
  have hb := centralizer_index_le_two_of_normal_four hT E he
  rw [hc] at hb
  have hne : (centralizer (D : Set G)).relIndex T ≠ 1 := fun hi =>
    hnc (le_centralizer_iff.mp (relIndex_eq_one.mp hi))
  have hz := ((centralizer (D : Set G)).subgroupOf T).index_ne_zero_of_finite
  rw [inf_relIndex_left]
  change ((centralizer (D : Set G)).subgroupOf T).index = 2
  change ((centralizer (D : Set G)).subgroupOf T).index ≠ 1 at hne
  omega

/-- The source outside centralizer has index two in the original T. -/
theorem extraspecial_four_centralizer_index
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G))
    {x : G} (hx : x ∈ D) (hxZ : x ∉ F.Vi 1) :
    ((T : Subgroup G) ⊓ centralizer ({x} : Set G)).relIndex (T : Subgroup G) = 2 := by
  have hHC : F.H ≤ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two _ (by simpa using F.card 1 (by decide))
  have hj := four_point_centralizer D (F.Vi 1) F.H hcard
    (by simpa using F.card 1 (by decide)) hZD hHC
    ((Subgroup.centralizer_le_normalizer _).trans hND.le) hx hxZ
  have heq : (T : Subgroup G) ⊓ centralizer ({x} : Set G) =
      (T : Subgroup G) ⊓ centralizer (D : Set G) := by
    rw [←hj,←inf_assoc,inf_eq_left.mpr (show (T : Subgroup G) ≤ F.H from F.invariant 1)]
  rw [heq]
  exact four_centralizer_index (T : Subgroup G) D T.isPGroup' hDT
    ((F.invariant 1).trans hND.ge) hcard hnc

/-- After the original Sylow and fusion deductions, precisely the outside
involution centralizers remain to prove the TI assertion of 14.7.26. -/
theorem extraspecial_four_ti_iff_centralizer_containment
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3))
    (D : Subgroup G) [IsElementaryAbelian 2 D]
    (hZD : F.Vi 1 ≤ D) (hDK : D ≤ (center (K F)).map (K F).subtype)
    (hcard : Nat.card D = 4) (hDT : D ≤ (T : Subgroup G))
    (hND : normalizer (D : Set G) = F.H) (hnc : ¬ D ≤ centralizer (T : Set G)) :
    IsTISubgroup D ↔
      ∀ x ∈ D, x ∉ F.Vi 1 → centralizer ({x} : Set G) ≤ F.H := by
  constructor
  · intro ht x hx hxZ
    exact (ht.centralizer_le_normalizer hx (fun he => hxZ (he ▸ (F.Vi 1).one_mem))).trans hND.le
  · intro hc
    apply lemma_I_6_1_1 D F.H hND.symm ?_ ?_
    · intro x hx hx1
      by_cases hxZ : x ∈ F.Vi 1
      · have hcardZ : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
        have hz : zpowers x = F.Vi 1 := by
          have heq := congrArg (fun A : Subgroup (F.Vi 1) => A.map (F.Vi 1).subtype)
            (zpowers_eq_top_of_prime_card hcardZ
              (show (⟨x,hxZ⟩ : F.Vi 1) ≠ 1 from fun he => hx1 (congrArg Subtype.val he)))
          simpa only [MonoidHom.map_zpowers,←MonoidHom.range_eq_map,range_subtype,Subgroup.coe_subtype] using heq
        have hC : centralizer ({x} : Set G) = centralizer (F.Vi 1 : Set G) := by
          rw [←hz,zpowers_eq_closure,centralizer_closure]
        rw [hC]
        exact Subgroup.centralizer_le_normalizer _
      · exact hc x hx hxZ
    · intro x y hx hy hconj
      exact (extraspecial_four_controls_fusion d h hab structural previous faithful earlier he
        D hZD hDK hcard hDT hND hnc).2 x y hx hy (isConj_iff.mpr hconj)

/-- Apply the noncentral four-group reductions to the subgroup selected from
14.7.25, without any additional local recognition premise. The remaining
centralizer-containment assertion is exposed as an equivalence, not assumed. -/
theorem extraspecial_center_four_fusion_reduction
    (d : Counterexample T L)
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (hab : IsMulCommutative F.U)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (previous : Chapter12.Section02.Theorem12213 KnownSimple.IsKnownSimple.{u})
    (faithful : EarlierFaithfulClassification G (T : Subgroup G))
    (earlier : ResidualNormalizer.LocalControl.Earlier14710.{u})
    (he : Nonempty (((K F) ⧸ pCore 2 (K F)) ≃* HeisenbergPrime 3)) :
    ∃ D : Subgroup G, F.Vi 1 ≤ D ∧ D ≤ (center (K F)).map (K F).subtype ∧
      Nat.card D = 4 ∧ D ≤ (T : Subgroup G) ∧ normalizer (D : Set G) = F.H ∧
      (IsTISubgroup D ∨ (IsElementaryAbelian 2 D ∧ ⁅D,(T : Subgroup G)⁆ = F.Vi 1 ∧
        (∀ x ∈ D, x ∉ F.Vi 1 →
          let J := F.H ⊓ centralizer ({x} : Set G)
          let S := (T : Subgroup G) ⊓ centralizer ({x} : Set G)
          J = centralizer (D : Set G) ∧ J ∈ He G ∧
            S.relIndex (T : Subgroup G) = 2 ∧
            normalizer ((center S).map S.subtype : Set G) = F.H ∧
            normalizer (S : Set G) ≤ F.H ∧
            ∃ P : Sylow 2 (centralizer ({x} : Set G)),
              (P : Subgroup (centralizer ({x} : Set G))).map
                (centralizer ({x} : Set G)).subtype = S) ∧
        (∀ x y : G, x ∈ D → y ∈ D → IsConj x y →
          ∃ m : F.H, (m : G) * x * (m : G)⁻¹ = y) ∧
        (IsTISubgroup D ↔ ∀ x ∈ D, x ∉ F.Vi 1 → centralizer ({x} : Set G) ≤ F.H))) := by
  obtain ⟨D,hZD,hDK,hcard,hDT,hND,hcases⟩ := extraspecial_center_four_ti_reduction
    d h hab structural previous faithful earlier he
  refine ⟨D,hZD,hDK,hcard,hDT,hND,?_⟩
  rcases hcases with ht | ⟨hele,hcomm,hnc⟩
  · exact Or.inl ht
  let := hele
  refine Or.inr ⟨hele,hcomm,?_,?_,?_⟩
  · intro x hx hxZ
    obtain ⟨hJ,hHe,hZ,hS,_,hP⟩ := extraspecial_four_centralizer_sylow
      d h hab structural previous faithful earlier he D hZD hDK hcard hDT hND hx hxZ
    exact ⟨hJ,hHe,extraspecial_four_centralizer_index D hZD hcard hDT hND hnc hx hxZ,hZ,hS,hP⟩
  · exact (extraspecial_four_controls_fusion d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc).2
  · exact extraspecial_four_ti_iff_centralizer_containment d h hab structural previous faithful earlier he
      D hZD hDK hcard hDT hND hnc


end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.SourceConstruction.LocalReduction
