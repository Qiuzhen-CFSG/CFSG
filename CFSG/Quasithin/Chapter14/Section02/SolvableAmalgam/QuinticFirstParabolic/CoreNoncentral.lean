module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.AlgebraicLowerBound
public import Theory.GroupTheory.CentralBinaryAbelianBound
public import Theory.GroupTheory.ConjugateIntersectionAbelianBound
public import Theory.GroupTheory.AmalgamLocalCores
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Abelian bounds and crossing cores in the original quintic branch

Put Q=O₂(H), U=⟨Vᴴ⟩, Z=Ω₁Z(T), and C=C_H(U). The original relation
[Q,U]≤Z and binary commutator duality bound every abelian subgroup
of Q by |C|. Since 16|C|≤|Q| and the cubic parabolic X has order at
most 12|Q|, every Q∩Qˣ with x∈X is nonabelian.

If [Q,Q]≤Z, the derived subgroup of each intersection identifies the
prime-order groups Z and Zˣ. Thus X would normalize Z, contradicting
the trivial common core of X and H. Hence [Q,Q]≰Z in both the D₁₀
and Sz(2) rows, without a core-order bound or path-transitivity premise.
`IntrinsicCore` uses this obstruction in its class-three proof. Bounding
the large radius-two kernel remains with qt-e-quintic-first-parabolic.

Source: Aschbacher--Smith F.9.7, printed p.321, and14.2.6,14.2.20--21,
printed pp.982,988--989. All subgroups retain their ambient embeddings.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The actual span centralizer bounds every abelian subgroup of the
original core, with no extra order or commutator hypothesis. -/
theorem source_core_abelian_le_span_centralizer
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)

    (A : Subgroup G) [IsMulCommutative A] (hAQ : A ≤ H.pCoreIn 2) :
    Nat.card A ≤ Nat.card (H ⊓ centralizer (conjugateSpanBy (localModule T M) H : Set G) : Subgroup G) := by
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let Z := centralInvolutions T
  let C := H ⊓ centralizer (U : Set G)
  let : IsElementaryAbelian 2 U :=
    (source_index_five_closure_structure hG T hempty hM hu hmany hcard e H hH.1 hi).1
  obtain ⟨he,F,hp,_,_,hloc⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨_,hlocal,_,_,_,_⟩ := hloc H hH.1
  have hUQ : U ≤ Q := by
    have hh := hlocal.U_le_core
    change conjugateSpanBy (rankTwoSeed T M) H ≤ H.pCoreIn 2 at hh
    simpa only [rankTwoSeed_eq_localModule] using hh
  have hc : ⁅U,Q⁆ ≤ Z := by
    have hh := hlocal.commutator_U_core_le_point
    change ⁅conjugateSpanBy (rankTwoSeed T M) H,H.pCoreIn 2⁆ ≤ F.Vi 1 at hh
    simpa only [rankTwoSeed_eq_localModule,hp] using hh
  have hZU : Z ≤ U := (le_conjugateSpanBy _ _).trans (le_conjugateSpanBy _ _)
  have hZQ : Z ≤ Q := hZU.trans hUQ
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  let UQ := U.subgroupOf Q
  let ZQ := Z.subgroupOf Q
  let AQ := A.subgroupOf Q
  let : IsElementaryAbelian 2 UQ := IsElementaryAbelian.subgroupOf hUQ
  let : UQ.Normal := normal_subgroupOf_of_le_normalizer
    ((pCoreIn_le 2 H).trans (le_normalizer_conjugateSpanBy _ _))
  let : IsMulCommutative AQ := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (setLike_mul_comm (s := A) a.property b.property))⟩⟩
  have hz : ZQ ≤ center Q := by
    intro z hz
    apply mem_center_iff.mpr
    intro q
    exact Subtype.ext ((mem_centralizer_iff.mp (hHZ (pCoreIn_le 2 H q.property)) _ hz).symm)
  have hzc : Nat.card ZQ = 2 :=
    (Nat.card_congr (subgroupOfEquivOfLe hZQ).toEquiv).trans
      (plane_centralInvolutions_card T M hM.1.2 hcard e)
  have hcomm : ⁅UQ,(⊤ : Subgroup Q)⁆ ≤ ZQ := by
    apply commutator_le.mpr
    intro u hu q _
    exact hc (commutator_mem_commutator hu q.property)
  have hb := card_abelian_le_centralizer_of_central_binary_commutators
    UQ AQ ZQ (fun _ hz => hZU hz) hz hzc hcomm
  rw [Nat.card_congr (subgroupOfEquivOfLe hAQ).toEquiv] at hb
  have hCle : (centralizer (UQ : Set Q)).map Q.subtype ≤ C := by
    rintro q ⟨a,ha,rfl⟩
    refine ⟨pCoreIn_le 2 H a.property,?_⟩
    intro u hu
    exact congrArg Q.subtype (ha ⟨u,hUQ hu⟩ hu)
  have hbc := card_le_of_le hCle
  rw [card_map_of_injective Q.subtype_injective] at hbc
  exact hb.trans hbc

/-- Every intersection of the original core with a cubic conjugate is
nonabelian. The conjugation map and cubic parabolic are literal. -/
theorem source_core_crossing_intersection_nonabelian
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)

    (x : G) (hx : x ∈ sourceResidual M Mc ⊔ (T : Subgroup G)) :
    ¬ IsMulCommutative (H.pCoreIn 2 ⊓ (H.pCoreIn 2).map (MulAut.conj x).toMonoidHom : Subgroup G) := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let U := conjugateSpanBy (localModule T M) H
  let C := H ⊓ centralizer (U : Set G)
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hQT : Q ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTH] using
      pCoreIn_le_sylow H (T.subtype hTH)
  have hqcard : Nat.card Q = Nat.card (pCore 2 H) := card_map_of_injective H.subtype_injective
  have hlower : 16 * Nat.card C ≤ Nat.card Q := by
    rw [hqcard]
    exact source_quintic_action_core_lower hG T hempty hM hu hmany hcard e H hH hi
  have hTbound : Nat.card (T : Subgroup G) ≤ 4 * Nat.card Q := by
    have ht := ((T : Subgroup G).subgroupOf H).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv] at ht
    change (T : Subgroup G).relIndex H * Nat.card (T : Subgroup G) = Nat.card H at ht
    rw [hi] at ht
    have hc := (pCore 2 H).index_mul_card
    change Nat.card (H ⧸ pCore 2 H) * Nat.card (pCore 2 H) = Nat.card H at hc
    rw [←hqcard] at hc
    rcases source_index_five_models hG T hempty hM hu hmany hcard e H hH.1 hi with hD | hS
    · have hm : Nat.card (H ⧸ pCore 2 H) = 10 :=
        (Nat.card_congr hD.some.toEquiv).trans DihedralGroup.nat_card
      rw [hm] at hc
      omega
    · have hm : Nat.card (H ⧸ pCore 2 H) = 20 :=
        (Nat.card_congr hS.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
      rw [hm] at hc
      omega
  obtain ⟨_,⟨eX⟩⟩ := source_residualSylow_quotient hG T hempty hM hu hmany hcard e
  have hXbound : Nat.card X ≤ 12 * Nat.card Q := by
    have hc := ((T : Subgroup G).subgroupOf X).index_mul_card
    have hiX := SymmetricThreeTwoCore.sylow_index_three eX (T.subtype hTX)
    change ((T : Subgroup G).subgroupOf X).index = 3 at hiX
    rw [hiX,Nat.card_congr (subgroupOfEquivOfLe hTX).toEquiv] at hc
    omega
  let f := (MulAut.conj x).toMonoidHom
  let Qx := Q.map f
  let K := Q ⊓ Qx
  have hQX : Q ≤ X := hQT.trans hTX
  have hQxX : Qx ≤ X := by
    rintro _ ⟨q,hq,rfl⟩
    exact X.mul_mem (X.mul_mem hx (hQX hq)) (X.inv_mem hx)
  have hQxcard : Nat.card Qx = Nat.card Q :=
    card_map_of_injective (MulAut.conj x).injective
  have hKcard : Nat.card Q * Nat.card Q ≤ Nat.card X * Nat.card K := by
    have hir : K.relIndex Q ≤ Qx.relIndex X := by
      change (Q ⊓ Qx).relIndex Q ≤ _
      rw [inf_relIndex_left]
      exact relIndex_le_of_le_right hQX index_ne_zero_of_finite
    have hk := (K.subgroupOf Q).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show K ≤ Q from inf_le_left)).toEquiv] at hk
    change K.relIndex Q * Nat.card K = Nat.card Q at hk
    have hX := (Qx.subgroupOf X).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hQxX).toEquiv,hQxcard] at hX
    change Qx.relIndex X * Nat.card Q = Nat.card X at hX
    calc
      Nat.card Q * Nat.card Q = (K.relIndex Q * Nat.card K) * Nat.card Q := by rw [hk]
      _ ≤ (Qx.relIndex X * Nat.card K) * Nat.card Q :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hir)
      _ = (Qx.relIndex X * Nat.card Q) * Nat.card K := by ring
      _ = _ := by rw [hX]
  intro hab
  let : IsMulCommutative K := hab
  have hb : Nat.card K ≤ Nat.card C :=
    source_core_abelian_le_span_centralizer hG T hempty hM hu hmany hcard e H hH hi K inf_le_left
  have horder : Nat.card X * Nat.card C < Nat.card Q * Nat.card Q := by
    have hcpos : 0 < Nat.card C := Nat.card_pos
    have hqpos : 0 < Nat.card Q := Nat.card_pos
    have h1 := Nat.mul_le_mul_right (Nat.card C) hXbound
    have h2 := Nat.mul_le_mul_left (Nat.card Q) hlower
    nlinarith
  exact (Nat.not_lt_of_ge (hKcard.trans (Nat.mul_le_mul_left _ hb))) horder

/-- The original core commutator is not contained in the central involution;
no core order or endpoint identification is assumed. -/
theorem source_core_derived_not_le_point
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
 :
    ¬ ⁅H.pCoreIn 2,H.pCoreIn 2⁆ ≤ centralInvolutions T := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let Q := H.pCoreIn 2
  let Z := centralInvolutions T
  have hTX : (T : Subgroup G) ≤ X := le_sup_right
  have hTH : (T : Subgroup G) ≤ H := hH.1.1.2
  have hZcard : Nat.card Z = 2 := plane_centralInvolutions_card T M hM.1.2 hcard e
  have hHZ : H ≤ centralizer (Z : Set G) :=
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  intro hder
  have hnX : X ≤ normalizer (Z : Set G) := by
    intro x hx
    let f := (MulAut.conj x).toMonoidHom
    let Qx := Q.map f
    let K := Q ⊓ Qx
    have hn : ⁅K,K⁆ ≠ ⊥ := fun he =>
      source_core_crossing_intersection_nonabelian hG T hempty hM hu hmany hcard e H hH hi x hx
        (commutator_self_eq_bot_iff.mp he)
    have hKZ : ⁅K,K⁆ ≤ Z := (commutator_mono inf_le_left inf_le_left).trans hder
    have hKeq : ⁅K,K⁆ = Z := by
      apply eq_of_le_of_card_ge hKZ
      have hd := card_dvd_of_le hKZ
      have hprime : Nat.Prime (Nat.card Z) := by rw [hZcard]; decide
      rcases hprime.eq_one_or_self_of_dvd _ hd with hone | heq
      · exact (hn (card_eq_one.mp hone)).elim
      · exact heq.ge
    have hKZx : ⁅K,K⁆ ≤ Z.map f := by
      apply (commutator_mono (show K ≤ Qx from inf_le_right) inf_le_right).trans
      change ⁅Q.map f,Q.map f⁆ ≤ Z.map f
      rw [← map_commutator]
      exact map_mono hder
    have hZZx : Z ≤ Z.map f := hKeq ▸ hKZx
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact (eq_of_le_of_card_ge hZZx (by rw [card_map_of_injective (MulAut.conj x).injective])).symm
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hXH : X ∈ Chapter1.HOver G (T : Set G) :=
    Chapter3.mem_HOver_of_sylow_interval T hTX hXM
      ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  have hcX : centralizer (pCore 2 X : Set X) ≤ pCore 2 X :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hXH)
  have hcore : pCore 2 (X ⊔ H : Subgroup G) = ⊥ := by
    let d : (X ⊔ H : Subgroup G) ≃* (H ⊔ X : Subgroup G) :=
      MulEquiv.subgroupCongr (sup_comm X H)
    apply (map_eq_bot_iff_of_injective _ (f := d.toMonoidHom) d.injective).mp
    rw [pCore_map_iso]
    exact source_solvable_amalgam_twoCore_eq_bot hG T hempty hM hu hmany hcard e H hH.1.2
  have hb := AmalgamLocalCores.common_normal_eq_bot X H Z
    (le_inf ((centralInvolutions_le_sylow T).trans hTX)
      ((centralInvolutions_le_sylow T).trans hTH))
    hnX (hHZ.trans (_root_.centralizer_le_normalizer _)) hcore hcX
  rw [hb,card_bot] at hZcard
  omega

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
