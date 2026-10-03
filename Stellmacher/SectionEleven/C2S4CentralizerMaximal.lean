module

public import Stellmacher.SectionFiveToSeven.Defs
public import Stellmacher.LaterDefs
public import Theory.GroupTheory.SymmetricFourModelCoreData

/-!
# Centralizer rigidity and maximal two-locality in Section 11

If Q is a p-subgroup and R a normal p-subgroup, the normalizer condition
in QR forces R into Q whenever R ∩ N(Q) ≤ Q. Apply this with R the core
of an overgroup of P and Q the abelian core of P. Characteristic p then
forces Q = R, so the overgroup normalizes Q and equals P.

For a Hypothesis Two pair with `P1 ≃ C₂ × S₄` and
`N_H(O₂(P1)) = P1`, the model-core theorem supplies the abelian core.
Every two-local overgroup contains `baumannIn S`, so `h.local_B` makes
it characteristic two and the preceding argument makes it equal to `P1`.
Thus maximality is proved separately from centralizer rigidity. The model's
center has order two; its normalizer is consequently two-local and contains
`P1`. Maximality identifies this normalizer with `P1`, and sandwiching the
center's centralizer proves the required equality.

This proves the local centralizer assertion and the explicit maximality
needed for alternative (c) in Stellmacher Section 11, case (II),
`refs/latex/stellmacher-n-group.tex`, lines 2092–2096. The non-Sylow
hypothesis is retained for the terminal interface, although this local
argument does not need it. No global characteristic-two assumption is used.
-/

private theorem normal_pSubgroup_le_of_normalizer_inf_le
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (Q R : Subgroup G) [R.Normal]
    (hQ : IsPGroup p Q) (hR : IsPGroup p R)
    (hInf : R ⊓ Subgroup.normalizer (Q : Set G) ≤ Q) : R ≤ Q := by
  let T := Q ⊔ R
  have hQT : Q ≤ T := le_sup_left
  have hT : IsPGroup p T := hQ.to_sup_of_normal_right hR
  let _ : Group.IsNilpotent T := hT.isNilpotent
  have htop : Q.subgroupOf T = ⊤ := by
    by_contra hproper
    have hlt := Group.normalizerCondition_of_isNilpotent
      (Q.subgroupOf T) (lt_top_iff_ne_top.mpr hproper)
    obtain ⟨element, hnorm, hnot⟩ := SetLike.exists_of_lt hlt
    rw [← Subgroup.subgroupOf_normalizer_eq hQT] at hnorm
    have hnormG : (element : G) ∈ Subgroup.normalizer (Q : Set G) := hnorm
    obtain ⟨left, hleft, right, hright, heq⟩ :=
      Subgroup.mem_sup_of_normal_right.mp element.property
    have hrightNorm : right ∈ Subgroup.normalizer (Q : Set G) := by
      have hmem := (Subgroup.normalizer (Q : Set G)).mul_mem
        ((Subgroup.normalizer (Q : Set G)).inv_mem (Subgroup.le_normalizer hleft))
        hnormG
      rw [← heq] at hmem
      simpa using hmem
    apply hnot
    change (element : G) ∈ Q
    rw [← heq]
    exact Q.mul_mem hleft (hInf ⟨hright, hrightNorm⟩)
  exact le_sup_right.trans (Subgroup.subgroupOf_eq_top.mp htop)

namespace Stellmacher.SectionEleven

open SectionsFiveToSeven

private theorem abelian_core_overgroup_eq
    {H : Type*} [Group H] [Finite H] (P U : Subgroup H)
    (hPU : P ≤ U) (hcomm : IsMulCommutative (pCore 2 P))
    (hnorm : Subgroup.normalizer (twoCoreIn P : Set H) = P)
    (hchar : IsCharacteristicTwoType U) : U = P := by
  let Q := twoCoreIn P
  let R := twoCoreIn U
  have hQP : Q ≤ P := Subgroup.map_subtype_le _
  have hQU : Q ≤ U := hQP.trans hPU
  have hRU : R ≤ U := Subgroup.map_subtype_le _
  have hRnormal : (R.subgroupOf U).Normal := by
    change (Subgroup.comap U.subtype ((pCore 2 U).map U.subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective U.subtype_injective]
    infer_instance
  have hUnorm : U ≤ Subgroup.normalizer (R : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRU).mp hRnormal
  have hRPnormal : (R.subgroupOf P).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hPU.trans hUnorm)
  have hRp : IsPGroup 2 R := pCore_isPGroup.map U.subtype
  have hRPcore : R.subgroupOf P ≤ pCore 2 P :=
    le_sSup ⟨hRPnormal, hRp.comap_subtype⟩
  have hRle : pCore 2 U ≤ Q.subgroupOf U := by
    apply normal_pSubgroup_le_of_normalizer_inf_le (Q.subgroupOf U) (pCore 2 U)
      ((pCore_isPGroup.map P.subtype).comap_subtype) pCore_isPGroup
    intro element helement
    have hnormU := helement.2
    rw [← Subgroup.subgroupOf_normalizer_eq hQU] at hnormU
    have helementP : (element : H) ∈ P := hnorm ▸ hnormU
    have helementR : (element : H) ∈ R :=
      Subgroup.mem_map_of_mem U.subtype helement.1
    exact Subgroup.mem_map_of_mem P.subtype
      (hRPcore (show (⟨element, helementP⟩ : P) ∈ R.subgroupOf P from helementR))
  let _ : IsMulCommutative (pCore 2 P) := hcomm
  let _ : IsMulCommutative Q := Subgroup.map_isMulCommutative (pCore 2 P) P.subtype
  let _ : CommGroup Q := IsMulCommutative.instCommGroup
  have hQle : Q.subgroupOf U ≤ pCore 2 U := by
    intro element helement
    apply hchar
    rw [Subgroup.mem_centralizer_iff]
    intro core hcore
    apply Subtype.ext
    exact congrArg (fun value : Q => (value : H))
      (mul_comm (⟨core, hRle hcore⟩ : Q) ⟨element, helement⟩)
  have heq : Q.subgroupOf U = pCore 2 U := le_antisymm hQle hRle
  have hQnormal : (Q.subgroupOf U).Normal := heq ▸ inferInstance
  apply le_antisymm _ hPU
  have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hQU).mp hQnormal
  exact hnorm ▸ hle

private theorem c2s4_center_card {H : Type*} [Group H] (P : Subgroup H)
    (hModel : Later.IsModel P (Later.C2 × Later.S4)) :
    Nat.card (Subgroup.center P) = 2 := by
  obtain ⟨model⟩ := hModel
  rw [Nat.card_congr (Subgroup.centerCongr model).toEquiv, Nat.card_eq_fintype_card]
  decide

public theorem c2s4_centralizer_maximal
    {H : Type*} [Group H] [Finite H]
    (S0 : Sylow 2 H) (S P1 P2 : Subgroup H)
    (h : HypothesisTwo H S0 S P1 P2)
    (_hne : S ≠ (S0 : Subgroup H))
    (hModel : Later.IsModel P1 (Later.C2 × Later.S4))
    (hNormalizer : Subgroup.normalizer (twoCoreIn P1 : Set H) = P1) :
    Subgroup.centralizer (((Subgroup.center P1).map P1.subtype) : Set H) = P1 ∧
      IsMaximalTwoLocal P1 := by
  let _ : IsElementaryAbelian 2 (pCore 2 P1) :=
    (symmetric_four_model_twoCore_data (K := P1) (Or.inr hModel)).1
  have hCore : IsMulCommutative (pCore 2 P1) := inferInstance
  have hSP : S ≤ P1 := h.fiveOne.P1_mem.1.2.1.1
  have hBP : baumannIn S ≤ P1 := inf_le_left.trans hSP
  have hPtwo : IsTwoLocal P1 := ⟨twoCoreIn P1,
    h.fiveOne.P1_mem.1.2.2.1, pCore_isPGroup.map P1.subtype, hNormalizer.symm⟩
  have hMax : IsMaximalTwoLocal P1 := by
    refine ⟨hPtwo, ?_⟩
    intro U hU hPU
    exact (abelian_core_overgroup_eq P1 U hPU hCore hNormalizer
      (h.local_B U hU (hBP.trans hPU)).2).le
  let Z := (Subgroup.center P1).map P1.subtype
  have hZcard : Nat.card Z = 2 :=
    (Subgroup.card_map_of_injective P1.subtype_injective).trans
      (c2s4_center_card P1 hModel)
  have hZne : Z ≠ ⊥ := by
    intro hbot
    simp [hbot] at hZcard
  have hZp : IsPGroup 2 Z := IsPGroup.of_card (n := 1) (by simpa using hZcard)
  have hPC : P1 ≤ Subgroup.centralizer (Z : Set H) := by
    intro element helement
    rw [Subgroup.mem_centralizer_iff]
    rintro center ⟨preimage, hpreimage, rfl⟩
    exact congrArg (fun value : P1 => (value : H))
      (Subgroup.mem_center_iff.mp hpreimage ⟨element, helement⟩).symm
  have hNP : Subgroup.normalizer (Z : Set H) ≤ P1 :=
    hMax.2 ⟨Z, hZne, hZp, rfl⟩
      (hPC.trans (Subgroup.centralizer_le_normalizer _))
  exact ⟨le_antisymm ((Subgroup.centralizer_le_normalizer _).trans hNP) hPC, hMax⟩

end Stellmacher.SectionEleven
