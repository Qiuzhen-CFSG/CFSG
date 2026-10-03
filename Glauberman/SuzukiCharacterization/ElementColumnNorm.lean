module

public import Glauberman.SuzukiCharacterization.PrincipalColumnNorm
public import Glauberman.Theorem5_1
public import Theory.GroupTheory.SylowCentralizerConjugacy

open scoped BigOperators
open Subgroup ModularBlock PrincipalBlockConstruction CompatibleBrauerBlock
noncomputable section
namespace Glauberman.SuzukiCharacterization

variable {G : Type*} [Group G] [Finite G]

private theorem centralizer_sylow_card
    (P : Sylow 2 G) (h : Hypotheses P) (x : G)
    (hx : x ∈ (P : Subgroup G))
    (Q : Sylow 2 (Subgroup.centralizer ({x} : Set G)))
    (hCPQ : (Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P)).map
      (P : Subgroup G).subtype ≤
      (Q : Subgroup (Subgroup.centralizer ({x} : Set G))).map
        (Subgroup.centralizer ({x} : Set G)).subtype) :
    Nat.card Q =
      Nat.card (Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P)) := by
  let C : Subgroup G := Subgroup.centralizer ({x} : Set G)
  let CP : Subgroup P := Subgroup.centralizer ({(⟨x, hx⟩ : P)} : Set P)
  let CPg : Subgroup G := CP.map (P : Subgroup G).subtype
  have hCPg : CPg = (P : Subgroup G) ⊓ C := by
    exact Subgroup.map_subtype_centralizer_singleton P ⟨x, hx⟩
  have hCPp : IsPGroup 2 CPg := by
    rw [hCPg]
    exact P.isPGroup'.to_inf_left
  let Qg : Subgroup G := (Q : Subgroup C).map C.subtype
  have hQg : IsPGroup 2 Qg := IsPGroup.map (H := (Q : Subgroup C))
      Q.isPGroup' C.subtype
  have hCPQg : CPg ≤ Qg := by
    intro y hy
    exact hCPQ hy
  have hQcentral : Qg ≤ C := by
    intro y hy
    rcases Subgroup.mem_map.mp hy with ⟨z, hz, rfl⟩
    exact z.property
  have hQnorm : Qg ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    apply hQcentral.trans
    apply (show C ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer (Subgroup.zpowers x : Set G))
    rw [Subgroup.le_centralizer_iff]
    rw [Subgroup.zpowers_le]
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mp hz
  have hxp : IsPGroup 2 (Subgroup.zpowers x) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_pow_pow_eq_one ⟨x, hx⟩
    exact IsPGroup.of_card_dvd_pow (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn))
  have hsup : IsPGroup 2 (Qg ⊔ Subgroup.zpowers x : Subgroup G) :=
    hQg.to_sup_of_normal_right' hxp hQnorm
  obtain ⟨S, hsupS⟩ := hsup.exists_le_sylow
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq G S P
  have haxP : a * x * a⁻¹ ∈ (P : Subgroup G) := by
    rw [← ha, sylow_smul_subgroup_eq_map_conj]
    exact Subgroup.mem_map.mpr
      ⟨x, hsupS ((le_sup_right : Subgroup.zpowers x ≤ Qg ⊔ Subgroup.zpowers x) (mem_zpowers x)), rfl⟩
  obtain ⟨n, hnP, hnx⟩ := h.fusion x hx _ haxP (isConj_iff.mpr ⟨a, rfl⟩)
  let c : G := n⁻¹ * a
  have hcx : c * x * c⁻¹ = x := by
    dsimp [c]
    rw [mul_inv_rev, inv_inv]
    change n⁻¹ * a * x * (a⁻¹ * n) = x
    calc
      n⁻¹ * a * x * (a⁻¹ * n) = n⁻¹ * (a * x * a⁻¹) * n := by group
      _ = n⁻¹ * (n * x * n⁻¹) * n := by rw [hnx]
      _ = x := by group
  let Q' : Subgroup G := Qg.map (MulAut.conj c).toMonoidHom
  have hQ'le : Q' ≤ CPg := by
    rw [hCPg]
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    have hza : a * z * a⁻¹ ∈ (P : Subgroup G) := by
      rw [← ha, sylow_smul_subgroup_eq_map_conj]
      exact Subgroup.mem_map.mpr ⟨z, hsupS ((le_sup_left : Qg ≤ Qg ⊔ Subgroup.zpowers x) hz), rfl⟩
    have hcz : c * z * c⁻¹ ∈ (P : Subgroup G) := by
      simpa [c, mul_assoc] using
        (Subgroup.mem_normalizer_iff.mp (inv_mem hnP) (a * z * a⁻¹)).mp hza
    refine ⟨hcz, ?_⟩
    have hcomm : z * x = x * z :=
      Subgroup.mem_centralizer_singleton_iff.mp (hQcentral hz)
    have hcomm' : (MulAut.conj c) z * (MulAut.conj c) x =
        (MulAut.conj c) x * (MulAut.conj c) z := by
      simpa only [map_mul] using congrArg (MulAut.conj c) hcomm
    change (MulAut.conj c) z ∈ C
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa [MulAut.conj_apply, hcx] using hcomm')
  have hcardQ' : Nat.card Q' = Nat.card Qg :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hcardQg : Nat.card Qg = Nat.card Q :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hle1 : Nat.card Q ≤ Nat.card CPg := by
    rw [← hcardQg, ← hcardQ']
    exact Nat.card_le_card_of_injective
      (fun y : Q' => ⟨y, hQ'le y.property⟩)
      (fun _ _ hxy => by simpa using hxy)
  have hle2 : Nat.card CPg ≤ Nat.card Qg := by
    exact Nat.card_le_card_of_injective
      (fun y : CPg => ⟨y, hCPQg y.property⟩)
      (fun _ _ hxy => by simpa using hxy)
  have hcard : Nat.card Q = Nat.card CPg := le_antisymm hle1 (hle2.trans_eq hcardQg)
  rw [hcard, Subgroup.card_map_of_injective Subtype.coe_injective]

/-- The nonidentity principal-block column norm is the centralizer order in P. -/
public theorem Hypotheses.principalBlock_column_norm
    (P : Sylow 2 G) (h : Hypotheses P) (d : PrincipalCongruenceBlockData G)
    (x : P) (hx : x ≠ 1) :
    ∑ i ∈ d.block, d.chi i (ConjClasses.mk (x : G)) *
      star (d.chi i (ConjClasses.mk (x : G))) =
        (Nat.card (Subgroup.centralizer ({x} : Set P)) : ℂ) := by
  let C := Subgroup.centralizer ({(x : G)} : Set G)
  obtain ⟨N, hN, hodd, hquot⟩ := h.centralizer_hasNormalPComplement P (x : G)
    x.property (by
      intro he
      exact hx (Subtype.ext he))
  let := hN
  let CP : Subgroup P := Subgroup.centralizer ({x} : Set P)
  let CPg : Subgroup G := CP.map (P : Subgroup G).subtype
  have hCPgC : CPg ≤ C := by
    simpa [CPg, C] using (show CP.map (P : Subgroup G).subtype ≤ C from by
      intro y hy
      rw [Subgroup.map_subtype_centralizer_singleton] at hy
      exact hy.2)
  have hCPp : IsPGroup 2 CPg := by
    exact IsPGroup.map (H := CP) (P.isPGroup'.to_subgroup CP)
      (P : Subgroup G).subtype
  let H : Subgroup C := CPg.subgroupOf C
  obtain ⟨Q, hHQ⟩ := hCPp.of_equiv (Subgroup.subgroupOfEquivOfLe hCPgC).symm |>.exists_le_sylow
  have hCPQ : CPg ≤ (Q : Subgroup C).map C.subtype := by
    intro y hy
    refine Subgroup.mem_map.mpr ⟨⟨y, hCPgC hy⟩, ?_, rfl⟩
    exact hHQ (show ⟨y, hCPgC hy⟩ ∈ H by exact hy)
  have hcard : Nat.card Q = Nat.card (Subgroup.centralizer ({x} : Set P)) := by
    exact centralizer_sylow_card P h (x : G) x.property Q hCPQ
  rw [LocalColumnNorm.principalBlock_local_column_norm d (x : G) (by
      obtain ⟨n, hn⟩ := P.isPGroup'.exists_pow_pow_eq_one x
      exact ⟨n, congrArg Subtype.val hn⟩),
    NormalComplementDegree.sum_degree_sq_eq_sylow_card (localData d C) Q N
      hodd hquot, hcard]

end Glauberman.SuzukiCharacterization
