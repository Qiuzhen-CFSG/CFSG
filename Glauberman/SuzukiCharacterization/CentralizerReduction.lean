module

public import Glauberman.SuzukiCharacterization.Hypotheses
public import FeitThompson.BGsection1.PLengthLemmas
public import FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import Theory.GroupTheory.SylowCentralizerConjugacy

/-!
# Reducing Suzuki centralizer containment to odd-subgroup exclusion

A normal two-complement in an involution centralizer also controls the
centralizers of elements having that involution as a power. Element fusion
then places every two-group centralizer back in the specified Sylow subgroup.

If P normalizes no nontrivial odd-order subgroup, each nonidentity central
element of P has centralizer P. A noncyclic center acts on the odd complement
of any other element centralizer. Coprime fixed-point generation makes that
complement trivial, proving containment.

This is the group-theoretic completion of Glauberman, *A Characterization
of the Suzuki Groups* (1968), p. 92; the paper is saved in
`refs/original/n-group-global/odd-core-rank-two-source/`. The two substantive
inputs, noncyclicity of the center and odd-subgroup exclusion, remain explicit.
-/

open Subgroup
open scoped IsMulCommutative
namespace Glauberman.SuzukiCharacterization
/-- Every nonidentity Sylow element has a centralizer with a normal two-complement. -/
public theorem Hypotheses.centralizer_hasNormalPComplement {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P) (x : G)
    (hx : x ∈ (P : Subgroup G)) (hne : x ≠ 1) :
    HasNormalPComplement 2 (Subgroup.centralizer ({x} : Set G)) := by
  let y := x ^ (orderOf x / 2)
  have hdiv : 2 ∣ orderOf x := by
    simpa using P.isPGroup'.dvd_orderOf (g := ⟨x, hx⟩)
      (fun he => hne (congrArg Subtype.val he))
  have hy : orderOf y = 2 := orderOf_pow_orderOf_div (orderOf_pos x).ne' hdiv
  apply hasNormalPComplement_of_le 2 (L := Subgroup.centralizer ({y} : Set G))
    (fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr
      (Commute.pow_right (show Commute g x from Subgroup.mem_centralizer_singleton_iff.mp hg) _).eq)
  exact h.involution_complement y ((P : Subgroup G).pow_mem hx _) hy


/-- Element fusion places a two-group centralizer in the specified Sylow subgroup. -/
public theorem Hypotheses.centralizer_le_of_isPGroup {G : Type*} [Group G] [Finite G]
    (P : Sylow 2 G) (h : Hypotheses P) (x : G)
    (hx : x ∈ (P : Subgroup G))
    (hc : IsPGroup 2 (centralizer ({x} : Set G))) :
    centralizer ({x} : Set G) ≤ (P : Subgroup G) := by
  obtain ⟨a, ha, _⟩ := exists_conj_centralizer_le_sylow P x hc
  have hax : a * x * a⁻¹ ∈ (P : Subgroup G) :=
    ha (mem_centralizer_singleton_iff.mpr rfl)
  obtain ⟨n, hn, hnax⟩ := h.fusion x hx _ hax (isConj_iff.mpr ⟨a, rfl⟩)
  intro y hy
  have hny : n * y * n⁻¹ ∈ (P : Subgroup G) := by
    apply ha
    rw [← hnax]
    exact mem_centralizer_singleton_iff.mpr
      (by simpa only [map_mul, MulAut.conj_apply] using
        congrArg (MulAut.conj n) (mem_centralizer_singleton_iff.mp hy))
  exact (mem_normalizer_iff.mp hn y).mpr hny

/-- Odd-subgroup exclusion makes central Sylow elements self-centralizing in P. -/
public theorem Hypotheses.centralizer_eq_of_no_normalized_odd_subgroup
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P)
    (hodd : ∀ H : Subgroup G, Nat.Coprime 2 (Nat.card H) →
      (P : Subgroup G) ≤ normalizer (H : Set G) → H = ⊥)
    (z : Subgroup.center P) (hz : z ≠ 1) :
    centralizer ({((z : P) : G)} : Set G) = (P : Subgroup G) := by
  let C := centralizer ({((z : P) : G)} : Set G)
  have hPC : (P : Subgroup G) ≤ C := by
    intro p hp
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_center_iff.mp z.property ⟨p, hp⟩))
  have hzG : ((z : P) : G) ≠ 1 := fun he => hz (Subtype.ext (Subtype.ext he))
  obtain ⟨N, hN, hcop, hquot⟩ := h.centralizer_hasNormalPComplement P _ (z : P).property hzG
  let := hN
  have hCN : C ≤ normalizer ((N.map C.subtype : Subgroup G) : Set G) := by
    intro c hc
    exact N.le_normalizer_map C.subtype ⟨⟨c, hc⟩, N.normalizer_eq_top ▸ mem_top _, rfl⟩
  have hNbot : N = ⊥ := by
    apply Subgroup.map_injective C.subtype_injective
    rw [Subgroup.map_bot]
    exact hodd (N.map C.subtype)
      (hcop.of_dvd_right (card_map_dvd N C.subtype)) (hPC.trans hCN)
  subst N
  have hCp : IsPGroup 2 C := hquot.of_equiv QuotientGroup.quotientBot
  exact P.is_maximal' hCp hPC

/-- The group-theoretic completion of Theorem 4.1(v), with its two structural inputs. -/
public theorem Hypotheses.centralizer_le_of_noncyclic_center_of_no_normalized_odd_subgroup
    {G : Type*} [Group G] [Finite G] (P : Sylow 2 G) (h : Hypotheses P)
    (hncyc : ¬ IsCyclic (Subgroup.center P))
    (hodd : ∀ H : Subgroup G, Nat.Coprime 2 (Nat.card H) →
      (P : Subgroup G) ≤ normalizer (H : Set G) → H = ⊥)
    (x : G) (hx : x ∈ (P : Subgroup G)) (hne : x ≠ 1) :
    centralizer ({x} : Set G) ≤ (P : Subgroup G) := by
  let C := centralizer ({x} : Set G)
  obtain ⟨N, hN, hcop, hquot⟩ := h.centralizer_hasNormalPComplement P x hx hne
  let := hN
  let Z := Subgroup.center P
  let f : Z →* C :=
    { toFun := fun z => ⟨((z : P) : G), mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_center_iff.mp z.property ⟨x, hx⟩)).symm⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let act : Z →* MulAut N := (MulAut.conjNormal : C →* MulAut N).comp f
  let : MulDistribMulAction Z N := MulDistribMulAction.compHom N act
  let : Fact (IsPGroup 2 Z) := ⟨P.isPGroup'.to_subgroup Z⟩
  have hgen := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := N) (A := Z) 2 hcop hncyc
  have hNbot : N = ⊥ := by
    have hall : (⊤ : Subgroup N) ≤ ⊥ := by
      rw [← hgen]
      refine iSup₂_le fun z hz => ?_
      intro n hn
      have hfix := (show ∀ a : zpowers z, a • n = n from hn) ⟨z, mem_zpowers z⟩
      have hcomm : ((n : C) : G) * ((z : P) : G) =
          ((z : P) : G) * ((n : C) : G) := by
        have he : ((z : P) : G) * ((n : C) : G) * ((z : P) : G)⁻¹ = ((n : C) : G) :=
          congrArg (fun n : N => ((n : C) : G)) hfix
        exact (mul_inv_eq_iff_eq_mul.mp he).symm
      have hnP : ((n : C) : G) ∈ (P : Subgroup G) := by
        rw [← h.centralizer_eq_of_no_normalized_odd_subgroup P hodd z hz]
        exact mem_centralizer_singleton_iff.mpr hcomm
      have hdiv : orderOf n ∣ Nat.card N := orderOf_dvd_natCard n
      have hpow : ∃ k, orderOf n = 2 ^ k := by
        simpa using P.isPGroup'.exists_orderOf_eq_pow ⟨((n : C) : G), hnP⟩
      obtain ⟨k, hk⟩ := hpow
      have hord : orderOf n = 1 := Nat.eq_one_of_dvd_coprimes
        (hcop.pow_left k) (by rw [hk]) hdiv
      exact mem_bot.mpr (orderOf_eq_one_iff.mp hord)
    apply eq_bot_iff.mpr
    intro n hn
    have he := mem_bot.mp (hall (mem_top (⟨n, hn⟩ : N)))
    exact mem_bot.mpr (congrArg Subtype.val he)
  subst N
  exact h.centralizer_le_of_isPGroup P x hx (hquot.of_equiv QuotientGroup.quotientBot)

end Glauberman.SuzukiCharacterization
