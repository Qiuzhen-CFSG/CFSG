module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalBasic
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# Involution transporters from Sylow fusion control

Fusion control on a Sylow subgroup contained in M extends to involutions
throughout M, by conjugating each into that Sylow subgroup inside M.
If an involution in M also has its ambient centralizer in M, every conjugator
carrying it back into M belongs to M. This is the unique conjugate-membership
condition used to descend product centralizers in GLS, Volume 4,
Chapter 2, Lemmas 4.2(c) and 4.5; compare Chapter 1, Lemmas 1.2 and 1.7.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}

/-- Sylow fusion control extends to all involutions in the subgroup. -/
public theorem involution_fusion_in_subgroup (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    (hf : ControlsFusionIn M (S : Subgroup G))
    {x y : G} (hx : IsInvolution x) (hy : IsInvolution y)
    (hxM : x ∈ M) (hyM : y ∈ M) (hxy : IsConj x y) :
    ∃ m : M, (m : G) * x * (m : G)⁻¹ = y := by
  have hx' : orderOf (⟨x, hxM⟩ : M) = 2 ^ 1 := by
    rw [← Subgroup.orderOf_coe]
    simpa using orderOf_eq_prime hx.sq_eq_one hx.ne_one
  have hy' : orderOf (⟨y, hyM⟩ : M) = 2 ^ 1 := by
    rw [← Subgroup.orderOf_coe]
    simpa using orderOf_eq_prime hy.sq_eq_one hy.ne_one
  obtain ⟨a, ha⟩ := (S.subtype hSM).exists_isConj_of_orderOf_eq_prime_pow hx'
  obtain ⟨b, hb⟩ := (S.subtype hSM).exists_isConj_of_orderOf_eq_prime_pow hy'
  obtain ⟨m, hm⟩ := isConj_iff.mp ha
  obtain ⟨n, hn⟩ := isConj_iff.mp hb
  have hm' : (m : G) * x * (m : G)⁻¹ = ((a : M) : G) := congrArg Subtype.val hm
  have hn' : (n : G) * y * (n : G)⁻¹ = ((b : M) : G) := congrArg Subtype.val hn
  have hab : IsConj ((a : M) : G) ((b : M) : G) :=
    (isConj_iff.mpr ⟨(m : G), hm'⟩).symm.trans
      (hxy.trans (isConj_iff.mpr ⟨(n : G), hn'⟩))
  obtain ⟨k, hk⟩ := hf.exists_conjugator a.property b.property hab
  change (k : G) * ((a : M) : G) * (k : G)⁻¹ = ((b : M) : G) at hk
  refine ⟨n⁻¹ * k * m, ?_⟩
  change ((n : G)⁻¹ * k * m) * x * ((n : G)⁻¹ * k * m)⁻¹ = y
  calc
    _ = (n : G)⁻¹ * (k * ((m : G) * x * (m : G)⁻¹) * (k : G)⁻¹) * n := by group
    _ = (n : G)⁻¹ * ((b : M) : G) * n := by rw [hm', hk]
    _ = y := by rw [← hn']; group

/-- Fusion control and centralizer containment give unique conjugate membership. -/
public theorem involution_transporter_mem (S : Sylow 2 G) (hSM : (S : Subgroup G) ≤ M)
    (hf : ControlsFusionIn M (S : Subgroup G))
    {x : G} (hx : IsInvolution x) (hxM : x ∈ M)
    (hC : Subgroup.centralizer ({x} : Set G) ≤ M)
    {g : G} (hg : MulAut.conj g x ∈ M) : g ∈ M := by
  have hconj : IsConj x (MulAut.conj g x) := isConj_iff.mpr ⟨g, rfl⟩
  obtain ⟨m, hm⟩ := involution_fusion_in_subgroup S hSM hf hx
    (BenderSuzuki.IsInvolution.map_of_injective hx (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
    hxM hg hconj
  have hmc : (m : G)⁻¹ * g ∈ Subgroup.centralizer ({x} : Set G) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    have h : (m : G) * x * (m : G)⁻¹ = g * x * g⁻¹ := hm
    calc
      ((m : G)⁻¹ * g) * x = (m : G)⁻¹ * (g * x * g⁻¹) * g := by group
      _ = (m : G)⁻¹ * ((m : G) * x * (m : G)⁻¹) * g := by rw [← h]
      _ = x * ((m : G)⁻¹ * g) := by group
  simpa only [mul_inv_cancel_left] using M.mul_mem m.property (hC hmc)

end BenderSuzuki.ZD
