module

public import Theory.GroupTheory.NormalClosureCentralizerCore
public import Theory.Quasithin

/-!
# The centralizer consequence of Theorem 15.4.8

Aschbacher–Smith, *The Classification of Quasithin Groups*, combined manuscript
(1 March 2004), Lemma 15.4.11(1), printed p. 1160.

For every overgroup M of T, the equality C_G(Z) = T makes the centralizer of
Z inside M a Sylow subgroup. Taking its normal closure therefore cuts the
centralizer down to the two-core. This separate module lets the later family
construction use the consequence without importing the final assembly module.
The factorization step of 15.4.11(2) then turns the ordering relation into
actual containment, hence equality by maximality among two-local subgroups.
-/

namespace CFSG.Quasithin.Chapter15.Section04

open Subgroup

/-- Lemma 15.4.11(1) from the centralizer conclusion of Theorem 15.4.8,
with the normal closure and the core both viewed in the ambient group. -/
public theorem centralizer_normalClosure_eq_core
    {G : Type*} [Group G] (T : Sylow 2 G) (Z M : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G)) (hTM : (T : Subgroup G) ≤ M)
    (hC : centralizer (Z : Set G) = (T : Subgroup G)) :
    M ⊓ centralizer
      ((normalClosure (Z.subgroupOf M : Set M)).map M.subtype : Set G) =
        M.pCoreIn 2 := by
  have hZM : Z ≤ M := hZT.trans hTM
  have hlocal : centralizer (Z.subgroupOf M : Set M) =
      (T.subtype hTM : Subgroup M) := by
    rw [T.coe_subtype]
    ext x
    constructor
    · intro hx
      change (x : G) ∈ (T : Subgroup G)
      rw [← hC]
      intro z hz
      exact congrArg Subtype.val (hx ⟨z, hZM hz⟩ hz)
    · intro hx z hz
      have hc : (x : G) ∈ centralizer (Z : Set G) := hC.symm ▸ hx
      exact Subtype.ext (hc z hz)
  have h := centralizer_normalClosure_eq_pCore_of_eq_sylow
    (T.subtype hTM) (Z.subgroupOf M) hlocal
  have hm := congrArg (fun K : Subgroup M => K.map M.subtype) h
  rwa [map_centralizer_subtype] at hm

/-- The factorization step of 15.4.11(2). The source ordering supplies
`hfactor`; the centralizer theorem makes its first factor lie in `T`. -/
public theorem eq_of_normalClosure_centralizer_factorization
    {G : Type*} [Group G] (T : Sylow 2 G) (Z M N : Subgroup G)
    (hZT : Z ≤ (T : Subgroup G))
    (hTM : (T : Subgroup G) ≤ M) (hTN : (T : Subgroup G) ≤ N)
    (hC : centralizer (Z : Set G) = (T : Subgroup G))
    (hM : IsMaximalTwoLocal M) (hN : IsTwoLocal N)
    (hfactor : M =
      (M ⊓ centralizer
        ((normalClosure (Z.subgroupOf M : Set M)).map M.subtype : Set G)) ⊔
      (M ⊓ N)) : M = N := by
  apply hM.eq_of_le hN
  have hcoreT : M.pCoreIn 2 ≤ (T : Subgroup G) := by
    have h := pCoreIn_le_sylow M (T.subtype hTM)
    rwa [T.coe_subtype, map_subgroupOf_eq_of_le hTM] at h
  have hcentral := centralizer_normalClosure_eq_core T Z M hZT hTM hC
  rw [hcentral] at hfactor
  calc
    M = M.pCoreIn 2 ⊔ (M ⊓ N) := hfactor
    _ ≤ N := sup_le (hcoreT.trans hTN) inf_le_right

end CFSG.Quasithin.Chapter15.Section04
