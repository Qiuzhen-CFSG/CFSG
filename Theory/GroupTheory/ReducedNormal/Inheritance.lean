module

public import Theory.GroupTheory.ReducedNormal.Basic
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.PCoreOvergroup

/-!
# Reduced subgroups in Sylow overgroups

Let H contain a Sylow p-subgroup of G. If a reduced subgroup of H has
an elementary abelian normal closure S in G, then S is reduced in G.
In G/C_G(S), the Sylow image contains the p-core. Its preimage is therefore
covered by C_G(S) and H, and reducedness inside H makes it centralize S.

When C_G(O_p(G)) ≤ O_p(G), the normal closure of R_p(H) lies in
Z(O_p(G)), so it is elementary abelian and the preceding result applies.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
A.1.11, printed p.22, generalized from two to an arbitrary prime.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- Reducedness passes to an elementary abelian normal closure from a Sylow overgroup. -/
theorem IsPReduced.normalClosure_of_sylow_le
    (T : Sylow p G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (V : Subgroup H) (hV : IsPReduced p V)
    (hS : IsElementaryAbelian p (normalClosure (V.map H.subtype : Set G))) :
    IsPReduced p (normalClosure (V.map H.subtype : Set G)) := by
  let := hV.normal
  let R := V.map H.subtype
  let S := normalClosure (R : Set G)
  let C := centralizer (S : Set G)
  let q := QuotientGroup.mk' C
  let Q := (pCore p (G ⧸ C)).comap q
  let N := Q.subgroupOf H
  let D := centralizer (V : Set H)
  let r := QuotientGroup.mk' D
  have hN : N ≤ D := by
    have himP : IsPGroup p (N.map r) := by
      rintro ⟨z, hz⟩
      obtain ⟨x, hx, rfl⟩ := hz
      obtain ⟨n, hn⟩ := pCore_isPGroup (⟨q x.val, hx⟩ : pCore p (G ⧸ C))
      refine ⟨n, Subtype.ext ?_⟩
      change r x ^ p ^ n = 1
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      have hxC : x.val ^ p ^ n ∈ C := by
        apply (QuotientGroup.eq_one_iff _).mp
        change q (x.val ^ p ^ n) = 1
        rw [map_pow]
        exact congrArg Subtype.val hn
      intro v hv
      apply Subtype.ext
      exact hxC v.val (le_normalClosure (mem_map_of_mem H.subtype hv))
    have him : N.map r ≤ pCore p (H ⧸ D) :=
      le_sSup ⟨Normal.map inferInstance r (QuotientGroup.mk'_surjective D), himP⟩
    intro x hx
    have hh := him (mem_map_of_mem r hx)
    rw [hV.quotient_pCore_eq_bot] at hh
    exact (QuotientGroup.eq_one_iff x).mp (mem_bot.mp hh)
  have hQC : Q ≤ centralizer (R : Set G) := by
    intro x hx
    have hcoreT : pCore p (G ⧸ C) ≤ (T : Subgroup G).map q :=
      pCore_isPGroup.le_sylow_of_normal (T.mapSurjective (QuotientGroup.mk'_surjective C))
    obtain ⟨t, ht, htx⟩ := hcoreT hx
    have htQ : t ∈ Q := by
      change q t ∈ pCore p (G ⧸ C)
      rwa [htx]
    have htR : t ∈ centralizer (R : Set G) := by
      rintro _ ⟨v, hv, rfl⟩
      exact congrArg H.subtype (hN (show (⟨t, hTH ht⟩ : H) ∈ N from htQ) v hv)
    have hxtC : x / t ∈ C := by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (x / t) = 1
      rw [map_div, htx]
      exact div_self' (q x)
    have hxtR : x / t ∈ centralizer (R : Set G) :=
      centralizer_le le_normalClosure hxtC
    simpa only [div_mul_cancel] using (centralizer (R : Set G)).mul_mem hxtR htR
  have hQS : Q ≤ C := le_centralizer_iff.mpr
    (normalClosure_le_normal (le_centralizer_iff.mp hQC))
  refine ⟨inferInstance, hS, ?_⟩
  apply bot_unique
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective C x
  exact (QuotientGroup.eq_one_iff g).mpr (hQS hx)

/-- In a group of characteristic p, R_p is inherited from each Sylow overgroup. -/
theorem reducedPSubgroup_map_le_of_sylow_le
    (T : Sylow p G) (H : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    (hG : centralizer (pCore p G : Set G) ≤ pCore p G) :
    (reducedPSubgroup p H).map H.subtype ≤ reducedPSubgroup p G := by
  let V := reducedPSubgroup p H
  let R := V.map H.subtype
  let S := normalClosure (R : Set G)
  have hV : IsPReduced p V := isPReduced_reducedPSubgroup
  let := hV.elementary
  let : IsElementaryAbelian p R := IsElementaryAbelian.map H.subtype
  have hRcentral : R ≤ centralizer (pCore p G : Set G) := by
    rintro _ ⟨v, hv, rfl⟩ x hx
    obtain ⟨y, hy, rfl⟩ := pCore_le_map_of_sylow_le T H hTH hx
    exact congrArg H.subtype (hV.le_centralizer_pCore hv y hy)
  have hScore : S ≤ pCore p G := normalClosure_le_normal (hRcentral.trans hG)
  have hScentral : S ≤ centralizer (pCore p G : Set G) :=
    normalClosure_le_normal hRcentral
  let : IsMulCommutative S := le_centralizer_iff_isMulCommutative.mp
    (hScentral.trans (centralizer_le hScore))
  have hS : IsPReduced p S := hV.normalClosure_of_sylow_le T H hTH V
    (IsElementaryAbelian.normalClosure_of_isMulCommutative R)
  exact le_normalClosure.trans hS.le_reducedPSubgroup

end Theory.GroupTheory
