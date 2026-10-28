module
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement
public import Theory.GroupTheory.SolvableRadical.TwoClosedKernel

/-!
# Odd radical quotient from a two-closed kernel

Let N be normal with a normal Sylow two-subgroup. Suppose that a normal
subgroup K has an ordinary component image in G/N and that G/N has trivial
two-core. A Sylow two-subgroup of the radical of K has central image in
that component, hence trivial image. Normal Sylow control inside N then
places it in the ambient two-core, whose intersection with K is O₂(K).
Thus O₂(K) has odd relative index in the radical of K.

Source: the component calculation in Aschbacher--Smith 14.6.10(5),
printed p.1029, using the normal Sylow subgroup supplied by F.6.11.
-/

public section
open Subgroup Theory.GroupTheory
namespace Subgroup

/-- A two-closed normal kernel and a component image with trivial ambient
two-core force odd radical index in the original normal subgroup. -/
theorem odd_radical_relIndex_of_component_quotient {G : Type*} [Group G] [Finite G]
    (N K : Subgroup G) [N.Normal] [K.Normal]
    (hN : ∃ S : Sylow 2 N, (S : Subgroup N).Normal)
    (hq : pCore 2 (G ⧸ N) = ⊥)
    (hK : IsComponent (G ⧸ N) (K.map (QuotientGroup.mk' N))) :
    Odd ((pCore 2 K).relIndex (solvableRadical K)) := by
  let q := QuotientGroup.mk' N
  let B := K.map q
  let f := q.subgroupMap K
  let : IsQuasisimple B := hK.2
  let R := solvableRadical K
  let S : Sylow 2 R := default
  let P : Subgroup K := (S : Subgroup R).map R.subtype
  have hPc : P.map f ≤ center B :=
    (map_mono (map_subtype_le (S : Subgroup R))).trans
      ((map_solvableRadical_le_of_surjective f (q.subgroupMap_surjective K)).trans
        IsQuasisimple.solvableRadical_le_center)
  have hBn : pCore 2 B = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.1, hq]
    exact B.subtype.ker_eq_bot B.subtype_injective
  have hPn : (P.map f).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hc := mem_center_iff.mp (hPc hx) g
    simpa only [hc, mul_inv_cancel_right] using hx
  have hPi : P.map f ≤ pCore 2 B :=
    le_sSup ⟨hPn, (S.isPGroup'.map R.subtype).map f⟩
  have hker : P ≤ f.ker := (map_eq_bot_iff P).mp (le_bot_iff.mp (hPi.trans_eq hBn))
  have hPN : P.map K.subtype ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x.val).mp
      (congrArg Subtype.val (show f x = 1 from hker hx))
  have hPG : P.map K.subtype ≤ pCore 2 G :=
    le_pCore_of_normalSylow hN ((S.isPGroup'.map R.subtype).map K.subtype) hPN
  have hPK : P ≤ pCore 2 K := by
    rw [pCore_subnormal_eq_comap 2 (inferInstance : K.Normal).isSubnormal]
    exact map_le_iff_le_comap.mp hPG
  have hS : (S : Subgroup R) ≤ (pCore 2 K).subgroupOf R :=
    map_le_iff_le_comap.mp hPK
  exact Nat.not_even_iff_odd.mp (fun he => S.not_dvd_index
    ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hS)))

end Subgroup
