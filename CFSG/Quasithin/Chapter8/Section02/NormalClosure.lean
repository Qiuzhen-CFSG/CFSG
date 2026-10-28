module

public import Theory.GroupTheory.PGroup.NormalClosureExtraspecial
public import Theory.PGroupCore

/-!
# The normal closure in the involution centralizer

Aschbacher–Smith, *The Classification of Quasithin Groups*, §8.2, Lemma 8.2.12,
combined manuscript (1 March 2004), printed p.722 (PDF p.739).

The normal closure is taken inside C = C_G(z). The local action on V_z makes
this closure extraspecial by the intrinsic normal-closure criterion. Normality
then places it in O₂(C). The source cover O₂(C) ≤ E Q_M and intersection
O₂(C) ∩ Q_M ≤ V_z give the reverse containment by writing each element as a
product from E and Q_M.

This module proves those deductions, with the earlier local action and cover
calculations explicit. It does not prove all of 8.2.12: its order, plus type,
and the source construction of the input data remain with the centralizer
calculation, as do 8.2.11 and 8.2.13. Theorem 8.2.14 additionally requires the
failure of weak closure and the Aschbacher–Segev recognition theorem.
-/

namespace CFSG.Quasithin.Chapter8.Section02
open Subgroup

/-- The literal closure E = ⟨V_z^C⟩ in C = C_G(z). -/
@[expose] public def centralizerClosure {G : Type*} [Group G] (z : G)
    (Vz : Subgroup (centralizer ({z} : Set G))) :
    Subgroup (centralizer ({z} : Set G)) := normalClosure (Vz : Set _)

/-- Normality is relative to the involution centralizer. -/
public instance centralizerClosure_normal {G : Type*} [Group G] (z : G)
    (Vz : Subgroup (centralizer ({z} : Set G))) : (centralizerClosure z Vz).Normal :=
  Subgroup.normalClosure_normal

/-- The extraspecial and two-core deductions of 8.2.12 from its local action
calculations. Here `Vz` is the actual source subgroup inside `C_G(z)`, and `QM`
is the restriction of O₂(LT) to that centralizer. The cover and intersection
premises are the final paragraph of the source proof. The preceding source
arguments must still supply these premises, the self-centralizer and fixed-point
calculations, and commutativity of E/Z(E). -/
public theorem centralizerClosure_extraspecial_and_eq_twoCore {G : Type*} [Group G] [Finite G] (z : G)
    (Vz QM : Subgroup (centralizer ({z} : Set G))) [IsElementaryAbelian 2 Vz]
    (hab : IsMulCommutative ((centralizerClosure z Vz) ⧸ center (centralizerClosure z Vz)))
    (hself : centralizer (Vz.subgroupOf (centralizerClosure z Vz) :
      Set (centralizerClosure z Vz)) ≤ Vz.subgroupOf (centralizerClosure z Vz))
    (hfixed : Nat.card (Vz.subgroupOf (centralizerClosure z Vz) ⊓
      center (centralizerClosure z Vz) : Subgroup (centralizerClosure z Vz)) = 2)
    (hlarge : 2 < Nat.card Vz)
    (hcover : pCore 2 (centralizer ({z} : Set G)) ≤ centralizerClosure z Vz ⊔ QM)
    (hcap : pCore 2 (centralizer ({z} : Set G)) ⊓ QM ≤ Vz) :
    IsExtraspecial 2 (centralizerClosure z Vz) ∧
      centralizerClosure z Vz = pCore 2 (centralizer ({z} : Set G)) := by
  have he : IsExtraspecial 2 (centralizerClosure z Vz) :=
    normalClosure_isExtraspecial_of_local_centralizers Vz hab hself hfixed hlarge
  let := he
  have hEQ : centralizerClosure z Vz ≤ pCore 2 (centralizer ({z} : Set G)) :=
    le_sSup ⟨inferInstance, IsExtraspecial.isPGroup 2 _⟩
  refine ⟨he, le_antisymm hEQ ?_⟩
  intro x hx
  obtain ⟨e, heE, m, hmM, rfl⟩ := mem_sup_of_normal_left.mp (hcover hx)
  have hmQ : m ∈ pCore 2 (centralizer ({z} : Set G)) := by
    have := (pCore 2 (centralizer ({z} : Set G))).mul_mem
      ((pCore 2 (centralizer ({z} : Set G))).inv_mem (hEQ heE)) hx
    simpa only [inv_mul_cancel_left] using this
  exact (centralizerClosure z Vz).mul_mem heE
    (le_normalClosure (hcap ⟨hmQ, hmM⟩))

end CFSG.Quasithin.Chapter8.Section02
