module

public import Theory.GroupTheory.PCoreFrattiniTransport
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Mathlib.GroupTheory.SpecificGroups.Cyclic


/-!
# Cyclic quotients by prime cores and central extensions

A normal p-subgroup with cyclic supplement gives a cyclic quotient by Oₚ.
For a central extension, the inverse image of the target p-core is nilpotent.
Its Sylow p-subgroup lies in the ambient p-core, while its p-residual lies
in the central kernel. Consequently this entire preimage becomes central
modulo the ambient p-core. A cyclic central quotient is abelian.

A preceding p-group kernel is removed using the actual induced isomorphism
modulo p-cores. The Bender Borel application retains precisely these two
kernel stages.
Source: the finite-group argument used in Aschbacher--Smith, 4.4.13,
printed pp.623--624, following E.2.2(2), pp.215--216.
-/

@[expose] public section
open Subgroup
namespace Subgroup
universe u v w
variable {G : Type u} [Group G]

theorem cyclic_quotient_pCore_of_sup {p : ℕ} (U T : Subgroup G)
    [U.Normal] (hU : IsPGroup p U) [IsCyclic T] (hsup : U ⊔ T = ⊤) :
    IsCyclic (G ⧸ pCore p G) := by
  let q := QuotientGroup.mk' (pCore p G)
  have hUcore : U ≤ pCore p G := le_sSup ⟨inferInstance, hU⟩
  have hUmap : U.map q = ⊥ := (map_eq_bot_iff U).mpr (by simpa only [q, QuotientGroup.ker_mk'] using hUcore)
  have hTmap : T.map q = ⊤ := by
    have h := congrArg (fun H : Subgroup G => H.map q) hsup
    simpa [Subgroup.map_sup, hUmap, q,
      map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using h
  apply isCyclic_of_surjective (q.comp T.subtype)
  apply MonoidHom.range_eq_top.mp
  simpa only [MonoidHom.range_comp, range_subtype] using hTmap

theorem cyclic_quotient_pCore_of_borel {p : ℕ} (U T B : Subgroup G)
    (hU : IsPGroup p U) [IsCyclic T] (hsup : U ⊔ T = B)
    (hn : (U.subgroupOf B).Normal) : IsCyclic (B ⧸ pCore p B) := by
  let := hn
  have hUB : U ≤ B := hsup ▸ le_sup_left
  have hTB : T ≤ B := hsup ▸ le_sup_right
  let : IsCyclic (T.subgroupOf B) := isCyclic_of_injective
    (subgroupOfEquivOfLe hTB).toMonoidHom (subgroupOfEquivOfLe hTB).injective
  apply cyclic_quotient_pCore_of_sup (U.subgroupOf B) (T.subgroupOf B) hU.comap_subtype
  rw [← subgroupOf_sup hUB hTB, hsup, subgroupOf_self]

variable {H : Type v} [Group H] [Finite G] [Finite H]
  {p : ℕ} [Fact p.Prime]

private theorem central_preimage_core_le (f : G →* H)
    (hk : f.ker ≤ center G) : (pCore p H).comap f ≤ pCore p G ⊔ center G := by
  let L := (pCore p H).comap f
  let r : L →* pCore p H := (f.comp L.subtype).codRestrict _ (fun x => x.property)
  have hrk : r.ker ≤ center L := by
    intro x hx
    have hfx : f x.val = 1 := congrArg (fun a : pCore p H => (a : H)) (show r x = 1 from hx)
    have hc := hk hfx
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_center_iff.mp hc y.val)
  let : Group.IsNilpotent (pCore p H) := (pCore_isPGroup (p := p) (G := H)).isNilpotent
  let : Group.IsNilpotent L := Subgroup.isNilpotent_of_ker_le_center r hrk
  let T : Sylow p L := Classical.choice inferInstance
  have hTnormal : ((T : Subgroup L).map L.subtype).Normal :=
    Sylow.normal_of_nilpotent_normal (inferInstance : L.Normal) inferInstance p T
  have hTcore : (T : Subgroup L).map L.subtype ≤ pCore p G :=
    le_sSup ⟨hTnormal, T.isPGroup'.map L.subtype⟩
  have hrquot : IsPGroup p (L ⧸ r.ker) :=
    ((pCore_isPGroup (p := p) (G := H)).to_subgroup r.range).of_equiv
      (QuotientGroup.quotientKerEquivRange r).symm
  have hres : pResidual p L ≤ r.ker := sInf_le ⟨inferInstance, hrquot⟩
  have hresZ : (pResidual p L).map L.subtype ≤ center G := by
    rintro _ ⟨x, hx, rfl⟩
    apply hk
    exact congrArg (fun a : pCore p H => (a : H)) (show r x = 1 from hres hx)
  have he := congrArg (fun D : Subgroup L => D.map L.subtype) (pResidual_sup_sylow_eq_top T)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at he
  change L ≤ pCore p G ⊔ center G
  rw [← he]
  exact sup_le (hresZ.trans le_sup_right) (hTcore.trans le_sup_left)

theorem commutative_core_quotient_of_central_cyclic (f : G →* H)
    (hf : Function.Surjective f) (hk : f.ker ≤ center G)
    [IsCyclic (H ⧸ pCore p H)] : IsMulCommutative (G ⧸ pCore p G) := by
  have hmap : (pCore p G).map f ≤ pCore p H :=
    le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  let r := QuotientGroup.map (pCore p G) (pCore p H) f (map_le_iff_le_comap.mp hmap)
  apply r.isMulCommutative_of_isCyclic_of_ker_le_center
  rw [QuotientGroup.ker_map]
  apply (map_mono (f := QuotientGroup.mk' (pCore p G))
    (central_preimage_core_le f hk)).trans
  rw [Subgroup.map_sup, QuotientGroup.map_mk'_self]
  simp only [bot_sup_eq]
  rintro _ ⟨x, hx, rfl⟩
  apply mem_center_iff.mpr
  intro y
  obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective (pCore p G) y
  simpa only [map_mul] using congrArg (QuotientGroup.mk' (pCore p G)) (mem_center_iff.mp hx z)

theorem commutative_core_quotient_of_two_stage
    {B : Type w} [Group B] [Finite B]
    (q : G →* H) (hq : Function.Surjective q) (hqk : IsPGroup p q.ker)
    (r : H →* B) (hr : Function.Surjective r) (hrk : r.ker ≤ center H)
    [IsCyclic (B ⧸ pCore p B)] : IsMulCommutative (G ⧸ pCore p G) := by
  let := commutative_core_quotient_of_central_cyclic (p := p) r hr hrk
  let e := q.pCoreQuotientEquiv hq hqk
  refine ⟨⟨fun x y => e.injective ?_⟩⟩
  simp only [map_mul]
  exact (inferInstance : IsMulCommutative (H ⧸ pCore p H)).is_comm.comm _ _

end Subgroup
