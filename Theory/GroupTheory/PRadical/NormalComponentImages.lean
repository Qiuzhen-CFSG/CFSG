module

public import Theory.GroupTheory.PRadical
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.SylowKernelCore
public import Theory.GroupTheory.CoprimeNormalizerAutomorphisms
public import Theory.GroupTheory.GeneralizedFitting.CentralCoverLift
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.QuotientIntersection

/-!
# Radical intersections and the two quotient stages

Intersect a radical p-subgroup with a normal subgroup. The local p-core
of the intersection normalizer is invariant under the original normalizer,
so radical saturation identifies it with the intersection. The same equality
passes through a p-kernel contained in the subgroup and then through a central
prime-to-p kernel. These are the actual two quotient stages from a component
to its faithful star image in C.2.7. No nontriviality is asserted after a
quotient, so the outer-action case remains available.

Source: Aschbacher, Some results on pushing up in finite groups (1981),
Lemma 8.2(4), and Aschbacher–Smith C.2.7, pp.146–147.
-/

public section
open Subgroup
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]
variable {p : ℕ} [Fact p.Prime]

theorem normal_intersection_normalizer_core (K R : Subgroup G) [K.Normal]
    (hR : IsPRadical p R) :
    (K ⊓ normalizer (R ⊓ K : Set G)).pCoreIn p = R ⊓ K := by
  let U := R ⊓ K
  let Y := K ⊓ normalizer (U : Set G)
  have hNU : normalizer (R : Set G) ≤ normalizer (U : Set G) :=
    (le_inf le_rfl le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  have hNY : normalizer (R : Set G) ≤ normalizer (Y : Set G) :=
    (le_inf le_normalizer_of_normal (hNU.trans (normalizer (U : Set G)).le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hPR : Y.pCoreIn p ≤ R := le_of_normalizer_le_normalizer_of_pCore_normalizer_le
    R _ hR.isPGroup (isPGroup_pCoreIn p Y) hR.2.le
    (hNY.trans (normalizer_le_normalizer_characteristic_image Y (pCore p Y)))
  exact le_antisymm (le_inf hPR ((pCoreIn_le p Y).trans inf_le_left))
    (le_pCoreIn_of_normalizes (hR.isPGroup.to_le inf_le_left)
      (le_inf inf_le_right U.le_normalizer) inf_le_right)

theorem normal_intersection_relative_core (K R : Subgroup G) [K.Normal]
    (hR : IsPRadical p R) :
    (normalizer (R.subgroupOf K : Set K)).pCoreIn p = R.subgroupOf K := by
  apply map_injective K.subtype_injective
  rw [map_pCoreIn_of_injective p _ _ K.subtype_injective]
  have hn : (normalizer (R.subgroupOf K : Set K)).map K.subtype =
      K ⊓ normalizer (R ⊓ K : Set G) := by
    rw [←inf_subgroupOf_right R K,←subgroupOf_normalizer_eq inf_le_right,
      subgroupOf_map_subtype,inf_comm]
    rfl
  rw [hn,normal_intersection_normalizer_core K R hR,subgroupOf_map_subtype]

theorem map_normalizer_core_of_p_kernel (R : Subgroup G)
    (hR : IsPGroup p R) (hc : (normalizer (R : Set G)).pCoreIn p = R)
    (f : G →* D) (hf : Function.Surjective f) (hk : f.ker ≤ R) :
    (normalizer (R.map f : Set D)).pCoreIn p = R.map f := by
  let : Finite D := Finite.of_surjective f hf
  have hn : (normalizer (R : Set G)).map f = normalizer (R.map f : Set D) := by
    have he : (normalizer (R.map f : Set D)).comap f = normalizer (R : Set G) := by
      rw [comap_normalizer_eq_of_surjective _ hf,comap_map_eq_self hk]
    rw [←he,map_comap_eq_self]
    rw [MonoidHom.range_eq_top_of_surjective _ hf]
    exact le_top
  rw [←hn,←map_pCoreIn_of_ker_isPGroup f (hR.to_le hk),hc]

theorem map_normalizer_core_of_central_coprime_kernel (R : Subgroup G)
    (hR : IsPGroup p R) (hc : (normalizer (R : Set G)).pCoreIn p = R)
    (f : G →* D) (hf : Function.Surjective f)
    (hk : f.ker ≤ center G) (hcop : Nat.Coprime p (Nat.card f.ker)) :
    (normalizer (R.map f : Set D)).pCoreIn p = R.map f := by
  let : Fact (IsPGroup p R) := ⟨hR⟩
  let N := normalizer (R : Set G)
  have hn := normalizer_map_eq_of_coprime_kernel p R f hf hcop
  let g := f.subgroupMap N
  have hg : g.ker ≤ center N := by
    intro x hx
    have hh : (x : G) ∈ f.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact mem_center_iff.mpr fun y => Subtype.ext (mem_center_iff.mp (hk hh) y)
  have he := g.map_pCore_of_central_kernel (f.subgroupMap_surjective N) hg (p := p)
  have hm := congrArg (map (N.map f).subtype) he
  change ((pCore p N).map g).map (N.map f).subtype = (N.map f).pCoreIn p at hm
  rw [map_map] at hm
  have heq : (N.map f).subtype.comp g = f.comp N.subtype := rfl
  rw [heq,←map_map] at hm
  change (N.pCoreIn p).map f = (N.map f).pCoreIn p at hm
  rw [hc] at hm
  rw [hn]
  exact hm.symm
omit [Finite G] in
theorem map_inf_of_kernel_le_sup (R K P : Subgroup G) [P.Normal]
    (f : G →* D) (hP : P ≤ f.ker) (hPR : P ≤ R) (hk : f.ker ≤ P ⊔ K) :
    (R ⊓ K).map f = R.map f ⊓ K.map f := by
  let q := QuotientGroup.mk' P
  let g := QuotientGroup.lift P f hP
  have he : g.comp q = f := by ext; rfl
  have hq : q.ker ≤ R := by simpa only [q,QuotientGroup.ker_mk'] using hPR
  have hp : P.map q = ⊥ := (map_eq_bot_iff P).mpr (by rw [QuotientGroup.ker_mk'])
  have hg : g.ker ≤ K.map q := by
    rw [show g.ker = f.ker.map q from QuotientGroup.ker_lift P f hP]
    have hh := map_mono (f := q) hk
    rwa [Subgroup.map_sup,hp,bot_sup_eq] at hh
  rw [←he,←map_map,inf_comm R K,map_inf_of_ker_le q K R hq,inf_comm,
    map_inf_of_ker_le g (R.map q) (K.map q) hg,map_map,map_map]
end Subgroup
