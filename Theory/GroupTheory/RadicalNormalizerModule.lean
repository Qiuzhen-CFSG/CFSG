module
public import Theory.GroupTheory.PRadical.NormalizerRestriction
public import Theory.GroupTheory.AbelianNormalizerCore
public import Theory.GroupTheory.IndexTwoFixedSylowComplement
public import Theory.GroupTheory.Commutator.CentralizingComplement

/-!
# Radical normalizers and their moved modules

An abelian two-radical inside a group with self-centralizing two-core is
that entire core when its ambient normalizer is contained in the group.
Its normalizer and centralizer are then determined as well.

More generally, let U be two-radical and N(U) ≤ N(B), with N(B) of
characteristic two. If U centralizes E and [U,B] = [E,B] = E, radical
saturation puts Q = O₂(N(B)) inside U. Self-centralization puts E inside
Q, so [Q,B] = E. Consequently the whole normalizer N(B) preserves E.

A fixed subgroup of index at most two in a two-group has a two-group
pointwise automorphism stabilizer. This identifies the relative module
centralizer when the radical is self-centralizing. A fully moved subgroup
inside its actor also retains normalizer control across a central kernel.

These are the finite-group normalizer calculations used in the
Aschbacher–Smith 4.2.13 and 4.4.14 Mathieu pushing-up comparisons,
printed pp.611–612 and624–625.
-/

public section
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]
/-- An abelian radical in a characteristic-two overgroup is its full core,
and determines both its ambient normalizer and centralizer. -/
theorem abelian_radical_in_constrained
    (U M : Subgroup G) [IsMulCommutative U]
    (hr : IsPRadical 2 U) (hUM : U ≤ M)
    (hNM : normalizer (U : Set G) ≤ M)
    (hc : centralizer (pCore 2 M : Set M) ≤ pCore 2 M) :
    M.pCoreIn 2 = U ∧ normalizer (U : Set G) = M ∧ centralizer (U : Set G) = U := by
  have hrM := hr.subgroupOf_of_normalizer_normalizes M hUM (hNM.trans M.le_normalizer)
  let : IsMulCommutative (U.subgroupOf M) := ⟨⟨fun x y => Subtype.ext (Subtype.ext
    (setLike_mul_comm (s := U) x.property y.property))⟩⟩
  have heM := eq_pCore_of_abelian_normalizer_core_le (U.subgroupOf M) hrM.isPGroup hc hrM.2.le
  have he : M.pCoreIn 2 = U := by
    have hh := congrArg (map M.subtype) heM
    rw [map_subgroupOf_eq_of_le hUM] at hh
    exact hh.symm
  have hN : normalizer (U : Set G) = M := le_antisymm hNM (by
    rw [←he]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M)))
  refine ⟨he,hN,le_antisymm ?_ ?_⟩
  · intro x hx
    have hxM : x ∈ M := hN ▸ Subgroup.centralizer_le_normalizer _ hx
    have hxC : (⟨x,hxM⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
      intro y hy
      apply Subtype.ext
      exact hx y (he ▸ mem_map_of_mem M.subtype hy)
    exact he ▸ mem_map_of_mem M.subtype (hc hxC)
  · intro x hx y hy
    exact setLike_mul_comm hy hx

/-- Recover the moved module from the characteristic normalizer core;
this proves that the entire residual normalizer preserves the module. -/
theorem radical_normalizer_core_displacement
    (U E B : Subgroup G) (hr : IsPRadical 2 U)
    (hNB : normalizer (U : Set G) ≤ normalizer (B : Set G))
    (hc : centralizer (pCore 2 (normalizer (B : Set G)) :
      Set (normalizer (B : Set G))) ≤ pCore 2 (normalizer (B : Set G)))
    (hEU : E ≤ U) (hUC : U ≤ centralizer (E : Set G))
    (hUB : ⁅U,B⁆ = E) (hEB : ⁅E,B⁆ = E) :
    let Q := (normalizer (B : Set G)).pCoreIn 2
    E ≤ Q ∧ Q ≤ U ∧ ⁅Q,B⁆ = E ∧
      normalizer (B : Set G) ≤ normalizer (E : Set G) := by
  let M := normalizer (B : Set G)
  let Q := M.pCoreIn 2
  have hMQ : M ≤ normalizer (Q : Set G) :=
    M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  have hQU : Q ≤ U := le_of_normalizer_le_normalizer_of_pCore_normalizer_le U Q
    hr.isPGroup (isPGroup_pCoreIn 2 M) hr.2.le (hNB.trans hMQ)
  have hUM : U ≤ M := U.le_normalizer.trans hNB
  have hEQ : E ≤ Q := by
    intro x hx
    have hxM : x ∈ M := hUM (hEU hx)
    have hxC : (⟨x,hxM⟩ : M) ∈ centralizer (pCore 2 M : Set M) := by
      intro y hy
      apply Subtype.ext
      exact ((hUC (hQU (mem_map_of_mem M.subtype hy))) x hx).symm
    exact mem_map_of_mem M.subtype (hc hxC)
  have he : ⁅Q,B⁆ = E := le_antisymm
    ((commutator_mono hQU le_rfl).trans_eq hUB)
    (hEB.symm.le.trans (commutator_mono hEQ le_rfl))
  refine ⟨hEQ,hQU,he,?_⟩
  intro x hx
  rw [mem_normalizer_iff_map_conj_eq,←he,map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (hMQ hx),
    mem_normalizer_iff_map_conj_eq.mp hx]

/-- A normalizer fixes a subgroup of index at most two in its self-centralizing
two-core only through elements of that core. Normality is relative to M. -/
theorem centralizer_le_core_of_fixed_index_le_two
    (M U E : Subgroup G) (hcore : M.pCoreIn 2 = U)
    (hCU : centralizer (U : Set G) ≤ U)
    (hEU : E ≤ U) (hi : E.relIndex U ≤ 2)
    (hME : M ≤ normalizer (E : Set G)) :
    M ⊓ centralizer (E : Set G) ≤ U := by
  have hUM : U ≤ M := hcore ▸ map_subtype_le _
  have hp : IsPGroup 2 U := hcore ▸ isPGroup_pCoreIn 2 M
  have hMU : M ≤ normalizer (U : Set G) := by
    rw [←hcore]
    exact M.le_normalizer.trans (normalizer_le_normalizer_characteristic_image M (pCore 2 M))
  let C := M ⊓ centralizer (E : Set G)
  let E' := E.subgroupOf U
  have hidx : E'.index ≤ 2 := hi
  have hfix : IsPGroup 2 (fixingSubgroup (MulAut U) (E' : Set U)) := by
    have hpos : E'.index ≠ 0 := Nat.card_pos.ne'
    interval_cases hd : E'.index
    · omega
    · have he := index_eq_one.mp hd
      have hb : fixingSubgroup (MulAut U) (E' : Set U) = ⊥ := by
        apply eq_bot_iff.mpr
        intro a ha
        apply MulEquiv.ext
        intro x
        exact (mem_fixingSubgroup_iff (MulAut U)).mp ha x (he ▸ mem_top x)
      rw [hb]
      exact IsPGroup.of_bot
    · exact E'.isPGroup_fixingSubgroup_of_index_two hd ((hp.to_le hEU).comap_subtype)
  let f : C →* MulAut U := U.normalizerMonoidHom.comp
    (inclusion (show C ≤ normalizer (U : Set G) from inf_le_left.trans hMU))
  have hf : f.range ≤ fixingSubgroup (MulAut U) (E' : Set U) := by
    rintro _ ⟨c,rfl⟩
    apply (mem_fixingSubgroup_iff (MulAut U)).mpr
    intro u hu
    apply Subtype.ext
    change (c : G) * (u : G) * (c : G)⁻¹ = (u : G)
    rw [←c.property.2 u hu,mul_inv_cancel_right]
  have hk : IsPGroup 2 f.ker := by
    apply hp.comap_subtype.to_le
    intro c hc
    apply hCU
    intro u hu
    have he := congrArg (fun a : MulAut U => (a ⟨u,hu⟩ : G)) hc
    change (c : G) * u * (c : G)⁻¹ = u at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hCp : IsPGroup 2 C := by
    have ht := (hfix.to_le hf).comap_of_ker_isPGroup f hk
    have he : f.range.comap f = ⊤ := by
      apply top_unique
      intro c _
      exact ⟨c,rfl⟩
    rw [he] at ht
    exact ht.of_equiv (topEquiv : (⊤ : Subgroup C) ≃* C)
  rw [←hcore]
  apply le_pCoreIn_of_normalizes hCp inf_le_left
  exact (le_inf M.le_normalizer (hME.trans (normalizer_le_normalizer_centralizer E))).trans
    inf_normalizer_le_normalizer_inf
end Subgroup

namespace Subgroup
variable {G Q : Type*} [Group G] [Group Q]

/-- Full displacement recovers normalization across a central kernel,
without identifying the subgroup with its full quotient preimage. -/
theorem normalizer_le_of_moved_map_normalizer_le
    (q : G →* Q) (hk : q.ker ≤ center G) (E B : Subgroup G)
    (hEB : E ≤ B) (hmove : ⁅E,B⁆ = E)
    (hn : normalizer (B.map q : Set Q) ≤ normalizer (E.map q : Set Q)) :
    normalizer (B : Set G) ≤ normalizer (E : Set G) := by
  apply le_normalizer_iff.mpr
  intro g hg e he
  let P := E.map (MulAut.conj g).toMonoidHom
  have hm : P.map q ≤ E.map q := by
    rintro _ ⟨x,⟨y,hy,rfl⟩,rfl⟩
    change q (g*y*g⁻¹) ∈ E.map q
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp
      (hn (B.le_normalizer_map q (mem_map_of_mem q hg))) (q y)).mp (mem_map_of_mem q hy)
  have hP : P ≤ E ⊔ q.ker := by
    rw [←comap_map_eq]
    exact map_le_iff_le_comap.mp hm
  have hPB : ⁅P,B⁆ = P := by
    have hh := congrArg (map (MulAut.conj g).toMonoidHom) hmove
    have hb : B.map (MulAut.conj g).toMonoidHom = B := mem_normalizer_iff_map_conj_eq.mp hg
    rwa [map_commutator,hb] at hh
  have hsup : ⁅E ⊔ q.ker,B⁆ = E := by
    rw [commutator_comm]
    rw [←commutator_eq_of_centralizing_sup (sup_comm q.ker E)
      (hk.trans (center_le_centralizer (B : Set G))) (hEB.trans B.le_normalizer)]
    rw [commutator_comm,hmove]
  exact (hPB.symm.le.trans ((commutator_mono hP le_rfl).trans_eq hsup))
    (mem_map_of_mem _ he)
end Subgroup
