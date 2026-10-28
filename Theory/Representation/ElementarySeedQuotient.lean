module
public import Theory.GroupTheory.PGroup.OmegaAmbient
public import Theory.GroupTheory.CommutatorPreimage
public import Theory.GroupTheory.ConjugateSpanOrder
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Elementary seeds in an irreducible group quotient

If Ω₁(K) = Y, an elementary subgroup W meets K exactly in W ∩ Y.
When W is normalized by Q and Q/K is abelian, this bounds [W,Q] by
W ∩ Y. An invariant subgroup with nonzero image in an irreducible binary
quotient Q/K supplements K. The latter statement retains the given actor
map, quotient map and conjugation formula on representatives; all normality
is relative to the displayed subgroups.

These are the seed and invariant-image arguments used in the action step
preceding (3) of DGS, Groups and Graphs (1985), printed p.188.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Subgroup
variable {G : Type*} [Group G]

/-- An elementary subgroup meets a kernel inside its first omega subgroup. -/
theorem elementary_inf_eq_of_omega (W K Y : Subgroup G)
    [IsElementaryAbelian 2 W] (hY : omegaOneAmbient K = Y) : W ⊓ K = W ⊓ Y := by
  have hWY : W ⊓ K ≤ Y := by
    rw [←hY]
    intro w hw
    exact (omegaOneAmbient_le_iff K (omegaOneAmbient K)).mp le_rfl w hw.2
      (elemPow_eq_one_of_isElementaryAbelian w hw.1)
  exact le_antisymm (le_inf inf_le_left hWY)
    (inf_le_inf_left W (hY ▸ omegaOneAmbient_le K))

/-- A normalized elementary seed has displacement in the kernel's first omega subgroup. -/
theorem elementary_commutator_le_of_omega (W Q K Y : Subgroup G)
    [IsElementaryAbelian 2 W] (hWQ : W ≤ Q)
    (hQW : Q ≤ normalizer (W : Set G)) (hder : ⁅Q,Q⁆ ≤ K)
    (hY : omegaOneAmbient K = Y) : ⁅W,Q⁆ ≤ W ⊓ Y := by
  rw [←elementary_inf_eq_of_omega W K Y hY]
  exact le_inf (le_normalizer_iff_commutator_le_left.mp hQW)
    ((commutator_mono hWQ le_rfl).trans hder)

/-- An invariant subgroup in a literal irreducible binary quotient is either
contained in the denominator or supplements it. The actor and quotient maps
are retained explicitly. -/
theorem inf_or_sup_of_irreducible_quotient
    {A M : Type*} [Group A] [Group M]
    (Q K J : Subgroup G) [(K.subgroupOf Q).Normal]
    [IsElementaryAbelian 2 (Q ⧸ K.subgroupOf Q)]
    (hKQ : K ≤ Q) (hJQ : J ≤ Q)
    (f : A → G) (π : A →* M) (hπ : Function.Surjective π)
    (hQ : ∀ a, f a ∈ normalizer (Q : Set G))
    (hJ : ∀ a, f a ∈ normalizer (J : Set G))
    (ρ : Representation (ZMod 2) M (Additive (Q ⧸ K.subgroupOf Q))) [ρ.IsIrreducible]
    (hρ : ∀ a : A, ∀ v : Q,
      (ρ (π a) (Additive.ofMul (QuotientGroup.mk v))).toMul =
        QuotientGroup.mk ⟨f a * v * (f a)⁻¹,
          (mem_normalizer_iff.mp (hQ a) v).mp v.property⟩) :
    J ≤ K ∨ J ⊔ K = Q := by
  let q := QuotientGroup.mk' (K.subgroupOf Q)
  let I := (J.subgroupOf Q).map q
  let U : Subrepresentation ρ := {
    toSubmodule := AddSubgroup.toZModSubmodule 2 I.toAddSubgroup
    apply_mem_toSubmodule m v hv := by
      obtain ⟨a,rfl⟩ := hπ m
      obtain ⟨w,hw,he⟩ := hv
      have hev : Additive.ofMul (q w) = v := congrArg Additive.ofMul he
      rw [←hev]
      change (ρ (π a) (Additive.ofMul (QuotientGroup.mk w))).toMul ∈ I
      rw [hρ]
      exact ⟨⟨f a * w * (f a)⁻¹,(mem_normalizer_iff.mp (hQ a) w).mp w.property⟩,
        (mem_normalizer_iff.mp (hJ a) w).mp hw,rfl⟩ }
  rcases eq_bot_or_eq_top U with hb | ht
  · left
    intro j hj
    have hh : Additive.ofMul (q ⟨j,hJQ hj⟩) ∈ U :=
      mem_map_of_mem q (show (⟨j,hJQ hj⟩ : Q) ∈ J.subgroupOf Q from hj)
    rw [hb] at hh
    exact (QuotientGroup.eq_one_iff (N := K.subgroupOf Q) _).mp
      (congrArg Additive.toMul hh)
  · right
    have hI : I = ⊤ := by
      apply eq_top_iff.mpr
      intro v _
      exact (show Additive.ofMul v ∈ U from ht ▸ Submodule.mem_top)
    have he := congrArg (Subgroup.comap q) hI
    change ((J.subgroupOf Q).map q).comap q = (⊤ : Subgroup (Q ⧸ K.subgroupOf Q)).comap q at he
    rw [comap_map_eq,QuotientGroup.ker_mk',comap_top] at he
    have hh := congrArg (Subgroup.map Q.subtype) he
    rw [map_sup,map_subgroupOf_eq_of_le hJQ,map_subgroupOf_eq_of_le hKQ,
      ←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh
end Subgroup
