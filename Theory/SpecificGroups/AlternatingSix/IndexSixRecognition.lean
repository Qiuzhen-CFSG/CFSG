module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.IsPerfect

/-!
# Recognizing A₆ from a nonnormal simple subgroup of index six

A nonnormal simple subgroup of order sixty has trivial normal core. Its
six-coset action embeds the ambient group, of order 360, in S₆. The image
has index two and therefore is the actual alternating group.

For a surjection to A₆ with kernel of order three, a nonabelian Sylow
three-subgroup forces perfectness. Otherwise the derived subgroup misses
the kernel, and the abelian Sylow three-subgroups of A₆ force the original
Sylow subgroup to commute.

These are the recognition and perfectness steps in Aschbacher,
*Sporadic Groups* (1994), proof of 47.3, printed p.262. The source consumer
must establish nonnormality and the nonabelian Sylow hypothesis.
-/

public section

open Subgroup
namespace Theory.SpecificGroups.AlternatingSix
variable {Q : Type*} [Group Q] [Finite Q]

omit [Finite Q] in
private theorem simple_core_free (K : Subgroup Q) [IsSimpleGroup K] (hn : ¬ K.Normal) :
    K.normalCore = ⊥ := by
  rcases (inferInstance : (K.normalCore.subgroupOf K).Normal).eq_bot_or_eq_top with h | h
  · have hm := congrArg (fun S : Subgroup K => S.map K.subtype) h
    simpa only [map_subgroupOf_eq_of_le K.normalCore_le, Subgroup.map_bot] using hm
  · have hm := congrArg (fun S : Subgroup K => S.map K.subtype) h
    have he : K.normalCore = K := by
      simpa only [map_subgroupOf_eq_of_le K.normalCore_le, ← MonoidHom.range_eq_map, range_subtype] using hm
    exact (hn (he ▸ inferInstance)).elim

private noncomputable def cosetRepresentation (K : Subgroup Q) (hi : K.index = 6) :
    Q →* Equiv.Perm (Fin 6) :=
  (Equiv.permCongrHom (Finite.equivFinOfCardEq hi)).toMonoidHom.comp
    (MulAction.toPermHom Q (Q ⧸ K))

private theorem cosetRepresentation_injective (K : Subgroup Q) (hi : K.index = 6)
    (hc : K.normalCore = ⊥) : Function.Injective (cosetRepresentation K hi) := by
  apply (Equiv.permCongrHom (Finite.equivFinOfCardEq hi)).injective.comp
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rwa [← normalCore_eq_ker]

/-- The faithful six-coset action identifies the group with A₆. -/
theorem alternatingSix_of_nonnormal_simple_index_six (K : Subgroup Q)
    [IsSimpleGroup K] (hK : Nat.card K = 60) (hi : K.index = 6)
    (hn : ¬ K.Normal) : Nonempty (Q ≃* alternatingGroup (Fin 6)) := by
  let f := cosetRepresentation K hi
  have hf : Function.Injective f := cosetRepresentation_injective K hi (simple_core_free K hn)
  have hQ : Nat.card Q = 360 := by
    have h := K.index_mul_card
    rw [hi, hK] at h
    omega
  have hr : Nat.card f.range = 360 :=
    (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hQ
  have hind : f.range.index = 2 := by
    have h := f.range.index_mul_card
    rw [hr, Nat.card_perm, Nat.card_fin] at h
    norm_num [Nat.factorial] at h
    omega
  exact ⟨(MonoidHom.ofInjective hf).trans
    (MulEquiv.subgroupCongr (Equiv.Perm.eq_alternatingGroup_of_index_eq_two hind))⟩

open scoped commutatorElement

/-- A nonabelian Sylow three-subgroup rules out a proper derived subgroup. -/
theorem perfect_of_three_kernel_alternating_six_quotient
    {L : Type*} [Group L] [Finite L]
    (f : L →* alternatingGroup (Fin 6)) (hf : Function.Surjective f)
    (hk : Nat.card f.ker = 3)
    (P : Sylow 3 L) (hP : ¬ IsMulCommutative P) : Group.IsPerfect L := by
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  let : IsSimpleGroup f.ker := isSimpleGroup_of_prime_card hk
  let D := commutator L
  have hm : D.map f = ⊤ := by
    rw [show D = commutator L from rfl, map_commutator_eq,
      MonoidHom.range_eq_top.mpr hf]
    exact Group.IsPerfect.commutator_eq_top
  rcases (inferInstance : (D.subgroupOf f.ker).Normal).eq_bot_or_eq_top with h | h
  · have hd : Disjoint D f.ker := subgroupOf_eq_bot.mp h
    let S := P.mapSurjective hf
    have hS : Nat.card S = 3 ^ 2 := by
      rw [S.card_eq_multiplicity, nat_card_alternatingGroup, Nat.card_fin]
      decide +kernel
    let : IsMulCommutative S := IsPGroup.isMulCommutative_of_card_eq_prime_sq hS
    apply (hP ?_).elim
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    have hxy : f (x : L) * f (y : L) = f (y : L) * f (x : L) := by
      have hx : f (x : L) ∈ (S : Subgroup (alternatingGroup (Fin 6))) :=
        ⟨x, x.property, rfl⟩
      have hy : f (y : L) ∈ (S : Subgroup (alternatingGroup (Fin 6))) :=
        ⟨y, y.property, rfl⟩
      exact congrArg Subtype.val (IsMulCommutative.is_comm.comm
        (⟨f x, hx⟩ : S) ⟨f y, hy⟩)
    have hc : ⁅(x : L), (y : L)⁆ ∈ D ⊓ f.ker := by
      refine ⟨commutator_mem_commutator (mem_top _) (mem_top _), ?_⟩
      change f ⁅(x : L), (y : L)⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr hxy
    rw [hd.eq_bot, mem_bot] at hc
    exact commutatorElement_eq_one_iff_mul_comm.mp hc
  · have hkD := subgroupOf_eq_top.mp h
    have htop : D ⊔ f.ker = ⊤ := by
      rw [← comap_map_eq, hm, comap_top]
    have hD : D = ⊤ := by simpa only [sup_eq_left.mpr hkD] using htop
    exact ⟨hD⟩

end Theory.SpecificGroups.AlternatingSix
