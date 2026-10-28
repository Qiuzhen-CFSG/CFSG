module

public import Theory.GroupTheory.SylowNormalizerFrattini

/-!
# Normalizer lifting from a Sylow subgroup of the actual preimage

A p-subgroup R whose kernel intersection is Sylow in the kernel is Sylow
in the preimage of its image. The relative Frattini argument therefore
lifts every normalizer of that image to the original normalizer of R.
The kernel may contain odd-order elements. This is the genuine local lift
used for the transposition in Aschbacher–Smith C.1.24(c), pp.130–131.
-/

public section
open Subgroup
namespace Subgroup
variable {G H : Type*} [Group G] [Group H] [Finite G]

private theorem relIndex_sup_of_normal_right (R N : Subgroup G) [N.Normal] :
    R.relIndex (R ⊔ N) = R.relIndex N := by
  have he : (R ⊓ N).relIndex R * R.relIndex (R ⊔ N) =
      (R ⊓ N).relIndex R * (R ⊓ N).relIndex N := by
    calc
      _ = (R ⊓ N).relIndex (R ⊔ N) :=
        relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
      _ = (R ⊓ N).relIndex N * N.relIndex (R ⊔ N) :=
        (relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right).symm
      _ = _ := by rw [relIndex_sup_right,inf_relIndex_left,Nat.mul_comm]
  have hi := Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)) he
  rwa [inf_relIndex_right] at hi

/-- The original R is Sylow in the preimage of q(R), including odd kernel factors. -/
theorem exists_sylow_preimage_of_kernel_intersection
    {p : ℕ} [Fact p.Prime] (R : Subgroup G) (hpR : IsPGroup p R)
    (q : G →* H) (P : Sylow p q.ker)
    (hP : (P : Subgroup q.ker).map q.ker.subtype = R ⊓ q.ker) :
    ∃ S : Sylow p ((R.map q).comap q),
      (S : Subgroup ((R.map q).comap q)) = R.subgroupOf ((R.map q).comap q) := by
  have hP' : (P : Subgroup q.ker) = R.subgroupOf q.ker := by
    apply map_injective q.ker.subtype_injective
    rw [hP,subgroupOf_map_subtype]
  have hi : ¬p ∣ R.relIndex q.ker := by
    change ¬p ∣ (R.subgroupOf q.ker).index
    rw [←hP']
    exact P.not_dvd_index
  have hi' : ¬p ∣ (R.subgroupOf ((R.map q).comap q)).index := by
    change ¬p ∣ R.relIndex ((R.map q).comap q)
    rw [comap_map_eq,relIndex_sup_of_normal_right]
    exact hi
  exact ⟨hpR.comap_subtype.toSylow hi',rfl⟩

/-- Relative Frattini lifts the actual image normalizer without an external
conjugator assumption. -/
theorem normalizer_map_eq_of_sylow_preimage
    {p : ℕ} [Fact p.Prime] (R : Subgroup G) (q : G →* H)
    (hq : Function.Surjective q) (P : Sylow p ((R.map q).comap q))
    (hP : (P : Subgroup ((R.map q).comap q)) = R.subgroupOf ((R.map q).comap q)) :
    (normalizer (R : Set G)).map q = normalizer (R.map q : Set H) := by
  apply le_antisymm (R.le_normalizer_map q)
  let U := (R.map q).comap q
  let W := (normalizer (R.map q : Set H)).comap q
  have hRU : R ≤ U := le_comap_map q R
  have hUW : U ≤ W := comap_mono (R.map q).le_normalizer
  have hWU : W ≤ normalizer (U : Set G) :=
    (comap_normalizer_eq_of_surjective (R.map q) hq).le
  have hfr := le_normalizer_sylow_sup U W hUW hWU P
  rw [hP,map_subgroupOf_eq_of_le hRU] at hfr
  have hm : W.map q ≤ (normalizer (R : Set G)).map q := by
    apply (map_mono hfr).trans
    rw [map_sup]
    apply sup_le le_rfl
    change ((R.map q).comap q).map q ≤ _
    rw [map_comap_eq_self_of_surjective hq]
    exact map_mono R.le_normalizer
  simpa only [W,map_comap_eq_self_of_surjective hq] using hm

/-- The kernel Sylow witness supplies the whole normalizer lift. -/
theorem normalizer_map_eq_of_kernel_intersection
    {p : ℕ} [Fact p.Prime] (R : Subgroup G) (hpR : IsPGroup p R)
    (q : G →* H) (hq : Function.Surjective q) (P : Sylow p q.ker)
    (hP : (P : Subgroup q.ker).map q.ker.subtype = R ⊓ q.ker) :
    (normalizer (R : Set G)).map q = normalizer (R.map q : Set H) := by
  obtain ⟨S,hS⟩ := exists_sylow_preimage_of_kernel_intersection R hpR q P hP
  exact normalizer_map_eq_of_sylow_preimage R q hq S hS

end Subgroup
