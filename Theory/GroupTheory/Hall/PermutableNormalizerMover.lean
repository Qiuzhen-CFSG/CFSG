module
public import Theory.GroupTheory.Hall.ConjugateTorusConstruction
public import Theory.GroupTheory.Hall.PermutableActors
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.CyclicSubgroupNormalizer

/-!
# A Sylow normalizer element outside a prescribed normal subgroup

Let an odd subgroup D permute with a Sylow two-subgroup T, with solvable
join. If D lies in a normal subgroup N, every T-coset modulo T intersection N
has a representative normalizing D. Here we retain an outside representative.

Choose an odd Hall subgroup containing D inside (D join T) intersection N.
Hall conjugacy factors the original Sylow through its intersection with this
normal overlap and the Hall normalizer. Permutability makes every Sylow
normalizer of the chosen Hall subgroup normalize D itself. For cyclic D,
the same normalizer identifies its kernels on conjugate ambient subgroups,
since every subgroup of D is characteristic.

Source: Hall's conjugacy theorem, applied to the paired J₁ step in
Aschbacher--Smith 5.1.13, printed p.636 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Subgroup.OddHall
variable {G : Type*} [Group G] [Finite G]

private theorem normalized_sylow (T : Sylow 2 G) (L : Subgroup G)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L := by
  let J := L ⊔ (T : Subgroup G)
  have hLJ : L ≤ J := le_sup_left
  let : (L.subgroupOf J).Normal :=
    normal_subgroupOf_of_le_normalizer (sup_le L.le_normalizer hTL)
  obtain ⟨P, hP⟩ :=
    (T.subtype (show (T : Subgroup G) ≤ J from le_sup_right)).exists_subgroupOf_eq_of_normal
      (L.subgroupOf J)
  let e := subgroupOfEquivOfLe hLJ
  refine ⟨P.mapSurjective (f := e.toMonoidHom) e.surjective, ?_⟩
  change (P : Subgroup (L.subgroupOf J)).map e.toMonoidHom = _
  rw [hP]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨⟨⟨x, hLJ x.property⟩, x.property⟩, hx, rfl⟩

/-- A permuting odd subgroup with solvable Sylow join has a Sylow
normalizer element outside every proper normal overgroup it lies in. -/
theorem permutable_normalizer_mover (T : Sylow 2 G) (D N : Subgroup G) [N.Normal]
    [Group.IsSolvable (D ⊔ (T : Subgroup G) : Subgroup G)]
    (ho : Odd (Nat.card D)) (hDN : D ≤ N)
    (hperm : (D : Set G) * (T : Set G) = (T : Set G) * (D : Set G))
    (s : G) (hs : s ∈ T) (hsN : s ∉ N) :
    ∃ t : G, t ∈ T ∧ t ∉ N ∧ t ∈ normalizer (D : Set G) := by
  let J := D ⊔ (T : Subgroup G)
  let K := J ⊓ N
  let R := (T : Subgroup G) ⊓ K
  have hTK : (T : Subgroup G) ≤ normalizer (K : Set G) :=
    (le_inf ((show (T : Subgroup G) ≤ J from le_sup_right).trans J.le_normalizer)
      le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  let : Group.IsSolvable K := Group.isSolvable_of_isSolvable_injective
    (inclusion_injective (show K ≤ J from inf_le_left))
  obtain ⟨P,hP⟩ := normalized_sylow T K hTK
  have hPR : (P : Subgroup K).map K.subtype = R := by
    rw [hP,subgroupOf_map_subtype]
  obtain ⟨F,hDF,hFK,hHall⟩ := exists_hall_containing_odd K D inferInstance
    (le_inf le_sup_left hDN) ho
  have hfac := normal_sylow_frattini K R T F inferInstance inf_le_left hTK P hPR hFK hHall
  have hsprod : s ∈ (R : Set G) * (((T : Subgroup G) ⊓ normalizer (F : Set G)) : Set G) :=
    hfac ▸ hs
  obtain ⟨r,hr,t,ht,hrt⟩ := hsprod
  have htN : t ∉ N := by
    intro htn
    exact hsN (hrt ▸ N.mul_mem hr.2.2 htn)
  have hoddF : Odd (Nat.card F) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe hFK).toEquiv]
    exact odd_hall_odd hHall
  have hdis : Disjoint (T : Subgroup G) F := by
    obtain ⟨k,hk⟩ := T.isPGroup'.exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hk]
    exact (Nat.coprime_two_left.mpr hoddF).pow_left k
  exact ⟨t,ht.1,htN,normalizer_permutable_subgroup D T F hDF hdis hperm ht⟩
end Subgroup.OddHall

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A normalizer of a cyclic actor makes its kernels on conjugate
subgroups identical. -/
theorem cyclic_conjugate_centralizers_eq (D R : Subgroup G) [IsCyclic D]
    (t : G) (ht : t ∈ normalizer (D : Set G)) :
    D ⊓ centralizer (R : Set G) = D ⊓ centralizer (R.map (MulAut.conj t).toMonoidHom : Set G) := by
  let Z := D ⊓ centralizer (R : Set G)
  have htZ : t ∈ normalizer (Z : Set G) :=
    normalizer_le_normalizer_of_le_cyclic Z D inf_le_left ht
  have hz : Z.map (MulAut.conj t).toMonoidHom = Z :=
    mem_normalizer_iff_map_conj_eq.mp htZ
  have hle : Z ≤ D ⊓ centralizer (R.map (MulAut.conj t).toMonoidHom : Set G) := by
    refine le_inf inf_le_left ?_
    rw [←hz]
    exact (map_mono (f := (MulAut.conj t).toMonoidHom)
      (show Z ≤ centralizer (R : Set G) from inf_le_right)).trans
      (map_centralizer_le_centralizer_image _ _)
  apply eq_of_le_of_card_ge hle
  have hpre : (D ⊓ centralizer (R.map (MulAut.conj t).toMonoidHom : Set G)).map
      (MulAut.conj t⁻¹).toMonoidHom ≤ Z := by
    rintro _ ⟨d,hd,rfl⟩
    refine ⟨(mem_normalizer_iff.mp ((normalizer (D : Set G)).inv_mem ht) d).mp hd.1,?_⟩
    intro r hr
    apply (MulAut.conj t).injective
    have hc := hd.2 ((MulAut.conj t) r) (mem_map_of_mem _ hr)
    simpa only [map_mul,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,inv_inv,mul_assoc,
      mul_inv_cancel_left,inv_mul_cancel_left,mul_inv_cancel,mul_one,inv_mul_cancel,one_mul] using hc
  have hcard := card_le_of_le hpre
  rwa [card_map_of_injective (MulAut.conj t⁻¹).injective] at hcard
end Subgroup
