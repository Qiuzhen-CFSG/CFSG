module

public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.PGroup.RankOneInvolution
public import Theory.GroupTheory.PGroup.UniqueInvolution
public import Theory.GroupTheory.SylowCoprimeEquivalence

/-!
# Small centralizers and cyclic outer Sylow subgroups

Let L be normal in a finite group B. If the Sylow two-subgroups of C_B(L)
have order at most two and those of Out(L) are cyclic, every Sylow two-subgroup
of a subgroup H with odd intersection with L is abelian. Indeed it injects
into B/L, whose actual outer-action kernel is the image of C_B(L). The kernel
on the Sylow subgroup consequently has order at most two and is central;
its cyclic outer image then forces commutativity. In the absence of elementary
fours the Sylow subgroup is cyclic.

This is the quotient argument in GLS IV, Chapter 2, Corollary 16.6(e).
It needs no splitting of the inner-automorphism extension.
-/

public section
open Subgroup

namespace Subgroup
variable {B : Type*} [Group B] [Finite B]

private theorem pSubgroup_card_le_of_surjective {J K : Type*} [Group J] [Finite J]
    [Group K] [Finite K] (f : J →* K) (hf : Function.Surjective f)
    (hJ : ∀ S : Sylow 2 J, Nat.card S ≤ 2)
    (P : Subgroup K) (hP : IsPGroup 2 P) : Nat.card P ≤ 2 := by
  obtain ⟨R, hPR⟩ := hP.exists_le_sylow
  obtain ⟨S, rfl⟩ := Sylow.mapSurjective_surjective (f := f) hf 2 R
  exact (card_le_of_le hPR).trans ((Nat.card_le_card_of_surjective
    (f.subgroupMap (S : Subgroup J)) (f.subgroupMap_surjective _)).trans (hJ S))

omit [Finite B] in
/-- The literal quotient outer action has the image of the relative
centralizer as kernel. -/
theorem outerAction_kernel (L : Subgroup B) [L.Normal] :
    (MulAut.outerAction L).ker = (centralizer (L : Set B)).map (QuotientGroup.mk' L) := by
  rw [MulAut.outerAction, QuotientGroup.ker_map,
    MulAut.conjNormal_comap_innerSubgroup, map_sup,
    QuotientGroup.map_mk'_self, bot_sup_eq]

/-- Sylow two-subgroups of H are abelian, via the actual outer action of L. -/
theorem sylow_commutative_of_odd_intersection_cyclic_outer
    (L : Subgroup B) [L.Normal] (H : Subgroup B)
    (hodd : Odd (Nat.card (L.subgroupOf H)))
    (hJ : ∀ S : Sylow 2 (centralizer (L : Set B)), Nat.card S ≤ 2)
    (hOuter : ∀ S : Sylow 2 (MulAut.Outer L), IsCyclic S)
    (P : Sylow 2 H) : IsMulCommutative P := by
  let q := QuotientGroup.mk' L
  let f : H →* B ⧸ L := q.comp H.subtype
  have hfker : f.ker = L.subgroupOf H := by
    ext h
    exact QuotientGroup.eq_one_iff _
  have hfodd : Nat.Coprime 2 (Nat.card f.ker) := by
    rw [hfker]
    exact hodd.coprime_two_left
  let i : P →* B ⧸ L := f.comp (P : Subgroup H).subtype
  have hi : Function.Injective i :=
    injective_comp_subtype_of_coprime_ker f hfodd (P : Subgroup H) P.isPGroup'
  let a : P →* MulAut.Outer L := (MulAut.outerAction L).comp i
  obtain ⟨R, hR⟩ :=
    (P.isPGroup'.of_surjective a.rangeRestrict a.rangeRestrict_surjective).exists_le_sylow
  let : IsCyclic R := hOuter R
  let : IsCyclic a.range := isCyclic_of_le hR
  let k : a.ker →* (MulAut.outerAction L).ker :=
    (i.comp a.ker.subtype).codRestrict _ (fun x => x.property)
  have hk : Function.Injective k := fun x y he =>
    Subtype.ext (hi (congrArg Subtype.val he))
  let J := centralizer (L : Set B)
  let c : J →* (MulAut.outerAction L).ker :=
    (q.comp J.subtype).codRestrict _ (fun x => by
      rw [outerAction_kernel L]
      exact mem_map_of_mem q x.property)
  have hc : Function.Surjective c := by
    rintro ⟨x, hx⟩
    rw [outerAction_kernel L] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    exact ⟨⟨j, hj⟩, rfl⟩
  have hcard : Nat.card a.ker ≤ 2 := by
    rw [Nat.card_congr (MonoidHom.ofInjective hk).toEquiv]
    exact pSubgroup_card_le_of_surjective c hc hJ k.range
      ((P.isPGroup'.to_subgroup a.ker).of_surjective k.rangeRestrict k.rangeRestrict_surjective)
  have hcentral : a.ker ≤ center P := by
    by_cases he : Nat.card a.ker = 1
    · rw [card_eq_one.mp he]
      exact bot_le
    · exact central_of_normal_card_two a.ker (by have := Nat.card_pos (α := a.ker); omega)
  apply a.rangeRestrict.isMulCommutative_of_isCyclic_of_ker_le_center
  simpa only [MonoidHom.ker_rangeRestrict] using hcentral

/-- In rank at most one, the abelian Sylow groups above are cyclic. -/
theorem sylow_cyclic_of_odd_intersection_cyclic_outer
    (L : Subgroup B) [L.Normal] (H : Subgroup B)
    (hodd : Odd (Nat.card (L.subgroupOf H)))
    (hJ : ∀ S : Sylow 2 (centralizer (L : Set B)), Nat.card S ≤ 2)
    (hOuter : ∀ S : Sylow 2 (MulAut.Outer L), IsCyclic S)
    (hfour : ∀ V : Subgroup H, IsElementaryAbelian 2 V → Nat.card V ≠ 4)
    (P : Sylow 2 H) : IsCyclic P := by
  let : IsMulCommutative P :=
    sylow_commutative_of_odd_intersection_cyclic_outer L H hodd hJ hOuter P
  cases subsingleton_or_nontrivial P with
  | inl h => let := h; infer_instance
  | inr h =>
    let := h
    have hf : ∀ V : Subgroup P, IsElementaryAbelian 2 V → Nat.card V ≠ 4 := by
      intro V hV hc
      let := hV
      apply hfour (V.map (P : Subgroup H).subtype)
        (IsElementaryAbelian.map (A := V) (P : Subgroup H).subtype)
      simpa only [card_map_of_injective (P : Subgroup H).subtype_injective] using hc
    obtain ⟨z, hz, _, huniq⟩ := P.isPGroup'.exists_central_involution_of_no_elementary_four hf
    apply P.isPGroup'.isCyclic_of_unique_involution_of_isMulCommutative
    refine ⟨z, hz, ?_⟩
    intro x hx
    exact (huniq x (by simpa only [hx] using pow_orderOf_eq_one x)).resolve_left
      (fun he => by simp [he] at hx)

end Subgroup

namespace Sylow

/-- A supplement to an odd normal subgroup controls cyclicity of Sylow
two-subgroups through the actual odd quotient. -/
theorem isCyclic_of_odd_normal_supplement
    {G : Type*} [Group G] [Finite G]
    (N C : Subgroup G) [N.Normal] (hN : Odd (Nat.card N))
    (hgen : N ⊔ C = ⊤) (hC : ∀ S : Sylow 2 C, IsCyclic S)
    (P : Sylow 2 G) : IsCyclic P := by
  let q := QuotientGroup.mk' N
  let f : C →* G ⧸ N := q.comp C.subtype
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N x
    obtain ⟨n, hn, c, hc, he⟩ := Subgroup.mem_sup_of_normal_left.mp
      (show g ∈ N ⊔ C by rw [hgen]; trivial)
    refine ⟨⟨c, hc⟩, ?_⟩
    change q c = q g
    have hqn : q n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
    rw [← he, map_mul, hqn, one_mul]
  let S : Sylow 2 C := Classical.choice inferInstance
  let Q : Sylow 2 (G ⧸ N) := S.mapSurjective (f := f) hf
  let : IsCyclic S := hC S
  let : IsCyclic Q := isCyclic_of_surjective (f.subgroupMap (S : Subgroup C))
    (f.subgroupMap_surjective _)
  let e := Sylow.equivOfSurjectiveCoprime q (QuotientGroup.mk'_surjective N)
    (by change Nat.Coprime 2 (Nat.card (QuotientGroup.mk' N).ker)
        simpa only [QuotientGroup.ker_mk'] using hN.coprime_two_left) P Q
  exact isCyclic_of_injective e.toMonoidHom e.injective

end Sylow
