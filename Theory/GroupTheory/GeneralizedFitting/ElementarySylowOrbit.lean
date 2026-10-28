module
public import Theory.GroupTheory.ConjugateOrbitIndexTwo
public import Theory.GroupTheory.SylowNormalJoinIntersection
public import Theory.ElementaryAbelian.Join
public import Theory.ElementaryAbelian.Injective

/-!
# Elementary Sylow subgroups of a two-component orbit

An index-two component normalizer identifies the normal component orbit with
the join of two commuting actual conjugate components. Each factor is normal
inside this join. The literal Sylow-intersection theorem for a normal product
therefore writes its Sylow subgroup as the join of the elementary intersections
with the two factors. Their commutation makes that join elementary. The
surjective-image theorem retains the supplied homomorphism.

Source application: Aschbacher--Smith G.10.15, printed p.362.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Theory.GroupTheory.ExchangedOrbit

private theorem elementary_sylow_equiv
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) (h : ∀ P : Sylow 2 A, IsElementaryAbelian 2 P)
    (Q : Sylow 2 B) : IsElementaryAbelian 2 Q := by
  let P := Q.mapSurjective (f:=e.symm.toMonoidHom) e.symm.surjective
  let : IsElementaryAbelian 2 P := h P
  let eq : Q ≃* P := e.symm.subgroupMap (Q:Subgroup B)
  exact IsElementaryAbelian.of_injective eq.toMonoidHom eq.injective

private theorem elementary_sylow_normal_product
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) [A.Normal] [B.Normal] (hAB : A ⊔ B = ⊤)
    (hc : A ≤ centralizer (B:Set G))
    (hA : ∀ P : Sylow 2 A, IsElementaryAbelian 2 P)
    (hB : ∀ P : Sylow 2 B, IsElementaryAbelian 2 P)
    (S : Sylow 2 G) : IsElementaryAbelian 2 S := by
  have hE (C : Subgroup G) [C.Normal]
      (hC : ∀ P : Sylow 2 C, IsElementaryAbelian 2 P) :
      IsElementaryAbelian 2 ((S:Subgroup G) ⊓ C : Subgroup G) := by
    obtain ⟨Q,hQ⟩ := S.exists_sylow_map_eq_inf_of_normal C
    let : IsElementaryAbelian 2 Q := hC Q
    exact hQ ▸ (IsElementaryAbelian.map_subtype (H := (Q:Subgroup C)))
  let : IsElementaryAbelian 2 ((S:Subgroup G) ⊓ A : Subgroup G) := hE A hA
  let : IsElementaryAbelian 2 ((S:Subgroup G) ⊓ B : Subgroup G) := hE B hB
  have he : (S:Subgroup G) = ((S:Subgroup G) ⊓ A) ⊔ ((S:Subgroup G) ⊓ B) := by
    simpa only [hAB, inf_top_eq] using S.inf_sup_eq_sup_inf_normal A B
  have hs : IsElementaryAbelian 2
      (((S:Subgroup G) ⊓ A) ⊔ ((S:Subgroup G) ⊓ B) : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer (fun b hb a ha => (hc ha.2 b hb.2).symm)
  exact he.symm ▸ hs

/-- A two-component orbit whose original component has elementary Sylow
two-subgroups has elementary Sylow two-subgroups itself. -/
theorem orbit_sylow_elementary
    {G : Type*} [Group G] [Finite G] {L : Subgroup G} (hL : IsComponent G L)
    (hi : (normalizer (L:Set G)).index = 2)
    (hE : ∀ P : Sylow 2 L, IsElementaryAbelian 2 P)
    (S : Sylow 2 (componentOrbit L ⊤)) : IsElementaryAbelian 2 S := by
  classical
  have hex : ∃ t : G, t ∉ normalizer (L:Set G) := by
    by_contra! hn
    have ht : normalizer (L:Set G) = ⊤ := top_unique (fun t _ => hn t)
    rw [ht, index_top] at hi
    omega
  obtain ⟨t,ht⟩ := hex
  let H := componentOrbit L ⊤
  let K := L.map (MulAut.conj t).toMonoidHom
  have hprod : H = L ⊔ K := componentOrbit_eq_sup_of_index_two L ⊤ (normalizer (L:Set G))
    (by simpa only [relIndex_top_right] using hi) inf_le_right (mem_top t) ht
  have hLH : L ≤ H := le_componentOrbit L ⊤
  have hKH : K ≤ H := hprod ▸ le_sup_right
  have hne : K ≠ L := fun he => ht (mem_normalizer_iff_map_conj_eq.mpr he)
  have hc : L ≤ centralizer (K:Set G) := commutator_eq_bot_iff_le_centralizer.mp
    (hL.commutator_eq_bot_of_ne (hL.map_conj t) hne.symm)
  let A := L.subgroupOf H
  let B := K.subgroupOf H
  let : A.Normal := (normal_subgroupOf_iff_le_normalizer hLH).mpr (by
    rw [hprod]
    exact sup_le L.le_normalizer ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _)))
  let : B.Normal := (normal_subgroupOf_iff_le_normalizer hKH).mpr (by
    rw [hprod]
    exact sup_le (hc.trans (Subgroup.centralizer_le_normalizer _)) K.le_normalizer)
  have hAB : A ⊔ B = ⊤ := by
    rw [←subgroupOf_sup hLH hKH,←hprod,subgroupOf_self]
  have hEK (P : Sylow 2 K) : IsElementaryAbelian 2 P :=
    elementary_sylow_equiv ((MulAut.conj t).subgroupMap L) hE P
  apply elementary_sylow_normal_product A B hAB
  · intro a ha b hb
    exact Subtype.ext (hc ha b hb)
  · exact elementary_sylow_equiv (subgroupOfEquivOfLe hLH).symm hE
  · exact elementary_sylow_equiv (subgroupOfEquivOfLe hKH).symm hEK

/-- Elementary Sylow two-subgroups pass through the actual surjective map. -/
theorem elementary_sylow_image
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f)
    (h : ∀ P : Sylow 2 A, IsElementaryAbelian 2 P) (Q : Sylow 2 B) :
    IsElementaryAbelian 2 Q := by
  obtain ⟨P,rfl⟩ := Sylow.mapSurjective_surjective hf 2 Q
  let : IsElementaryAbelian 2 P := h P
  exact IsElementaryAbelian.map f

end Theory.GroupTheory.ExchangedOrbit
