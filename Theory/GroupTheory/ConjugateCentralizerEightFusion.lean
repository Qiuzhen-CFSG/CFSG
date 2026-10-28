module
public import Theory.GroupTheory.ElementaryEightTwoStabilizers
public import Theory.GroupAction.SubgroupConjugation

/-!
# Two conjugate point stabilizers on an elementary eight

Suppose the centralizer of t splits as K times its central involution t,
and every four in K has transitive normalizer on its nonidentity elements.
On an elementary eight F, this supplies a transitive three-point action
fixing t. Conjugating the same construction supplies that action at every
t-conjugate point in F. If these form the four-point complement of F∩K,
a Sylow of N(F) cannot fix t.
Source: Aschbacher--Smith 2.5.21, printed p.565.
-/
public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

 theorem elementaryEight_conjugate_centralizers_false
    (K F : Subgroup G) [IsElementaryAbelian 2 F] (hF : Nat.card F=8)
    (t : G) (htF : t∈F) (htK : t∉K)
    (hFC : F≤centralizer ({t}:Set G))
    (hC : centralizer ({t}:Set G)=K⊔zpowers t)
    (havoid : ∀k∈K, ¬IsConj t k)
    (hclass : ∀u∈F, IsConj t u ↔ u∉K)
    (hfour : ∀ A : Subgroup G, A≤K → IsKleinFour A →
      ∀ a∈A, ∀ b∈A, a≠1 → b≠1 →
        ∃n∈K⊓normalizer (A:Set G), MulAut.conj n a=b)
    (P : Sylow 2 (normalizer (F:Set G)))
    (hfix : ∀a∈(P:Subgroup (normalizer (F:Set G))), MulAut.conj (a:G) t=t) : False := by
  classical
  let Ω : Set G := {u | u∈F ∧ IsConj t u}
  have hΩdiff : Ω=(F:Set G)\(K:Set G) := by
    ext u
    exact and_congr_right (fun hu => hclass u hu)
  have hΩ : Ω.ncard=4 := by
    rw [hΩdiff]
    exact (Subgroup.elementaryEight_centralizer_point_stabilizer_transitive
      K F hF t htF htK hFC hC hfour).1
  have htΩ : t∈Ω := ⟨htF,IsConj.refl t⟩
  have hstable : ∀n∈normalizer (F:Set G), ∀u∈Ω, MulAut.conj n u∈Ω := by
    intro n hn u hu
    refine ⟨?_,hu.2.trans (isConj_iff.mpr ⟨n,rfl⟩)⟩
    exact ((mem_normalizer_iff.mp hn) u).mp hu.1
  have htrans (u:G) (hu:u∈Ω) :
      ∀y∈Ω, ∀z∈Ω, y≠u → z≠u →
        ∃a∈normalizer (F:Set G), MulAut.conj a u=u ∧ MulAut.conj a y=z := by
    obtain ⟨g,hg⟩ := isConj_iff.mp hu.2
    change MulAut.conj g t=u at hg
    let V := F.conjBy g⁻¹
    let α := MulAut.conj g⁻¹
    have hback (a:G) : MulAut.conj g (α a)=a := by
      change g*(g⁻¹*a*(g⁻¹)⁻¹)*g⁻¹=a
      group
    have hforward (a:G) : α (MulAut.conj g a)=a := by
      change g⁻¹*(g*a*g⁻¹)*(g⁻¹)⁻¹=a
      group
    have hut : α u=t := by rw [←hg]; exact hforward t
    have htV : t∈V := by
      rw [←hut]
      exact mem_map_of_mem α.toMonoidHom hu.1
    let : IsElementaryAbelian 2 V := IsElementaryAbelian.map α.toMonoidHom
    have hV : Nat.card V=8 := by
      change Nat.card (F.map α.toMonoidHom)=8
      rw [card_map_of_injective α.injective,hF]
    have hVC : V≤centralizer ({t}:Set G) := by
      rintro _ ⟨a,ha,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      change α a*t=t*α a
      rw [←hut,←map_mul,←map_mul]
      exact congrArg α ((F.le_centralizer ha) u hu.1).symm
    have hnotK (a:G) (ha:IsConj t a) : α a∉K := by
      intro hk
      exact havoid (α a) hk (ha.trans (isConj_iff.mpr ⟨g⁻¹,rfl⟩))
    have hlocal := (Subgroup.elementaryEight_centralizer_point_stabilizer_transitive
      K V hV t htV htK hVC hC hfour).2
    intro y hy z hz hyu hzu
    have hyV : α y∈V := mem_map_of_mem α.toMonoidHom hy.1
    have hzV : α z∈V := mem_map_of_mem α.toMonoidHom hz.1
    have hyt : α y≠t := by
      intro hh
      apply hyu
      calc y=MulAut.conj g (α y) := (hback y).symm
           _=u := by rw [hh,hg]
    have hzt : α z≠t := by
      intro hh
      apply hzu
      calc z=MulAut.conj g (α z) := (hback z).symm
           _=u := by rw [hh,hg]
    obtain ⟨a,ha,hat,hay⟩ := hlocal (α y) hyV (α z) hzV
      (hnotK y hy.2) (hnotK z hz.2) hyt hzt
    let b := MulAut.conj g a
    have hbN : b∈normalizer (F:Set G) := by
      have hh := mem_map_of_mem (MulAut.conj g).toMonoidHom ha
      rw [map_equiv_normalizer_eq] at hh
      have hVF : V.map (MulAut.conj g).toMonoidHom=F := by
        apply le_antisymm
        · rintro _ ⟨a,⟨v,hv,rfl⟩,rfl⟩
          change MulAut.conj g (α v)∈F
          rw [hback]
          exact hv
        · intro v hv
          exact ⟨α v,mem_map_of_mem α.toMonoidHom hv,hback v⟩
      rw [hVF] at hh
      exact hh
    have hconj (v:G) : MulAut.conj b v=MulAut.conj g (MulAut.conj a (α v)) := by
      change (g*a*g⁻¹)*v*(g*a*g⁻¹)⁻¹=g*(a*(g⁻¹*v*(g⁻¹)⁻¹)*a⁻¹)*g⁻¹
      group
    refine ⟨b,hbN,?_,?_⟩
    · rw [hconj,hut,hat,hg]
    · rw [hconj,hay,hback]
  obtain ⟨u,hu,hut⟩ := Set.exists_ne_of_one_lt_ncard (by omega : 1<Ω.ncard) t
  exact Subgroup.false_of_four_set_two_transitive_stabilizers
    (normalizer (F:Set G)) Ω hΩ hstable P t u htΩ hu hut.symm hfix
    (htrans t htΩ) (htrans u hu)
end Theory.GroupTheory
