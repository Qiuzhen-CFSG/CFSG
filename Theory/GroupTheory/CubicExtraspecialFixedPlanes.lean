module

public import Theory.GroupTheory.CubicExtraspecialMaxAbelian

/-!
# Fixed planes in the ternary Sylow product

The maximal abelian intersection V∩D has order27 and centralizes only itself
inside extraspecial D. Commutation with an outside element gives a nonzero
homomorphism to the central cubic line, so its kernel has order9. The preceding
outside-centralizer property identifies this kernel with the full fixed group
in V. Multiplication by V does not change that fixed group, covering every
element of VD outside V.
Source: Aschbacher, Sporadic Groups (1994),45.9,printed p246.
-/

public section
open Subgroup
open scoped commutatorElement IsMulCommutative Pointwise
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem cubic_maximal_abelian_fixed_nine (V D W:Subgroup G) [IsMulCommutative V] [IsExtraspecial 3 D]
    (hD:Nat.card D=243) (hI:Nat.card (V⊓D:Subgroup G)=27) (hVD:V≤normalizer (D:Set G))
    (hW:Nat.card W=3) (hcom:⁅D,D⁆≤W) (hcen:W≤centralizer (D:Set G))
    (hfix:∀d∈D,d∉V→V⊓centralizer ({d}:Set G)≤D)
    (d:G) (hd:d∈D) (hdV:d∉V) : Nat.card (V⊓centralizer ({d}:Set G):Subgroup G)=9 := by
  let A:=V⊓D
  let C:=V⊓centralizer ({d}:Set G)
  have hself: D⊓centralizer (A:Set G)=A:=
    (cubic_extraspecial_intersection_and_normalizer V D hD hI hVD).1
  let f:A→*W:={
    toFun a:=⟨⁅(a:G),d⁆,hcom (commutator_mem_commutator a.property.2 hd)⟩
    map_one':=by apply Subtype.ext;simp
    map_mul' a b:=by
      apply Subtype.ext
      change ⁅(a:G)*(b:G),d⁆=⁅(a:G),d⁆*⁅(b:G),d⁆
      have hb:=hcom (commutator_mem_commutator b.property.2 hd)
      have hc:=mem_centralizer_iff.mp (hcen hb) a a.property.2
      rw [commutatorElement_mul_left_eq_conj_mul,hc]
      simp only [mul_inv_cancel_right]
      have haD:⁅(a:G),d⁆∈D:=le_normalizer_iff_commutator_le_left.mp D.le_normalizer
        (commutator_mem_commutator a.property.2 hd)
      exact (mem_centralizer_iff.mp (hcen hb) _ haD).symm }
  have hk:f.ker=C.subgroupOf A:=by
    ext a
    change (⟨⁅(a:G),d⁆,_⟩:W)=1 ↔ (a:G)∈C
    rw [Subtype.ext_iff]
    change ⁅(a:G),d⁆=1 ↔ (a:G)∈V⊓centralizer ({d}:Set G)
    rw [commutatorElement_eq_one_iff_mul_comm,mem_inf,mem_centralizer_singleton_iff]
    exact ⟨fun h=>⟨a.property.1,h⟩,fun h=>h.2⟩
  have hr:Nat.card f.range=3:=by
    have hdvd:Nat.card f.range∣3:=hW ▸ f.range.card_subgroup_dvd_card
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hc|hc
    · have hb:f.range=⊥:=card_eq_one.mp hc
      have hdc:d∈centralizer (A:Set G):=by
        intro a ha
        have hf:f ⟨a,ha⟩=1:=by
          have hm:f ⟨a,ha⟩∈f.range:=⟨⟨a,ha⟩,rfl⟩
          simpa only [hb,mem_bot] using hm
        have hh:⁅a,d⁆=1:=congrArg Subtype.val hf
        exact commutatorElement_eq_one_iff_mul_comm.mp hh
      exact (hdV (hself.le ⟨hd,hdc⟩).1).elim
    · exact hc
  have hCA:C≤A:=le_inf inf_le_left (hfix d hd hdV)
  have hh:=f.ker.card_mul_index
  rw [index_ker,hr,hk,Nat.card_congr (subgroupOfEquivOfLe hCA).toEquiv] at hh
  change Nat.card C*3=Nat.card (V⊓D:Subgroup G) at hh
  rw [hI] at hh
  change Nat.card C=9
  omega
end Subgroup

namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
open scoped Pointwise IsMulCommutative
theorem cubic_sup_outside_fixed_nine (V D W:Subgroup G) [IsMulCommutative V] [IsExtraspecial 3 D]
    (hD:Nat.card D=243) (hI:Nat.card (V⊓D:Subgroup G)=27) (hVD:V≤normalizer (D:Set G))
    (hW:Nat.card W=3) (hcom:⁅D,D⁆≤W) (hcen:W≤centralizer (D:Set G))
    (hfix:∀d∈D,d∉V→V⊓centralizer ({d}:Set G)≤D)
    (x:G) (hx:x∈V⊔D) (hxV:x∉V) : Nat.card (V⊓centralizer ({x}:Set G):Subgroup G)=9 := by
  have hDV: D≤normalizer (V:Set G):=(cubic_extraspecial_intersection_and_normalizer V D hD hI hVD).2
  have hh:x∈(V:Set G)*(D:Set G):=by
    rw [←coe_mul_of_right_le_normalizer_left V D hDV]
    exact hx
  obtain ⟨v,hv,d,hd,rfl⟩:=hh
  have hdV:d∉V:=fun hh=>hxV (V.mul_mem hv hh)
  have he:V⊓centralizer ({v*d}:Set G)=V⊓centralizer ({d}:Set G):=by
    ext a
    simp only [mem_inf,mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨ha,hax⟩
      refine ⟨ha,?_⟩
      have hav:a*v=v*a:=(V.le_centralizer hv a ha)
      rw [←mul_assoc,hav,mul_assoc,mul_assoc] at hax
      exact mul_left_cancel hax
    · rintro ⟨ha,had⟩
      refine ⟨ha,?_⟩
      have hav:a*v=v*a:=(V.le_centralizer hv a ha)
      rw [←mul_assoc,hav,mul_assoc,had,←mul_assoc]
  rw [he]
  exact cubic_maximal_abelian_fixed_nine V D W hD hI hVD hW hcom hcen hfix d hd hdV
end Subgroup
