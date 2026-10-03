module
public import Theory.GroupAction.CyclicQuotientSmallLayer

/-!
# Quotient displacement bounded by a restriction index

Let V/Z be an abelian literal quotient and let an arbitrary element normalize
V. If A,B≤V and [A,⟨mover⟩]≤B, the image of [V,⟨mover⟩] modulo Z has
order at most [V:A] times the image order of B modulo Z. No involution,
exponent, or invariance assumption on A is required.

The displacement v↦q(v)q(mover*v*mover⁻¹)⁻¹ is a homomorphism because
the quotient is abelian. The cyclic-generation lemma identifies its range
with the exact ambient commutator image. Restriction to A has image inside
B modulo Z; comparing the full and restricted kernel cardinalities supplies
the factor [V:A]. Exact quotient-image indices recover the stated bound.

This source-neutral estimate gives the factor 4*4 in Stellmacher (8.6)(17),
Journal of Algebra 190 (1997), printed pp.44–45, while retaining the actual
subgroups and central quotient used by that proof.
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative

private theorem range_card_le_index_mul_restriction
    {V G : Type*} [Group V] [Finite V] [Group G] [Finite G]
    (f : V →* G) (A : Subgroup V) :
    Nat.card f.range ≤ A.index * Nat.card (f.comp A.subtype).range := by
  let g := f.comp A.subtype
  let inclusion : g.ker → f.ker := fun x => ⟨x.val.val,x.property⟩
  have hinj : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : f.ker => (z : V)) hxy
  have hker : Nat.card g.ker ≤ Nat.card f.ker :=
    Nat.card_le_card_of_injective inclusion hinj
  have hf : Nat.card V = Nat.card f.range * Nat.card f.ker := by
    rw [← index_ker,index_mul_card]
  have hg : Nat.card A = Nat.card g.range * Nat.card g.ker := by
    rw [← index_ker,index_mul_card]
  have hpos : 0 < Nat.card f.ker := Nat.card_pos
  have hbound : Nat.card f.range * Nat.card f.ker ≤
      (A.index * Nat.card g.range) * Nat.card f.ker := by
    calc
      Nat.card f.range * Nat.card f.ker = Nat.card V := hf.symm
      _ = A.index * Nat.card A := A.index_mul_card.symm
      _ = A.index * Nat.card g.range * Nat.card g.ker := by rw [hg]; ac_rfl
      _ ≤ A.index * Nat.card g.range * Nat.card f.ker := Nat.mul_le_mul_left _ hker
  exact Nat.le_of_mul_le_mul_right hbound hpos

public theorem quotient_commutator_relIndex_le_mul_of_restriction
    {G : Type*} [Group G] [Finite G]
    (V A Z B : Subgroup G) (_hAV : A ≤ V) (hZV : Z ≤ V) (hBV : B ≤ V)
    (hN : (Z.subgroupOf V).Normal) (habelian : ⁅V,V⁆ ≤ Z)
    (mover : G) (hmV : mover ∈ normalizer (V : Set G))
    (hAB : ⁅A,zpowers mover⁆ ≤ B) :
    Z.relIndex (⁅V,zpowers mover⁆ ⊔ Z) ≤ A.relIndex V * Z.relIndex B := by
  classical
  let _ := hN
  have hderived : _root_.commutator V ≤ Z.subgroupOf V := by
    intro point hpoint
    have hm : (_root_.commutator V).map V.subtype = ⁅V,V⁆ := by
      rw [_root_.commutator_def,map_commutator,← MonoidHom.range_eq_map,range_subtype]
    exact habelian (hm ▸ mem_map_of_mem V.subtype hpoint)
  let W := V ⧸ Z.subgroupOf V
  let _ : IsMulCommutative W :=
    (Normal.quotient_commutative_iff_commutator_le (N := Z.subgroupOf V)).mpr hderived
  let q : V →* W := QuotientGroup.mk' (Z.subgroupOf V)
  have hHV : ⁅V,zpowers mover⁆ ≤ V :=
    le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hmV)
  let c : V →* V := {
    toFun := fun point => ⟨mover * (point : G) * mover⁻¹,
      (mem_normalizer_iff.mp hmV point).mp point.property⟩
    map_one' := by apply Subtype.ext; simp
    map_mul' := by intro x y; apply Subtype.ext; simp [mul_assoc] }
  let f : V →* W := q * (q.comp c)⁻¹
  have hf (point : V) : f point = q ⟨⁅(point : G),mover⁆,
      hHV (commutator_mem_commutator point.property (mem_zpowers mover))⟩ := by
    change q point * (q (c point))⁻¹ = _
    rw [← map_inv,← map_mul]
    congr 1
    apply Subtype.ext
    simp [c,commutatorElement_def,mul_assoc]
  let H := ⁅V,zpowers mover⁆
  have hrange : f.range = (H.subgroupOf V).map q := by
    apply le_antisymm
    · rintro point ⟨source,rfl⟩
      rw [hf]
      exact mem_map_of_mem q (commutator_mem_commutator source.property (mem_zpowers mover))
    · let preimage := (f.range.comap q).map V.subtype
      have hsingle (point : G) (hpoint : point ∈ V) : ⁅point,mover⁆ ∈ preimage := by
        refine ⟨⟨⁅point,mover⁆,hHV
          (commutator_mem_commutator hpoint (mem_zpowers mover))⟩,?_,rfl⟩
        exact ⟨⟨point,hpoint⟩,hf ⟨point,hpoint⟩⟩
      have hpre : H ≤ preimage :=
        commutator_zpowers_le_of_generator_normalizes V preimage mover hmV hsingle
      rintro point ⟨source,hsource,rfl⟩
      obtain ⟨lift,hlift,heq⟩ := hpre hsource
      exact (show lift = source from Subtype.ext heq) ▸ hlift
  let A' := A.subgroupOf V
  let fA := f.comp A'.subtype
  let Bbar := (B.subgroupOf V).map q
  have hfA : fA.range ≤ Bbar := by
    rintro point ⟨source,rfl⟩
    change f source.val ∈ Bbar
    rw [hf]
    exact mem_map_of_mem q (hAB (commutator_mem_commutator source.property (mem_zpowers mover)))
  have hBbar : Nat.card Bbar = Z.relIndex B := by
    change Nat.card ((B.subgroupOf V).map q) = Z.relIndex B
    rw [← relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hBV]
  have hbound := range_card_le_index_mul_restriction f A'
  have hsmallImage : Nat.card fA.range ≤ Z.relIndex B :=
    (card_le_of_le hfA).trans_eq hBbar
  have hcost : Nat.card f.range = Z.relIndex (H ⊔ Z) := by
    rw [hrange,← relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hHV]
    have hh := relIndex_sup_right (H.subgroupOf V) (Z.subgroupOf V)
    rw [← subgroupOf_sup hHV hZV,relIndex_subgroupOf (sup_le hHV hZV),
      relIndex_subgroupOf hHV] at hh
    exact hh.symm
  rw [← hcost]
  exact hbound.trans (Nat.mul_le_mul_left _ hsmallImage)

end Subgroup
