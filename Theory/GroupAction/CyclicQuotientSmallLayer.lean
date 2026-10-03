module
public import Theory.GroupAction.InvolutionCommutatorSmallLayer
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Small cyclic displacement on an abelian central quotient

Let V/Z be abelian and A≤V have index at most two. If an arbitrary element
normalizing V has its A-commutator in B≤V, whose image in V/Z has order at
most two, then its full V-commutator has image of order at most four.
The element need not be an involution, and V/Z need not be elementary.

The literal map v↦q(v)q(uvu⁻¹)⁻¹ is a homomorphism because the quotient is
abelian. Its range equals the image of [V,⟨u⟩]: finite cyclic powers and
[v,u^(n+1)]=[v,u][uvu⁻¹,u^n] establish the reverse containment. The image of
its restriction to A has order at most two. The image/kernel cardinal
bound therefore gives four, and quotient-image indices recover the exact
ambient relative-index statement.

This is the common algebraic step behind Stellmacher (8.6)(16) and (18),
printed pp.44–45. It extends the elementary involution count to the arbitrary
residual-centralizer elements required in (18).
-/

namespace Subgroup
open scoped commutatorElement IsMulCommutative

/-- For an element normalizing A, its single commutators already generate
all commutators of A with its cyclic subgroup. -/
public theorem commutator_zpowers_le_of_generator_normalizes
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (mover : G) (hmA : mover ∈ normalizer (A : Set G))
    (hgenerator : ∀ point ∈ A, ⁅point,mover⁆ ∈ B) : ⁅A,zpowers mover⁆ ≤ B := by
  have hpowers (n : ℕ) : ∀ point ∈ A, ⁅point,mover^n⁆ ∈ B := by
    induction n with
    | zero => intro point hpoint; simp
    | succ n ih =>
      intro point hpoint
      have hcpoint : mover * point * mover⁻¹ ∈ A :=
        (mem_normalizer_iff.mp hmA point).mp hpoint
      have hfactor : ⁅point,mover^(n+1)⁆ =
          ⁅point,mover⁆ * ⁅mover * point * mover⁻¹,mover^n⁆ := by
        simp only [commutatorElement_def,pow_succ']
        group
      rw [hfactor]
      exact B.mul_mem (hgenerator point hpoint) (ih _ hcpoint)
  apply commutator_le.mpr
  intro point hpoint other hother
  obtain ⟨n,rfl⟩ := mem_powers_iff_mem_zpowers.mpr hother
  exact hpowers n point hpoint

public theorem quotient_commutator_relIndex_le_four_of_index_two_small_layer
    {G : Type*} [Group G] [Finite G]
    (V A Z B : Subgroup G) (hAV : A ≤ V) (hZV : Z ≤ V) (hBV : B ≤ V)
    (hN : (Z.subgroupOf V).Normal) (habelian : ⁅V,V⁆ ≤ Z)
    (mover : G) (hmV : mover ∈ normalizer (V : Set G))
    (hsize : Nat.card V ≤ 2 * Nat.card A)
    (hsmall : Z.relIndex B ≤ 2) (hAB : ⁅A,zpowers mover⁆ ≤ B) :
    Z.relIndex (⁅V,zpowers mover⁆ ⊔ Z) ≤ 4 := by
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
  have hBbar : Nat.card Bbar ≤ 2 := by
    change Nat.card ((B.subgroupOf V).map q) ≤ 2
    rw [← relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hBV]
    exact hsmall
  have hAcard : Nat.card A' = Nat.card A :=
    Nat.card_congr (subgroupOfEquivOfLe hAV).toEquiv
  have hbound := range_card_le_twice_restriction f A' (by rwa [hAcard])
  have hsmallImage : Nat.card fA.range ≤ 2 := (card_le_of_le hfA).trans hBbar
  have hcost : Nat.card f.range = Z.relIndex (H ⊔ Z) := by
    rw [hrange,← relIndex_ker,QuotientGroup.ker_mk',relIndex_subgroupOf hHV]
    have hh := relIndex_sup_right (H.subgroupOf V) (Z.subgroupOf V)
    rw [← subgroupOf_sup hHV hZV,relIndex_subgroupOf (sup_le hHV hZV),
      relIndex_subgroupOf hHV] at hh
    exact hh.symm
  change Z.relIndex (H ⊔ Z) ≤ 4
  rw [← hcost]
  change Nat.card f.range ≤ 2 * Nat.card fA.range at hbound
  omega

end Subgroup
