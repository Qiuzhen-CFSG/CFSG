module
public import Theory.GroupTheory.ConjugacyClassSize
public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Conjugacy orbits under an actual subgroup

The orbit is expressed by literal ambient conjugators. Transport to the
ordinary conjugacy class inside the subgroup proves orbit–stabilizer with
the actual intersection centralizer. This supports the source normalizer
argument in Aschbacher–Smith 13.9.9, printed pp.972–973.
-/

@[expose] public noncomputable section
namespace Subgroup
variable {G:Type*} [Group G]

def elementOrbit (H:Subgroup G) (x:G) : Set G := {y | ∃g∈H,g*x*g⁻¹=y}

theorem self_mem_elementOrbit (H:Subgroup G) (x:G) : x∈H.elementOrbit x :=
  ⟨1,H.one_mem,by simp⟩

theorem elementOrbit_mono {H K:Subgroup G} (h:H≤K) (x:G) :
    H.elementOrbit x⊆K.elementOrbit x := by
  rintro y ⟨g,hg,he⟩
  exact ⟨g,h hg,he⟩

theorem elementOrbit_conjugate (H:Subgroup G) (x:G) (g:G) (hg:g∈H) :
    H.elementOrbit (g*x*g⁻¹)=H.elementOrbit x := by
  ext y
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a*g,H.mul_mem ha hg,by simp [mul_assoc]⟩
  · rintro ⟨a,ha,rfl⟩
    exact ⟨a*g⁻¹,H.mul_mem ha (H.inv_mem hg),by simp [mul_assoc]⟩

theorem elementOrbit_eq_of_mem {H:Subgroup G} {x y:G} (h:y∈H.elementOrbit x) :
    H.elementOrbit y=H.elementOrbit x := by
  obtain ⟨g,hg,rfl⟩:=h
  exact elementOrbit_conjugate H x g hg

theorem elementOrbit_subset {H N:Subgroup G} (hN:H≤normalizer (N:Set G))
    {x:G} (hx:x∈N) : H.elementOrbit x⊆N := by
  rintro y ⟨g,hg,rfl⟩
  exact (mem_normalizer_iff.mp (hN hg) x).mp hx

theorem elementOrbit_orderOf {H:Subgroup G} {x y:G} (h:y∈H.elementOrbit x) :
    orderOf y=orderOf x := by
  obtain ⟨g,_,rfl⟩:=h
  exact (MulAut.conj g).orderOf_eq x

theorem elementOrbit_card [Finite G] (H:Subgroup G) (x:G) (hx:x∈H) :
    Nat.card (H.elementOrbit x) * Nat.card (H⊓centralizer ({x}:Set G):Subgroup G)=Nat.card H := by
  let a:H:=⟨x,hx⟩
  let e : (ConjClasses.mk a).carrier ≃ H.elementOrbit x := {
    toFun := fun y=>⟨y.1,by
      obtain ⟨g,hg⟩:=isConj_iff.mp (show IsConj a y.1 from y.property)
      exact ⟨g,g.property,congrArg Subtype.val hg⟩⟩
    invFun := fun y=>⟨⟨y.1,by
      obtain ⟨g,hg,he⟩:=y.property
      rw [←he]
      exact H.mul_mem (H.mul_mem hg hx) (H.inv_mem hg)⟩,by
      change IsConj a _
      obtain ⟨g,hg,he⟩:=y.property
      exact isConj_iff.mpr ⟨⟨g,hg⟩,Subtype.ext he⟩⟩
    left_inv := fun _=>rfl
    right_inv := fun _=>rfl }
  have heq : centralizer ({a}:Set H)=(H⊓centralizer ({x}:Set G)).subgroupOf H := by
    ext g
    simp only [mem_centralizer_singleton_iff,mem_subgroupOf,mem_inf]
    constructor
    · intro h
      exact ⟨g.property,congrArg Subtype.val h⟩
    · intro h
      exact Subtype.ext h.2
  rw [←Nat.card_congr e,ConjClasses.nat_card_carrier_eq_index_centralizer,
    ←Nat.card_congr (subgroupOfEquivOfLe (show H⊓centralizer ({x}:Set G)≤H from inf_le_left)).toEquiv,
    ←heq]
  exact (centralizer ({a}:Set H)).index_mul_card
end Subgroup
