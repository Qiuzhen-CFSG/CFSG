module
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors.Model
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.Placement
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.OuterActors.Coordinates
public import Theory.SpecificGroups.PSL3Three.Generators
/-!
# One inner four-group reference in the PSL₃(3) graph extension

We construct an elementary four-group in SL₃(3), place its literal inner
image in a 32-element Sylow subgroup and a conjugate graph centralizer,
and verify all six geometric clauses consumed by inner-actor placement.

The checked coordinates and Sylow subgroup are reused from
`OuterActors.Coordinates`; its matrix embedding agrees definitionally with
`InnerActors.inner`. The actor consists of matrix indices 0, 4, 8 and 12.
The local graph involution has coordinate (13, true). Small kernel-checked
coordinate tests establish the centralizer containment and intersection order.
A local commutator has cube one and eighth power different from one, excluding
the actor from the intrinsic normal two-core, whose order is eight.
Two explicit words recover the generators of SL₃(3); adjoining the graph
involution then generates the actual extension.

The matrix table is originally from `PSL3Three.SylowInvolutions`, preserved
and exposed by `OuterActors.Coordinates.Table`. The two word witnesses and
local commutator were found by the parent task's GAP diagnostics and are
certified here without using those diagnostics as proof premises.

Source: Aschbacher–Smith E.1.2, E.1.5 and E.1.14(7), printed pp.209–210,
214; Asc82a, Lemma 4.11. The reference discharges the finite premises of
`centralizerPlacement_of_inner_seed`; that consumer is checked separately
to preserve the direction of imports.
-/

open Subgroup Theory.GroupTheory
open Matrix.PSL3Three Matrix.PSL3Three.GraphLocalQuotients
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors
namespace Reference
set_option maxRecDepth 10000

abbrev O := OuterActors.standardSubgroup
abbrev c := OuterActors.localConjugator true

theorem inner_eq : inner = OuterActors.inner := rfl

def actorIndex : Fin 4 → Fin 16 := ![0,4,8,12]
def actorElement (i : Fin 4) : SL := OuterActors.twoElement (actorIndex i)
def actorProduct : Fin 4 → Fin 4 → Fin 4 :=
  ![![0,1,2,3], ![1,0,3,2], ![2,3,0,1], ![3,2,1,0]]
theorem actor_mul (i j : Fin 4) : actorElement (actorProduct i j) =
    actorElement i * actorElement j := by
  apply Subtype.ext
  revert i j
  decide +kernel
theorem actor_sq (i : Fin 4) : actorElement i * actorElement i = 1 := by
  apply Subtype.ext
  revert i
  decide +kernel
def actor : Subgroup SL where
  carrier := Set.range actorElement
  one_mem' := ⟨0, Subtype.ext (by decide +kernel)⟩
  mul_mem' := by
    rintro _ _ ⟨i,rfl⟩ ⟨j,rfl⟩
    exact ⟨actorProduct i j, actor_mul i j⟩
  inv_mem' := by
    rintro _ ⟨i,rfl⟩
    exact ⟨i, eq_inv_of_mul_eq_one_left (actor_sq i)⟩
theorem actor_elementary : IsElementaryAbelian 2 actor where
  toIsMulCommutative := ⟨⟨by
    rintro ⟨_,i,rfl⟩ ⟨_,j,rfl⟩
    apply Subtype.ext
    change actorElement i * actorElement j = actorElement j * actorElement i
    rw [← actor_mul, ← actor_mul]
    have h : ∀ i j, actorProduct i j = actorProduct j i := by decide +kernel
    rw [h]⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
    rintro ⟨_,i,rfl⟩
    apply Subtype.ext
    change actorElement i ^ 2 = 1
    simpa only [pow_two] using actor_sq i)
theorem actor_injective : Function.Injective actorElement := by
  have h : ∀ i j, (actorElement i).val = (actorElement j).val → i = j := by decide +kernel
  exact fun _ _ h' => h _ _ (congrArg Subtype.val h')
theorem actor_card : Nat.card actor = 4 := by
  let e : Fin 4 ≃ actor := Equiv.ofBijective
    (fun i => ⟨actorElement i, ⟨i,rfl⟩⟩)
    ⟨fun _ _ h => actor_injective (congrArg Subtype.val h), by
      rintro ⟨_,i,rfl⟩
      exact ⟨i,rfl⟩⟩
  rw [← Nat.card_congr e]
  simp
theorem inner_actorElement (i : Fin 4) : inner (actorElement i) =
    OuterActors.element (actorIndex i, false) := by
  simp [inner_eq, OuterActors.element, OuterActors.pair, actorElement]
theorem actor_le : actor.map inner ≤ O := by
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
  rw [inner_actorElement]
  exact OuterActors.element_mem_standardSubgroup _

def localTest (i : OuterActors.Index) : Prop :=
  OuterActors.multiply i (13,true) = OuterActors.multiply (13,true) i
instance (i : OuterActors.Index) : Decidable (localTest i) := inferInstanceAs (Decidable (_ = _))
theorem mem_local_iff (i : OuterActors.Index) :
    OuterActors.element i ∈ localSubgroup c ↔ localTest i := by
  rw [OuterActors.localSubgroup_marker, mem_centralizer_singleton_iff]
  exact (OuterActors.element_commute_iff _ _)
theorem actor_local : actor.map inner ≤ localSubgroup c := by
  rintro _ ⟨_,⟨i,rfl⟩,rfl⟩
  rw [inner_actorElement, mem_local_iff]
  revert i
  decide +kernel
theorem centralizer_local : O ⊓ centralizer (actor.map inner : Set G) ≤ localSubgroup c := by
  rintro _ ⟨⟨i,rfl⟩,hc⟩
  have hz := hc (inner (actorElement 1)) (mem_map_of_mem _ (show actorElement 1 ∈ actor from ⟨1,rfl⟩))
  have hb := hc (inner (actorElement 2)) (mem_map_of_mem _ (show actorElement 2 ∈ actor from ⟨2,rfl⟩))
  rw [inner_actorElement] at hz hb
  have hz' := (OuterActors.element_commute_iff i (actorIndex 1,false)).mp hz.symm
  have hb' := (OuterActors.element_commute_iff i (actorIndex 2,false)).mp hb.symm
  apply (mem_local_iff i).mpr
  have h : ∀ i : OuterActors.Index,
    OuterActors.multiply i (actorIndex 1,false) = OuterActors.multiply (actorIndex 1,false) i →
    OuterActors.multiply i (actorIndex 2,false) = OuterActors.multiply (actorIndex 2,false) i →
    localTest i := by decide +kernel
  exact h i hz' hb'

theorem intersection_card : Nat.card (O.subgroupOf (localSubgroup c)) = 16 := by
  let f : {i : OuterActors.Index // localTest i} → O.subgroupOf (localSubgroup c) :=
    fun i => ⟨⟨OuterActors.element i.val, (mem_local_iff i.val).mpr i.property⟩,
      ⟨i.val,rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      apply Subtype.ext
      apply OuterActors.element_injective
      exact congrArg (fun x : O.subgroupOf (localSubgroup c) => x.val.val) hij
    · rintro ⟨⟨x,hx⟩,hxO⟩
      obtain ⟨i,hi⟩ := hxO
      have he : OuterActors.element i = x := hi
      refine ⟨⟨i, (mem_local_iff i).mp (he ▸ hx)⟩, ?_⟩
      exact Subtype.ext (Subtype.ext he)
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  decide +kernel

theorem inner_mem_local_of_matrix (x : SL)
    (hx : x * OuterActors.twoElement 13 = OuterActors.twoElement 13 *
      Matrix.PSL3.OuterSolvable.graphSL (ZMod 3) x) : inner x ∈ localSubgroup c := by
  rw [OuterActors.localSubgroup_marker, mem_centralizer_singleton_iff, inner_eq]
  change OuterActors.inner x * (OuterActors.inner (OuterActors.twoElement 13) * graphElement) =
    (OuterActors.inner (OuterActors.twoElement 13) * graphElement) * OuterActors.inner x
  rw [mul_assoc _ graphElement, OuterActors.graphElement_mul_inner, ← mul_assoc,
    ← mul_assoc, ← map_mul, ← map_mul, hx]

def coreWitness : SL := ⟨!![0,1,2; 2,0,1; 0,0,1], by decide⟩
def generationWitness : SL := ⟨!![0,0,2; 2,1,2; 0,1,2], by decide⟩
theorem coreWitness_local : inner coreWitness ∈ localSubgroup c := by
  apply inner_mem_local_of_matrix
  apply Subtype.ext
  decide +kernel
theorem generationWitness_local : inner generationWitness ∈ localSubgroup c := by
  apply inner_mem_local_of_matrix
  apply Subtype.ext
  decide +kernel

def coreCommutator : SL := actorElement 2 * coreWitness * (actorElement 2)⁻¹ * coreWitness⁻¹
theorem coreCommutator_cube : coreCommutator ^ 3 = 1 := by
  apply Subtype.ext
  decide +kernel
theorem coreCommutator_eighth_ne : coreCommutator ^ 8 ≠ 1 := by
  intro h
  have hn : (coreCommutator ^ 8).val ≠ (1 : SL).val := by decide +kernel
  exact hn (congrArg Subtype.val h)

theorem actor_escape : ¬ (actor.map inner).subgroupOf (localSubgroup c) ≤
    pCore 2 (localSubgroup c) := by
  intro h
  let b : localSubgroup c := ⟨inner (actorElement 2),
    actor_local (mem_map_of_mem _ (show actorElement 2 ∈ actor from ⟨2,rfl⟩))⟩
  let k : localSubgroup c := ⟨inner coreWitness, coreWitness_local⟩
  have hb : b ∈ pCore 2 (localSubgroup c) :=
    h (mem_map_of_mem _ (show actorElement 2 ∈ actor from ⟨2,rfl⟩))
  have hcomm : b * k * b⁻¹ * k⁻¹ ∈ pCore 2 (localSubgroup c) := by
    have hc := (pCore_normal (p := 2) (G := localSubgroup c)).conj_mem
      b⁻¹ ((pCore 2 (localSubgroup c)).inv_mem hb) k
    simpa only [mul_assoc] using (pCore 2 (localSubgroup c)).mul_mem hb hc
  have hp := pow_card_eq_one' (x := (⟨b * k * b⁻¹ * k⁻¹,hcomm⟩ : pCore 2 (localSubgroup c)))
  rw [localSubgroup_twoCore_card] at hp
  have hp' := congrArg (fun x : pCore 2 (localSubgroup c) => x.val.val) hp
  change (inner (actorElement 2) * inner coreWitness *
    (inner (actorElement 2))⁻¹ * (inner coreWitness)⁻¹) ^ 8 = 1 at hp'
  have he : inner (coreCommutator ^ 8) = inner 1 := by
    simpa only [coreCommutator, map_pow, map_mul, map_inv, map_one] using hp'
  exact coreCommutator_eighth_ne (inner_injective he)

def generators : Fin 6 → SL :=
  ![OuterActors.twoElement 1, actorElement 2, generationWitness,
    (OuterActors.twoElement 1)⁻¹, (actorElement 2)⁻¹, generationWitness⁻¹]
theorem first_word : evalWord generators [2,0,2,0,5,0,5,3,2,3,2] = ambientGenerators 0 := by
  apply Subtype.ext
  decide +kernel
theorem second_word : evalWord generators [2,0,2,0,5,0,5,3,5,0,2,3,5] = ambientGenerators 1 := by
  apply Subtype.ext
  decide +kernel

theorem generation : O ⊔ localSubgroup c = ⊤ := by
  let H := O ⊔ localSubgroup c
  have ha : inner (OuterActors.twoElement 1) ∈ H := by
    apply mem_sup_left
    have h := OuterActors.element_mem_standardSubgroup (1,false)
    simpa [OuterActors.element, OuterActors.pair, inner_eq] using h
  have hb : inner (actorElement 2) ∈ H :=
    mem_sup_left (actor_le (mem_map_of_mem _ (show actorElement 2 ∈ actor from ⟨2,rfl⟩)))
  have hk : inner generationWitness ∈ H := mem_sup_right generationWitness_local
  have hall : ∀ i, generators i ∈ H.comap inner := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hk
    · change inner ((OuterActors.twoElement 1)⁻¹) ∈ H
      rw [map_inv]
      exact H.inv_mem ha
    · change inner ((actorElement 2)⁻¹) ∈ H
      rw [map_inv]
      exact H.inv_mem hb
    · change inner (generationWitness⁻¹) ∈ H
      rw [map_inv]
      exact H.inv_mem hk
  have h0 : ambientGenerators 0 ∈ H.comap inner :=
    first_word ▸ SubgroupEnumeration.evalWord_mem generators (H.comap inner) hall _
  have h1 : ambientGenerators 1 ∈ H.comap inner :=
    second_word ▸ SubgroupEnumeration.evalWord_mem generators (H.comap inner) hall _
  have htop : H.comap inner = ⊤ := by
    apply eq_top_of_ambientGenerators_mem
    intro i
    fin_cases i
    · exact h0
    · exact h1
    · have hi := ambientGenerators_inverse 0
      change ambientGenerators 2 = _ at hi
      change ambientGenerators 2 ∈ H.comap inner
      rw [hi]
      exact (H.comap inner).inv_mem h0
    · have hi := ambientGenerators_inverse 1
      change ambientGenerators 3 = _ at hi
      change ambientGenerators 3 ∈ H.comap inner
      rw [hi]
      exact (H.comap inner).inv_mem h1
  have hg : graphElement ∈ H := by
    apply mem_sup_left
    have ht : OuterActors.twoElement 0 = 1 := Subtype.ext (by decide +kernel)
    have hh := OuterActors.element_mem_standardSubgroup (0,true)
    simpa only [OuterActors.element, OuterActors.pair, ↓reduceIte,
      ht, map_one, one_mul] using hh
  apply top_unique
  intro x _
  obtain ⟨s, rfl | rfl⟩ := inner_or_inner_graph x
  · exact show s ∈ H.comap inner from htop ▸ mem_top s
  · exact H.mul_mem (show s ∈ H.comap inner from htop ▸ mem_top s) hg

end Reference

/-- A concrete inner four-group with every placement obligation in the literal
PSL₃(3) graph extension. No finite-certificate premises remain. -/
public theorem exists_inner_reference : ∃ (R : Sylow 2 G) (D : Subgroup SL) (c : G),
    IsElementaryAbelian 2 D ∧ Nat.card D = 4 ∧
    D.map inner ≤ (R : Subgroup G) ∧
    D.map inner ≤ localSubgroup c ∧
    (R : Subgroup G) ⊓ centralizer (D.map inner : Set G) ≤ localSubgroup c ∧
    Nat.card ((R : Subgroup G).subgroupOf (localSubgroup c)) = 16 ∧
    ¬ (D.map inner).subgroupOf (localSubgroup c) ≤ pCore 2 (localSubgroup c) ∧
    (R : Subgroup G) ⊔ localSubgroup c = ⊤ := by
  refine ⟨OuterActors.standardSylow, Reference.actor, Reference.c,
    Reference.actor_elementary, Reference.actor_card, ?_⟩
  rw [OuterActors.standardSylow_coe]
  exact ⟨Reference.actor_le, Reference.actor_local, Reference.centralizer_local,
    Reference.intersection_card, Reference.actor_escape, Reference.generation⟩

end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphThree.ConcreteGeometry.InnerActors
