module

public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupAction.Defs
public import Mathlib.Algebra.Group.Subgroup.Pointwise

/-!
# Odd images of cyclic action commutators

Every homomorphism from a finite group to an odd-order group kills its
two-core. Restricting such a homomorphism to an action commutator therefore
bounds the commutator modulo its two-core from below by any computed image
of the generator displacements. The actor need not be an involution.

The proof factors the restricted homomorphism through the two-core quotient.
Setwise preservation by the generator implies preservation by its full cyclic
group, so all the commutators lie in the specified subgroup.

Application: the Borel commutator estimate in Aschbacher–Smith, proof of
13.8.20, printed p.954. No matrix-group or automorphism-classification input
is built into this general transfer.
-/

public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupAction.OddCommutatorImage
variable {G T : Type*} [Group G] [Finite G] [Group T] [Finite T]

omit [Finite G] in
theorem twoCore_le_ker (f : G →* T) (hodd : Odd (Nat.card T)) :
    pCore 2 G ≤ f.ker := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 ((pCore 2 G).map f) := pCore_isPGroup.map f
  have hdis : Disjoint ((pCore 2 G).map f) (⊤ : Subgroup T) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨k,hk⟩ := hp.exists_card_eq
    rw [hk,card_top]
    exact hodd.coprime_two_left.pow_left k
  exact (Subgroup.map_eq_bot_iff _).mp (disjoint_top.mp hdis)

theorem card_range_le_quotient_twoCore (f : G →* T) (hodd : Odd (Nat.card T)) :
    Nat.card f.range ≤ Nat.card (G ⧸ pCore 2 G) := by
  have hk : pCore 2 G ≤ f.rangeRestrict.ker := by
    simpa only [MonoidHom.ker_rangeRestrict] using twoCore_le_ker f hodd
  let q := QuotientGroup.lift (pCore 2 G) f.rangeRestrict hk
  apply Nat.card_le_card_of_surjective q
  intro y
  obtain ⟨x,hx⟩ := f.rangeRestrict_surjective y
  exact ⟨QuotientGroup.mk x,hx⟩

omit [Group T] [Finite T] in
/-- An odd subgroup injects into any containing subgroup modulo its two-core. -/
theorem odd_subgroup_card_le_quotient_twoCore (D C : Subgroup G)
    (hDC : D ≤ C) (hodd : Odd (Nat.card D)) :
    Nat.card D ≤ Nat.card (C ⧸ pCore 2 C) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdis : Disjoint (D.subgroupOf C) (pCore 2 C) := by
    apply disjoint_of_coprime_natCard
    rw [Nat.card_congr (subgroupOfEquivOfLe hDC).toEquiv]
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := C)).exists_card_eq
    rw [hk]
    exact hodd.coprime_two_right.pow_right k
  let f := (QuotientGroup.mk' (pCore 2 C)).comp (inclusion hDC)
  have hinj : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hxC : inclusion hDC x ∈ pCore 2 C := (QuotientGroup.eq_one_iff _).mp hx
    have he := disjoint_def.mp hdis
      (show inclusion hDC x ∈ D.subgroupOf C from x.property) hxC
    exact (show x = (1 : D) from Subtype.ext (congrArg (fun c : C => c.val) he))
  exact Nat.card_le_card_of_injective f hinj

omit [Finite G] [Group T] [Finite T] in
theorem cyclic_commutator_le (B : Subgroup G) (α : MulAut G)
    (hB : B.map α.toMonoidHom = B) :
    commutatorSubgroup (zpowers α) G B ≤ B := by
  rw [commutatorSubgroup, Subgroup.closure_le]
  rintro x ⟨β,b,hb,rfl⟩
  have hα : α ∈ MulAction.stabilizer (MulAut G) B := hB
  have hβ : β.val ∈ MulAction.stabilizer (MulAut G) B :=
    (zpowers_le.mpr hα) β.property
  have hmap : B.map β.val.toMonoidHom = B := hβ
  exact B.mul_mem (B.inv_mem hb) (hmap.le (mem_map_of_mem _ hb))

omit [Finite G] [Group T] [Finite T] in
theorem generator_displacement_mem (B : Subgroup G) (α : MulAut G) (b : B) :
    (b : G)⁻¹ * α b ∈ commutatorSubgroup (zpowers α) G B :=
  subset_closure ⟨⟨α,mem_zpowers α⟩,b,b.property,rfl⟩

/-- A computed odd image of the generator displacements bounds the full cyclic
commutator modulo its two-core, even when the actor has order greater than two. -/
theorem card_le_cyclic_commutator_quotient
    (B : Subgroup G) (α : MulAut G) (hB : B.map α.toMonoidHom = B)
    (f : B →* T) (hodd : Odd (Nat.card T))
    {U : Type*} [Group U] (δ : U →* T)
    (hδ : ∀ u : U, ∃ b : B,
      δ u = f ⟨(b : G)⁻¹ * α b,
        cyclic_commutator_le B α hB (generator_displacement_mem B α b)⟩) :
    Nat.card δ.range ≤ Nat.card
      (commutatorSubgroup (zpowers α) G B ⧸
        pCore 2 (commutatorSubgroup (zpowers α) G B)) := by
  let C := commutatorSubgroup (zpowers α) G B
  let g : C →* T := f.comp (inclusion (cyclic_commutator_le B α hB))
  have hle : δ.range ≤ g.range := by
    rintro _ ⟨u,rfl⟩
    obtain ⟨b,hb⟩ := hδ u
    exact ⟨⟨(b : G)⁻¹ * α b,generator_displacement_mem B α b⟩,hb.symm⟩
  exact (Subgroup.card_le_of_le hle).trans (card_range_le_quotient_twoCore g hodd)
end Theory.GroupAction.OddCommutatorImage
