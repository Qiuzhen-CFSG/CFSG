module

public import Theory.Mathieu.M12.SmallParabolicPair.Actions
public import Theory.Mathieu.M12.Properties.Transitivity

/-!
# The action of the first M₁₂ parabolic on the fixed points of its involution

Restriction to the four fixed points and then to their three matchings gives
an epimorphism onto S₃. Sharp five-transitivity bounds the centralizer by 192.
The restriction construction and explicit epimorphism witnesses are adapted
from `Stellmacher.SectionNine.NineFiveM12LocalActions`.
Source: Aschbacher–Smith, Lemma 14.2.21.
-/

@[expose] public section
noncomputable section
open scoped Pointwise
namespace Sporadic.Mathieu.M12SmallPair.FirstCore
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def restrictAction {G X I : Type*} [Group G]
    (representation : G →* Equiv.Perm X) (label : I → X)
    (injective : Function.Injective label)
    (stable : ∀ actor index, ∃ target, representation actor (label index) = label target) :
    G →* Equiv.Perm I := by
  let act : G → I → I := fun actor index => Classical.choose (stable actor index)
  have spec (actor : G) (index : I) :
      representation actor (label index) = label (act actor index) :=
    Classical.choose_spec (stable actor index)
  have one_act (index : I) : act 1 index = index := by
    apply injective
    rw [← spec, map_one]
    rfl
  have mul_act (actor other : G) (index : I) :
      act (actor * other) index = act actor (act other index) := by
    apply injective
    rw [← spec, ← spec, ← spec, map_mul]
    rfl
  exact {
    toFun := fun actor => {
      toFun := act actor
      invFun := act actor⁻¹
      left_inv := fun index => by rw [← mul_act, inv_mul_cancel, one_act]
      right_inv := fun index => by rw [← mul_act, mul_inv_cancel, one_act] }
    map_one' := Equiv.ext one_act
    map_mul' := fun actor other => Equiv.ext (mul_act actor other) }

theorem restrictAction_spec {G X I : Type*} [Group G]
    (representation : G →* Equiv.Perm X) (label : I → X)
    (injective : Function.Injective label)
    (stable : ∀ actor index, ∃ target, representation actor (label index) = label target)
    (actor : G) (index : I) :
    representation actor (label index) =
      label (restrictAction representation label injective stable actor index) :=
  Classical.choose_spec (stable actor index)

def conjugationPermHom {G : Type*} [Group G] : G →* Equiv.Perm G where
  toFun actor := (MulAut.conj actor).toEquiv
  map_one' := by ext; simp
  map_mul' actor other := by ext; simp [mul_assoc]

def fixedLabel : Fin 4 → Fin 12 := ![2, 7, 9, 0]

theorem fixedLabel_injective : Function.Injective fixedLabel := by decide +kernel

theorem fixed_iff (point : Fin 12) :
    zPerm point = point ↔ ∃ index, point = fixedLabel index := by
  revert point
  decide +kernel

def secondRepresentation : firstParabolic →* Equiv.Perm (Fin 12) :=
  M12.subtype.comp firstParabolic.subtype

theorem second_stable (actor : firstParabolic) (index : Fin 4) :
    ∃ target, secondRepresentation actor (fixedLabel index) = fixedLabel target := by
  apply (fixed_iff _).mp
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp actor.property
  have heq := congrArg (fun element : M12 => (element : Equiv.Perm (Fin 12)) (fixedLabel index)) hcomm.symm
  have hfixed : zPerm (fixedLabel index) = fixedLabel index :=
    (fixed_iff _).mpr ⟨index, rfl⟩
  change zPerm (((actor : M12) : Equiv.Perm (Fin 12)) (fixedLabel index)) =
    ((actor : M12) : Equiv.Perm (Fin 12)) (zPerm (fixedLabel index)) at heq
  simpa only [hfixed, secondRepresentation, MonoidHom.comp_apply,
    Subgroup.coe_subtype] using heq

def fixedPointAction : firstParabolic →* Equiv.Perm (Fin 4) :=
  restrictAction secondRepresentation fixedLabel fixedLabel_injective second_stable

def matchingLabel : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

theorem matchingLabel_injective : Function.Injective matchingLabel := by decide +kernel

theorem matching_stable (actor : Equiv.Perm (Fin 4)) (index : Fin 3) :
    ∃ target, conjugationPermHom actor (matchingLabel index) = matchingLabel target := by
  revert actor index
  decide +kernel

def matchingAction : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 3) :=
  restrictAction conjugationPermHom matchingLabel matchingLabel_injective matching_stable

def matchingQuotient : firstParabolic →* Equiv.Perm (Fin 3) :=
  matchingAction.comp fixedPointAction

def secondCyclePerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 6, 11] * List.formPerm [5, 8, 10] * List.formPerm [7, 0, 9]

def secondSwapPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [2, 9, 7, 0] * List.formPerm [3, 6, 4, 8]

private def wordPerm : List Bool → Equiv.Perm (Fin 12)
  | [] => 1
  | b :: bs => (if b then m12GeneratorB else m12GeneratorA) * wordPerm bs

private theorem wordPerm_mem (bs : List Bool) : wordPerm bs ∈ M12 := by
  induction bs with
  | nil => exact M12.one_mem
  | cons b bs ih =>
    exact M12.mul_mem (by cases b <;> first | exact m12GeneratorA_mem | exact m12GeneratorB_mem) ih

theorem secondCyclePerm_mem : secondCyclePerm ∈ M12 := by
  have h : secondCyclePerm = wordPerm [true, false, true, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false, true, true, false, true, true, false, true, false, true, false, true, true, false] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

def secondCycle : M12 := ⟨secondCyclePerm, secondCyclePerm_mem⟩

theorem secondSwapPerm_mem : secondSwapPerm ∈ M12 := by
  have h : secondSwapPerm = wordPerm [true, false, true, true, false, true, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, true, false, true, false, true, false, true, false, true, true, false, true, false, true, false] := by decide +kernel
  rw [h]
  exact wordPerm_mem _

def secondSwap : M12 := ⟨secondSwapPerm, secondSwapPerm_mem⟩

theorem secondCycle_mem : secondCycle ∈ firstParabolic := by
  rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  decide +kernel

theorem secondSwap_mem : secondSwap ∈ firstParabolic := by
  rw [firstParabolic, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  decide +kernel

theorem surjective_of_two_images {G : Type*} [Group G]
    (action : G →* Equiv.Perm (Fin 3)) (cycle swap : G)
    (cycleImage swapImage : Equiv.Perm (Fin 3))
    (hcycle : action cycle = cycleImage) (hswap : action swap = swapImage)
    (hcover : ∀ target : Equiv.Perm (Fin 3),
      target = 1 ∨ target = cycleImage ∨ target = cycleImage ^ 2 ∨
      target = swapImage ∨ target = cycleImage * swapImage ∨
      target = cycleImage ^ 2 * swapImage) :
    Function.Surjective action := by
  intro target
  rcases hcover target with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, map_one action⟩
  · exact ⟨cycle, hcycle⟩
  · exact ⟨cycle ^ 2, by simp [hcycle]⟩
  · exact ⟨swap, hswap⟩
  · exact ⟨cycle * swap, by simp [hcycle, hswap]⟩
  · exact ⟨cycle ^ 2 * swap, by simp [hcycle, hswap]⟩

theorem second_four_action_eq (actor : firstParabolic) (image : Equiv.Perm (Fin 4))
    (himage : ∀ index, secondRepresentation actor (fixedLabel index) =
      fixedLabel (image index)) : fixedPointAction actor = image := by
  apply Equiv.ext
  intro index
  apply fixedLabel_injective
  exact (restrictAction_spec secondRepresentation fixedLabel fixedLabel_injective
    second_stable actor index).symm.trans (himage index)

theorem matching_action_eq (actor : Equiv.Perm (Fin 4)) (image : Equiv.Perm (Fin 3))
    (himage : ∀ index, actor * matchingLabel index * actor⁻¹ =
      matchingLabel (image index)) : matchingAction actor = image := by
  apply Equiv.ext
  intro index
  apply matchingLabel_injective
  exact (restrictAction_spec conjugationPermHom matchingLabel matchingLabel_injective
    matching_stable actor index).symm.trans (himage index)

theorem matchingQuotient_surjective : Function.Surjective matchingQuotient := by
  apply surjective_of_two_images matchingQuotient
    ⟨secondCycle, secondCycle_mem⟩ ⟨secondSwap, secondSwap_mem⟩
    (List.formPerm [0, 2, 1]) (Equiv.swap 1 2)
  · change matchingAction (fixedPointAction ⟨secondCycle, secondCycle_mem⟩) = _
    have hfour : fixedPointAction ⟨secondCycle, secondCycle_mem⟩ =
        List.formPerm [1, 3, 2] := by
      apply second_four_action_eq
      decide +kernel
    rw [hfour]
    apply matching_action_eq
    decide +kernel
  · change matchingAction (fixedPointAction ⟨secondSwap, secondSwap_mem⟩) = _
    have hfour : fixedPointAction ⟨secondSwap, secondSwap_mem⟩ =
        List.formPerm [0, 2, 1, 3] := by
      apply second_four_action_eq
      decide +kernel
    rw [hfour]
    apply matching_action_eq
    decide +kernel
  · decide +kernel


end Sporadic.Mathieu.M12SmallPair.FirstCore
