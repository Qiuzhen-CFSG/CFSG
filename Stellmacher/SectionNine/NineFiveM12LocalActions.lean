module

public import Stellmacher.SectionNine.NineFiveM12Data

public section

open scoped Pointwise

noncomputable section

namespace Stellmacher.SectionNine.M12Realization

open Sporadic.Mathieu

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private def restrictAction {G X I : Type*} [Group G]
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

private theorem restrictAction_spec {G X I : Type*} [Group G]
    (representation : G →* Equiv.Perm X) (label : I → X)
    (injective : Function.Injective label)
    (stable : ∀ actor index, ∃ target, representation actor (label index) = label target)
    (actor : G) (index : I) :
    representation actor (label index) =
      label (restrictAction representation label injective stable actor index) :=
  Classical.choose_spec (stable actor index)

private def conjugationPermHom {G : Type*} [Group G] : G →* Equiv.Perm G where
  toFun actor := (MulAut.conj actor).toEquiv
  map_one' := by ext; simp
  map_mul' actor other := by ext; simp [mul_assoc]

private def planeLabel : Fin 3 → M12 :=
  ![centerElement, planeElement, centerElement * planeElement]

private theorem planeLabel_injective : Function.Injective planeLabel := by
  decide +kernel

private theorem plane_mem_iff (element : M12) :
    element ∈ centerPlane ↔ element = 1 ∨ ∃ index, element = planeLabel index := by
  have hmem : element ∈ centerPlane ↔ element = 1 ∨ element = centerElement ∨
      element = planeElement ∨ element = centerElement * planeElement := by
    apply Subgroup.mem_closure_pair_iff
    · apply Subtype.ext; decide +kernel
    · apply Subtype.ext; decide +kernel
    · change centerElement * planeElement = planeElement * centerElement
      apply Subtype.ext; decide +kernel
  rw [hmem]
  simp [planeLabel, Fin.exists_fin_succ]

private def firstRepresentation : firstLocal →* Equiv.Perm M12 :=
  conjugationPermHom.comp firstLocal.subtype

private theorem first_stable (actor : firstLocal) (index : Fin 3) :
    ∃ target, firstRepresentation actor (planeLabel index) = planeLabel target := by
  have hmem : planeLabel index ∈ centerPlane :=
    (plane_mem_iff _).mpr (Or.inr ⟨index, rfl⟩)
  have hconj := (Subgroup.mem_set_normalizer_iff.mp actor.property (planeLabel index)).mp hmem
  rcases (plane_mem_iff _).mp hconj with hone | hex
  · have hne : ∀ index, planeLabel index ≠ 1 := by decide +kernel
    exfalso
    apply hne index
    have : (actor : M12)⁻¹ * ((actor : M12) * planeLabel index * (actor : M12)⁻¹) *
        (actor : M12) = 1 := by rw [hone]; group
    simpa [mul_assoc] using this
  · exact hex

def firstThreeAction : firstLocal →* Equiv.Perm (Fin 3) :=
  restrictAction firstRepresentation planeLabel planeLabel_injective first_stable

private def fixedLabel : Fin 4 → Fin 12 := ![2, 7, 9, 0]

private theorem fixedLabel_injective : Function.Injective fixedLabel := by decide +kernel

private theorem fixed_iff (point : Fin 12) :
    centerPerm point = point ↔ ∃ index, point = fixedLabel index := by
  revert point
  decide +kernel

private def secondRepresentation : secondLocal →* Equiv.Perm (Fin 12) :=
  M12.subtype.comp secondLocal.subtype

private theorem second_stable (actor : secondLocal) (index : Fin 4) :
    ∃ target, secondRepresentation actor (fixedLabel index) = fixedLabel target := by
  apply (fixed_iff _).mp
  have hcomm := Subgroup.mem_centralizer_singleton_iff.mp actor.property
  have heq := congrArg (fun element : M12 => (element : Equiv.Perm (Fin 12)) (fixedLabel index)) hcomm.symm
  have hfixed : centerPerm (fixedLabel index) = fixedLabel index :=
    (fixed_iff _).mpr ⟨index, rfl⟩
  change centerPerm (((actor : M12) : Equiv.Perm (Fin 12)) (fixedLabel index)) =
    ((actor : M12) : Equiv.Perm (Fin 12)) (centerPerm (fixedLabel index)) at heq
  simpa only [hfixed, secondRepresentation, MonoidHom.comp_apply,
    Subgroup.coe_subtype] using heq

private def secondFourAction : secondLocal →* Equiv.Perm (Fin 4) :=
  restrictAction secondRepresentation fixedLabel fixedLabel_injective second_stable

private def matchingLabel : Fin 3 → Equiv.Perm (Fin 4) :=
  ![Equiv.swap 0 1 * Equiv.swap 2 3,
    Equiv.swap 0 2 * Equiv.swap 1 3,
    Equiv.swap 0 3 * Equiv.swap 1 2]

private theorem matchingLabel_injective : Function.Injective matchingLabel := by decide +kernel

private theorem matching_stable (actor : Equiv.Perm (Fin 4)) (index : Fin 3) :
    ∃ target, conjugationPermHom actor (matchingLabel index) = matchingLabel target := by
  revert actor index
  decide +kernel

private def matchingAction : Equiv.Perm (Fin 4) →* Equiv.Perm (Fin 3) :=
  restrictAction conjugationPermHom matchingLabel matchingLabel_injective matching_stable

def secondThreeAction : secondLocal →* Equiv.Perm (Fin 3) :=
  matchingAction.comp secondFourAction

private def firstCyclePerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 0, 3] * List.formPerm [2, 4, 5] *
    List.formPerm [6, 9, 10] * List.formPerm [7, 11, 8]

private def firstSwapPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 2, 5, 0] * Equiv.swap 3 11 * Equiv.swap 4 10 *
    List.formPerm [6, 9, 8, 7]

private def secondCyclePerm : Equiv.Perm (Fin 12) :=
  List.formPerm [1, 6, 11] * List.formPerm [5, 8, 10] * List.formPerm [7, 0, 9]

private def secondSwapPerm : Equiv.Perm (Fin 12) :=
  List.formPerm [2, 9, 7, 0] * List.formPerm [3, 6, 4, 8]

private theorem action_mem_of_blocks (permutation : Equiv.Perm (Fin 12))
    (hblocks : permutation • m12Blocks = m12Blocks) : permutation ∈ M12 := by
  apply (mem_M12_iff _).mpr
  exact_mod_cast hblocks

private def firstCycle : M12 :=
  ⟨firstCyclePerm, action_mem_of_blocks _ (by decide +kernel)⟩

private def firstSwap : M12 :=
  ⟨firstSwapPerm, action_mem_of_blocks _ (by decide +kernel)⟩

private def secondCycle : M12 :=
  ⟨secondCyclePerm, action_mem_of_blocks _ (by decide +kernel)⟩

private def secondSwap : M12 :=
  ⟨secondSwapPerm, action_mem_of_blocks _ (by decide +kernel)⟩

private theorem first_mem_of_labels (actor : M12)
    (forward : ∀ index, ∃ target, actor * planeLabel index * actor⁻¹ = planeLabel target)
    (backward : ∀ index, ∃ target, actor⁻¹ * planeLabel index * actor = planeLabel target) :
    actor ∈ firstLocal := by
  rw [firstLocal, Subgroup.mem_set_normalizer_iff]
  intro element
  constructor
  · intro hmem
    rcases (plane_mem_iff _).mp hmem with rfl | ⟨index, rfl⟩
    · simp
    · exact (plane_mem_iff _).mpr (Or.inr (forward index))
  · intro hmem
    have hinv : actor⁻¹ * (actor * element * actor⁻¹) * actor ∈ centerPlane := by
      rcases (plane_mem_iff _).mp hmem with hone | ⟨index, hindex⟩
      · rw [hone]; simp
      · rw [hindex]
        exact (plane_mem_iff _).mpr (Or.inr (backward index))
    simpa [mul_assoc] using hinv

private theorem firstCycle_mem : firstCycle ∈ firstLocal := by
  apply first_mem_of_labels <;> decide +kernel

private theorem firstSwap_mem : firstSwap ∈ firstLocal := by
  apply first_mem_of_labels <;> decide +kernel

private theorem secondCycle_mem : secondCycle ∈ secondLocal := by
  rw [secondLocal, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  decide +kernel

private theorem secondSwap_mem : secondSwap ∈ secondLocal := by
  rw [secondLocal, Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  decide +kernel

private theorem surjective_of_two_images {G : Type*} [Group G]
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

private theorem first_action_eq (actor : firstLocal) (image : Equiv.Perm (Fin 3))
    (himage : ∀ index, (actor : M12) * planeLabel index * (actor : M12)⁻¹ =
      planeLabel (image index)) : firstThreeAction actor = image := by
  apply Equiv.ext
  intro index
  apply planeLabel_injective
  exact (restrictAction_spec firstRepresentation planeLabel planeLabel_injective
    first_stable actor index).symm.trans (himage index)

private theorem second_four_action_eq (actor : secondLocal) (image : Equiv.Perm (Fin 4))
    (himage : ∀ index, secondRepresentation actor (fixedLabel index) =
      fixedLabel (image index)) : secondFourAction actor = image := by
  apply Equiv.ext
  intro index
  apply fixedLabel_injective
  exact (restrictAction_spec secondRepresentation fixedLabel fixedLabel_injective
    second_stable actor index).symm.trans (himage index)

private theorem matching_action_eq (actor : Equiv.Perm (Fin 4)) (image : Equiv.Perm (Fin 3))
    (himage : ∀ index, actor * matchingLabel index * actor⁻¹ =
      matchingLabel (image index)) : matchingAction actor = image := by
  apply Equiv.ext
  intro index
  apply matchingLabel_injective
  exact (restrictAction_spec conjugationPermHom matchingLabel matchingLabel_injective
    matching_stable actor index).symm.trans (himage index)

theorem firstThreeAction_surjective : Function.Surjective firstThreeAction := by
  apply surjective_of_two_images firstThreeAction
    ⟨firstCycle, firstCycle_mem⟩ ⟨firstSwap, firstSwap_mem⟩
    (List.formPerm [0, 1, 2]) (Equiv.swap 0 2)
  · apply first_action_eq
    decide +kernel
  · apply first_action_eq
    decide +kernel
  · decide +kernel

theorem secondThreeAction_surjective : Function.Surjective secondThreeAction := by
  apply surjective_of_two_images secondThreeAction
    ⟨secondCycle, secondCycle_mem⟩ ⟨secondSwap, secondSwap_mem⟩
    (List.formPerm [0, 2, 1]) (Equiv.swap 1 2)
  · change matchingAction (secondFourAction ⟨secondCycle, secondCycle_mem⟩) = _
    have hfour : secondFourAction ⟨secondCycle, secondCycle_mem⟩ =
        List.formPerm [1, 3, 2] := by
      apply second_four_action_eq
      decide +kernel
    rw [hfour]
    apply matching_action_eq
    decide +kernel
  · change matchingAction (secondFourAction ⟨secondSwap, secondSwap_mem⟩) = _
    have hfour : secondFourAction ⟨secondSwap, secondSwap_mem⟩ =
        List.formPerm [0, 2, 1, 3] := by
      apply second_four_action_eq
      decide +kernel
    rw [hfour]
    apply matching_action_eq
    decide +kernel
  · decide +kernel

theorem m12_local_symmetric_three_quotients :
    (∃ action : firstLocal →* Equiv.Perm (Fin 3), Function.Surjective action) ∧
    (∃ action : secondLocal →* Equiv.Perm (Fin 3), Function.Surjective action) :=
  ⟨⟨firstThreeAction, firstThreeAction_surjective⟩,
    ⟨secondThreeAction, secondThreeAction_surjective⟩⟩


end Stellmacher.SectionNine.M12Realization
