module
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerQuotient
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order168
public import GorensteinWalter.PSL2PerfectOfCard
public import Theory.GroupTheory.SolvableResidual
public import Theory.Mathieu.M23.QuasithinGeometry.Involutions.CentralizerTransport
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Residual control of the original M₂₃ involution centralizer

The actual involution centralizer acts on its seven fixed points, with the
existing elementary kernel of order 16 and quotient PSL₃(2). Four explicit
commutators span that kernel: their sixteen binary words have distinct images
of point 16. Perfectness of the quotient therefore proves perfectness of the
whole centralizer. Its center lies in the self-centralizing kernel; commutation
with three certified generators leaves precisely the identity and the marked
involution. Fusion transports both facts to every involution centralizer.

An overgroup whose residual lies in this centralizer consequently has that
centralizer as its residual. It normalizes the marked center line, hence fixes
the involution and equals its centralizer. This is the exact intrinsic model
input used by the original central-cover argument in Aschbacher--Smith
15.1.20(3d), printed p.1097. No claim of maximality is made, and no solvability
of this perfect centralizer is used. All finite certificates reduce only the
existing seven explicit permutation generators and sixteen short words.
-/

public section
open Subgroup
open scoped commutatorElement
noncomputable section
namespace Sporadic.Mathieu.M23Geometry.InvolutionCentralizer
private abbrev C := representativeCentralizer
private def pair : Fin 4 → Fin 7 × Fin 7 := ![(1,6),(2,4),(2,6),(3,4)]
private def basis (i : Fin 4) : C :=
  ⁅involutionCentralizerGenerator (pair i).1, involutionCentralizerGenerator (pair i).2⁆
private def basisAction (i : Fin 4) (x : Fin 23) : Fin 23 :=
  involutionCentralizerGeneratorTable (pair i).1
    (involutionCentralizerGeneratorTable (pair i).2
      (involutionCentralizerGeneratorInvTable (pair i).1
        (involutionCentralizerGeneratorInvTable (pair i).2 x)))
private theorem basis_apply (i : Fin 4) (x : Fin 23) :
    (basis i).val.val x = basisAction i x := rfl
private theorem basis_mem_kernel (i : Fin 4) : basis i ∈ kernel := by
  change toHeptad (basis i) ∈ heptadKernel
  apply (mem_heptadKernel_iff_labels _).mpr
  intro j
  change basisAction i (label j) = label j
  revert i j
  decide +kernel
private theorem basis_mem_commutator (i : Fin 4) : basis i ∈ commutator C :=
  commutator_mem_commutator (mem_top _) (mem_top _)
private def words : Fin 16 → List (Fin 4) :=
  ![[],[0],[1],[1,0],[2],[2,0],[2,1],[2,1,0],
    [3],[3,0],[3,1],[3,1,0],[3,2],[3,2,0],[3,2,1],[3,2,1,0]]
private def wordElement : List (Fin 4) → C
  | [] => 1
  | j :: w => basis j * wordElement w
private def wordAction : List (Fin 4) → Fin 23 → Fin 23
  | [] => id
  | j :: w => fun x => basisAction j (wordAction w x)
private theorem wordElement_apply (w : List (Fin 4)) (x : Fin 23) :
    (wordElement w).val.val x = wordAction w x := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    change basisAction j (((wordElement w).val.val) x) = _
    rw [ih]
    rfl
private theorem word_mem (H : Subgroup C) (hb : ∀ j, basis j ∈ H)
    (w : List (Fin 4)) : wordElement w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons j w ih => exact H.mul_mem (hb j) ih
private def kernelWord (i : Fin 16) : kernel :=
  ⟨wordElement (words i), word_mem kernel basis_mem_kernel _⟩
private theorem kernelWord_injective : Function.Injective kernelWord := by
  have h : Function.Injective (fun i : Fin 16 => wordAction (words i) 16) := by
    decide +kernel
  intro i j he
  apply h
  simpa only [kernelWord, wordElement_apply] using
    congrArg (fun g : kernel => g.val.val.val (16 : Fin 23)) he
private theorem kernelWord_surjective : Function.Surjective kernelWord :=
  (kernelWord_injective.bijective_of_nat_card_le (by rw [kernel_card, Nat.card_fin])).2

private theorem kernel_le_commutator : kernel ≤ commutator C := by
  intro x hx
  obtain ⟨i,hi⟩ := kernelWord_surjective ⟨x,hx⟩
  have hv : wordElement (words i) = x := congrArg Subtype.val hi
  rw [← hv]
  exact word_mem (commutator C) basis_mem_commutator _

private def linearIndex : Fin 3 → Fin 7 := ![4,5,6]
private theorem center_word_index (i : Fin 16)
    (h : ∀ j : Fin 3,
      wordAction (words i) (involutionCentralizerGeneratorTable (linearIndex j) 16) =
        involutionCentralizerGeneratorTable (linearIndex j)
          (wordAction (words i) 16)) : i = 0 ∨ i = 6 := by
  revert i
  decide +kernel

/-- The original eight-transposition involution inside its actual centralizer. -/
def markedInvolution : representativeCentralizer :=
  ⟨involutionRepresentative, mem_centralizer_singleton_iff.mpr rfl⟩
private theorem word_six : wordElement (words 6) = markedInvolution := by
  apply Subtype.ext
  apply Subtype.ext
  apply Equiv.ext
  intro x
  change (wordElement (words 6)).val.val x = involutionPerm x
  rw [wordElement_apply]
  revert x
  decide +kernel

private theorem center_elements (x : C) (hx : x ∈ center C) : x = 1 ∨ x = markedInvolution := by
  have hxk : x ∈ kernel := kernel_selfCentralizing (center_le_centralizer (kernel : Set C) hx)
  obtain ⟨i,hi⟩ := kernelWord_surjective ⟨x,hxk⟩
  have hv : wordElement (words i) = x := congrArg Subtype.val hi
  have hc : ∀ j : Fin 3,
      wordAction (words i) (involutionCentralizerGeneratorTable (linearIndex j) 16) =
        involutionCentralizerGeneratorTable (linearIndex j)
          (wordAction (words i) 16) := by
    intro j
    have hh := mem_center_iff.mp hx (involutionCentralizerGenerator (linearIndex j))
    have he := congrArg (fun g : C => g.val.val (16 : Fin 23)) hh
    rw [← hv] at he
    change involutionCentralizerGeneratorTable (linearIndex j) ((wordElement (words i)).val.val 16) =
      (wordElement (words i)).val.val (involutionCentralizerGeneratorTable (linearIndex j) 16) at he
    rw [wordElement_apply, wordElement_apply] at he
    exact he.symm
  rcases center_word_index i hc with rfl | rfl
  · exact Or.inl hv.symm
  · exact Or.inr (hv.symm.trans word_six)

private instance sevenPrime : Fact (Nat.Prime 7) := ⟨by decide⟩
/-- The full actual involution centralizer is perfect. -/
theorem representative_isPerfect : Group.IsPerfect representativeCentralizer := by
  let : Group.IsPerfect (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (ZMod 7)) :=
    GorensteinWalter.psl2_isPerfect_of_card_gt_three (ZMod 7) (by norm_num)
  let e := Atlas.Comparisons.Exceptional.psl2SevenEquivPsl3Two.trans actionEquivPSL.symm
  let : Group.IsPerfect action.range := Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  have hm : (commutator C).map action.rangeRestrict = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ action.rangeRestrict_surjective]
    exact Group.IsPerfect.commutator_eq_top
  have hk : action.rangeRestrict.ker ≤ commutator C := by
    rw [MonoidHom.ker_rangeRestrict]
    exact kernel_le_commutator
  refine ⟨?_⟩
  have hh := congrArg (Subgroup.comap action.rangeRestrict) hm
  rwa [comap_map_eq_self hk, comap_top] at hh

/-- The center is exactly the original involution line. -/
theorem representative_center_eq_marked :
    center representativeCentralizer = zpowers markedInvolution := by
  apply le_antisymm
  · intro x hx
    rcases center_elements x hx with rfl | rfl
    · exact one_mem _
    · exact mem_zpowers _
  · apply zpowers_le.mpr
    apply mem_center_iff.mpr
    intro y
    exact Subtype.ext (mem_centralizer_singleton_iff.mp y.property)

/-- The marked centralizer has center of order two. -/
theorem representative_center_card : Nat.card (center representativeCentralizer) = 2 := by
  rw [representative_center_eq_marked, Nat.card_zpowers]
  exact (Subgroup.orderOf_coe markedInvolution).symm.trans involutionRepresentative_order

/-- Fusion preserves perfectness of every literal involution centralizer. -/
theorem isPerfect_of_involution {t : M23} (ht : orderOf t = 2) :
    Group.IsPerfect (centralizer ({t} : Set M23)) := by
  obtain ⟨e⟩ := centralizer_equiv_representative ht
  let : Group.IsPerfect C := representative_isPerfect
  exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective

/-- Fusion preserves the center order, without choosing a new marking. -/
theorem center_card_of_involution {t : M23} (ht : orderOf t = 2) :
    Nat.card (center (centralizer ({t} : Set M23))) = 2 := by
  obtain ⟨e⟩ := centralizer_equiv_representative ht
  exact (Nat.card_congr (centerCongr e).toEquiv).trans representative_center_card

/-- The ambient center image is the line of the original involution. -/
theorem center_image_eq_zpowers {t : M23} (ht : orderOf t = 2) :
    (center (centralizer ({t} : Set M23))).map
      (centralizer ({t} : Set M23)).subtype = zpowers t := by
  let D := centralizer ({t} : Set M23)
  let z : D := ⟨t, mem_centralizer_singleton_iff.mpr rfl⟩
  have hz : z ∈ center D := mem_center_iff.mpr (fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp y.property))
  have hle : zpowers t ≤ (center D).map D.subtype :=
    zpowers_le.mpr (mem_map_of_mem D.subtype hz)
  apply (eq_of_le_of_card_ge hle ?_).symm
  rw [card_map_of_injective D.subtype_injective, center_card_of_involution ht,
    Nat.card_zpowers, ht]

/-- Preserving the center line forces the normalizer to fix the involution. -/
theorem self_normalizing_of_involution {t : M23} (ht : orderOf t = 2) :
    normalizer (centralizer ({t} : Set M23) : Set M23) = centralizer ({t} : Set M23) := by
  apply le_antisymm
  · exact normalizer_le_centralizer_of_characteristic_involution
      (centralizer ({t} : Set M23)) (center _) t ht (center_image_eq_zpowers ht)
  · exact le_normalizer

/-- The exact residual-control input for the original M₂₃ source row. -/
theorem centralizer_eq_of_residual_le (U : Subgroup M23) (t : M23)
    (ht : orderOf t = 2)
    (hCU : centralizer ({t} : Set M23) ≤ U)
    (hR : (solvableResidual U).map U.subtype ≤ centralizer ({t} : Set M23)) :
    U = centralizer ({t} : Set M23) := by
  let D := centralizer ({t} : Set M23)
  let : Group.IsPerfect D := isPerfect_of_involution ht
  have he : (solvableResidual U).map U.subtype = D :=
    le_antisymm hR (le_map_solvableResidual_of_isPerfect D U hCU)
  have hn : U ≤ normalizer (D : Set M23) := by
    rw [← he]
    have hh := (solvableResidual U).le_normalizer_map U.subtype
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  rw [self_normalizing_of_involution ht] at hn
  exact le_antisymm hn hCU
end Sporadic.Mathieu.M23Geometry.InvolutionCentralizer
