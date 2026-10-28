module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairStabilizer
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePairCentralizerOrder
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuUniqueness
public import Theory.SpecificGroups.Janko4.Model.InvolutionCentralizers.Second.FiveDisplacement

/-!
# Full ambient centralizer of the native pure pair

The independent first-centralizer census gives order 196608 for the centralizer
of the literal kernel pair 818/1449. Five native star words supply 96 distinct
Mathieu permutations fixing both masks. Their lifts, together with the complete
elementary kernel of order 2048, attain that ambient order inside max1. Hence
the ambient centralizer is exactly the image of its literal max1 centralizer.
Every elementary overgroup and its full centralizer therefore lie in max1;
kernel uniqueness then controls the whole normalizer in the trivial-image case.
The quotient comparison uses the original Mathieu projection and the literal
restriction of its binary kernel; its equation on representatives is explicit.

This uses the native row-seven conjugacy theorem, independently of a printed
MOG coordinate marking. It does not identify a printed sextet or use the
printed AAA(2) centralizer shape. Source motivation: Kleidman--Wilson (1988),
Section 2.1, pp.488--489; the counting argument is proved from the native census.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
open Cardinality QuotientCount.Image KernelCount LocalInvolutionCensus
open Simplicity.Max1Fusion.KernelOrbits LinearFive InvolutionCentralizers.Second
open M22Images.KernelAction InvolutionCentralizers.Second.FiveAction
attribute [local irreducible] modelGroup matrixA matrixB max1Subgroup localKernel basis
set_option backward.isDefEq.respectTransparency true

private def pairCentralizerMap (i : Fin 11) :
    centralizer ({representative i} : Set H) → centralizer (firstFourGroup i : Set Model) :=
  fun x => ⟨eH x.val, by
    rw [firstFourGroup, centralizer_closure]
    rintro y (rfl | rfl)
    · exact (eH_commute_z x.val).eq.symm
    · have hx := mem_centralizer_singleton_iff.mp x.property
      simpa only [map_mul] using (congrArg eH hx).symm⟩

private theorem pairCentralizerMap_bijective (i : Fin 11) :
    Function.Bijective (pairCentralizerMap i) := by
  constructor
  · intro x y he
    exact Subtype.ext (eH_injective (congrArg Subtype.val he))
  · intro x
    have ha : a ∈ firstFourGroup i := subset_closure (by simp)
    have hr : eH (representative i) ∈ firstFourGroup i := subset_closure (by simp)
    let v : InvolutionCentralizers.First.centralizer :=
      ⟨x, mem_centralizer_singleton_iff.mpr (x.property a ha).symm⟩
    obtain ⟨u, hu⟩ := Cardinality.Thompson.max2EquivCentralizer.surjective v
    have heu : eH u = (x : Model) := by
      simpa only [Cardinality.Thompson.max2EquivCentralizer_coe] using congrArg Subtype.val hu
    have hc : u ∈ centralizer ({representative i} : Set H) := by
      apply mem_centralizer_singleton_iff.mpr
      apply eH_injective
      simpa only [map_mul, heu] using (x.property (eH (representative i)) hr).symm
    exact ⟨⟨u,hc⟩, Subtype.ext heu⟩

/-- Exact full ambient order, using the local census and its literal first-centralizer equivalence. -/
theorem centralizer_card : Nat.card (centralizer (nativePair : Set Model)) = 196608 := by
  have hc : Nat.card (centralizer ({representative 7} : Set H)) = 196608 := by
    have h := ConjClasses.nat_card_carrier_mul_card_centralizer (representative 7)
    change Nat.card (localClass (representative 7)) * _ = _ at h
    rw [localClass_seven_card,Cardinality.Thompson.max2_card] at h
    omega
  have hrow : Nat.card (centralizer (firstFourGroup 7 : Set Model)) = 196608 := by
    rw [← Nat.card_congr (Equiv.ofBijective _ (pairCentralizerMap_bijective 7)),hc]
  obtain ⟨g,_,he,_⟩ := row_seven_geometry
  rw [he,card_map_of_injective (MulAut.conj g).injective,hrow]

/-- The pointwise centralizer in the original Mathieu local, with its original quotient map. -/
@[expose] def localPairCentralizer : Subgroup M :=
  centralizer ({kernelValue 818,kernelValue 1449} : Set M)

private theorem fixed_lift (x : M) (i : Fin 5) (hx : starHom x = Stabilizer.generator i) :
    x ∈ localPairCentralizer := by
  have hf (m : ℕ) (hm : SylowCore.starMask (Stabilizer.generator i) m = m) :
      x * kernelValue m * x⁻¹ = kernelValue m := by
    rw [kernel_conjugation]
    change kernelValue (SylowCore.starMask (starHom x) m) = _
    rw [hx,hm]
  rintro y (rfl | rfl)
  · exact (mul_inv_eq_iff_eq_mul.mp (hf 818 (Stabilizer.generator_fixed i).1)).symm
  · exact (mul_inv_eq_iff_eq_mul.mp (hf 1449 (Stabilizer.generator_fixed i).2)).symm

private theorem generator_mem_image (i : Fin 5) :
    Stabilizer.generator i ∈ localPairCentralizer.map starHom := by
  obtain ⟨x,hx⟩ := starHom_surjective (Stabilizer.generator i)
  exact ⟨x,fixed_lift x i hx,hx⟩

private theorem local_image_lower : 96 ≤ Nat.card (localPairCentralizer.map starHom) := by
  let f : Fin 96 → localPairCentralizer.map starHom := fun i =>
    ⟨Stabilizer.element i, Stabilizer.element_mem _ generator_mem_image i⟩
  have hf : Function.Injective f := fun _ _ h =>
    Stabilizer.element_injective (congrArg Subtype.val h)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

private theorem kernel_le_local : starHom.ker ≤ localPairCentralizer := by
  rw [starHom_ker]
  let : IsElementaryAbelian 2 max1Kernel := localKernel_elementary _ _
  intro x hx
  rintro y (rfl | rfl)
  · exact congrArg (fun t : max1Kernel => (t : M))
      (mul_comm (maskValue matrixA_mul_self matrixB_pow_four 818) ⟨x,hx⟩)
  · exact congrArg (fun t : max1Kernel => (t : M))
      (mul_comm (maskValue matrixA_mul_self matrixB_pow_four 1449) ⟨x,hx⟩)

private theorem local_card_eq : Nat.card localPairCentralizer =
    Nat.card (localPairCentralizer.map starHom) * 2048 := by
  have he := Subgroup.comap_map_eq_self (f := starHom) kernel_le_local
  have hc := (localPairCentralizer.map starHom).index_comap_of_surjective starHom_surjective
  rw [he] at hc
  have hk := starHom.ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top_of_surjective starHom starHom_surjective,card_top,
    starHom_ker] at hk
  have hkcard : Nat.card max1Kernel = 2048 := localKernel_card _ _
  rw [hkcard] at hk
  have hlocal := localPairCentralizer.card_mul_index
  have himage := (localPairCentralizer.map starHom).card_mul_index
  rw [← hc] at himage
  apply Nat.eq_of_mul_eq_mul_right
      (Nat.pos_of_ne_zero localPairCentralizer.index_ne_zero_of_finite)
  calc
    Nat.card localPairCentralizer * localPairCentralizer.index = Nat.card M := hlocal
    _ = 2048 * Nat.card StarGroup := hk.symm
    _ = (Nat.card (localPairCentralizer.map starHom) * 2048) *
        localPairCentralizer.index := by rw [← himage]; ring

private theorem localPairCentralizer_lower : 196608 ≤ Nat.card localPairCentralizer := by
  rw [local_card_eq]
  have hlo := local_image_lower
  omega

/-- The whole ambient centralizer is the image of its literal max1 centralizer. -/
theorem centralizer_eq_local_map :
    centralizer (nativePair : Set Model) = localPairCentralizer.map M.subtype := by
  have hle : localPairCentralizer.map M.subtype ≤ centralizer (nativePair : Set Model) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [nativePair,centralizer_closure]
    rintro y (rfl | rfl)
    · exact congrArg (fun t : M => (t : Model)) (hx (kernelValue 818) (by simp))
    · exact congrArg (fun t : M => (t : Model)) (hx (kernelValue 1449) (by simp))
  have he : localPairCentralizer.map M.subtype = centralizer (nativePair : Set Model) :=
    eq_of_le_of_card_ge hle (by
      rw [card_map_of_injective M.subtype_injective, centralizer_card]
      exact localPairCentralizer_lower)
  exact he.symm

/-- The entire ambient centralizer lies in the literal max1 subgroup. -/
theorem centralizer_le_max1 : centralizer (nativePair : Set Model) ≤ max1 := by
  rw [centralizer_eq_local_map]
  exact map_subtype_le _

/-- The actual Mathieu image of the full native pair centralizer has order 96. -/
theorem centralizer_image_card : Nat.card (localPairCentralizer.map starHom) = 96 := by
  have hc := centralizer_card
  rw [centralizer_eq_local_map,card_map_of_injective M.subtype_injective,local_card_eq] at hc
  exact Nat.eq_of_mul_eq_mul_right (by decide : 0 < 2048) hc

/-- Restriction of the original Mathieu projection to the native pair centralizer. -/
@[expose] def localPairProjection :
    localPairCentralizer →* localPairCentralizer.map starHom :=
  starHom.subgroupMap localPairCentralizer

theorem localPairProjection_surjective : Function.Surjective localPairProjection :=
  starHom.subgroupMap_surjective localPairCentralizer

theorem localPairProjection_ker :
    localPairProjection.ker = max1Kernel.subgroupOf localPairCentralizer := by
  rw [localPairProjection, Subgroup.ker_subgroupMap, starHom_ker]

/-- The denominator maps to the whole original kernel inside max1. -/
theorem localPairProjection_kernel_map :
    localPairProjection.ker.map localPairCentralizer.subtype = max1Kernel := by
  rw [localPairProjection_ker]
  apply map_subgroupOf_eq_of_le
  rw [← starHom_ker]
  exact kernel_le_local

/-- The quotient by the literal original binary kernel, with no denominator replacement. -/
@[expose] def localPairQuotientEquiv :
    (localPairCentralizer ⧸ max1Kernel.subgroupOf localPairCentralizer) ≃*
      localPairCentralizer.map starHom :=
  (QuotientGroup.quotientMulEquivOfEq localPairProjection_ker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ localPairProjection_surjective)

theorem localPairQuotientEquiv_apply (x : localPairCentralizer) :
    localPairQuotientEquiv
      (QuotientGroup.mk' (max1Kernel.subgroupOf localPairCentralizer) x) =
        localPairProjection x := by
  rfl

theorem localPairQuotientEquiv_coe (x : localPairCentralizer) :
    (localPairQuotientEquiv
      (QuotientGroup.mk' (max1Kernel.subgroupOf localPairCentralizer) x) : Cardinality.QuotientCount.Image.StarGroup) =
        starHom x.val := by
  rfl

theorem localPairQuotient_card :
    Nat.card (localPairCentralizer ⧸ max1Kernel.subgroupOf localPairCentralizer) = 96 := by
  rw [Nat.card_congr localPairQuotientEquiv.toEquiv, centralizer_image_card]


/-- Any elementary overgroup of the marked pure pair and its full centralizer lie in max1. -/
theorem elementary_overgroup_placement (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : nativePair ≤ X) : X ≤ max1 ∧ centralizer (X : Set Model) ≤ max1 := by
  have hc := (centralizer_le hX).trans centralizer_le_max1
  exact ⟨X.le_centralizer.trans hc,hc⟩

/-- The literal Mathieu image is trivial exactly when the marked elementary overgroup lies in E. -/
theorem image_eq_bot_iff (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : nativePair ≤ X) :
    (X.subgroupOf M).map starHom = ⊥ ↔ X ≤ embeddedKernel := by
  have hXM : X ≤ M := (elementary_overgroup_placement X hX).1
  rw [Subgroup.map_eq_bot_iff,starHom_ker]
  constructor
  · intro h x hx
    exact ⟨⟨x,hXM hx⟩,h hx,rfl⟩
  · intro h x hx
    obtain ⟨y,hy,he⟩ := h hx
    have he' : y = x := Subtype.ext he
    exact he' ▸ hy

/-- The trivial-image branch of the pure-pair extension has its whole normalizer in max1. -/
theorem trivial_image_normalizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hX : nativePair ≤ X) (himage : (X.subgroupOf M).map starHom = ⊥) :
    normalizer (X : Set Model) ≤ max1 :=
  normalizer_le_mathieu_of_kernel_and_centralizer X ((image_eq_bot_iff X hX).mp himage)
    (elementary_overgroup_placement X hX).2

/-- The literal marked pair itself has its whole normalizer in max1. -/
theorem normalizer_le_max1 : normalizer (nativePair : Set Model) ≤ max1 := by
  have hE : nativePair ≤ embeddedKernel := by
    rw [nativePair,closure_le]
    rintro x (rfl | rfl)
    · exact mem_map_of_mem M.subtype (maskValue matrixA_mul_self matrixB_pow_four 818).property
    · exact mem_map_of_mem M.subtype (maskValue matrixA_mul_self matrixB_pow_four 1449).property
  exact normalizer_le_mathieu_of_kernel_and_centralizer nativePair hE centralizer_le_max1

end Janko4.LocalStructure.ElementaryNormalizerCover.PureTwoA.NativePair
