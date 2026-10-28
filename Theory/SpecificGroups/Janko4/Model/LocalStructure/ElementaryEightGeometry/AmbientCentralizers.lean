module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.QuotientCentralizers
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryEightGeometry.Pairing

/-!
# Full native centralizers in the unprimed rows

The seed in the marked pair forces every ambient centralizer element into the
original max1 subgroup. The full quotient-centralizer calculation then leaves
only the selected row image. Removing a representative from the elementary
subgroup leaves exactly the previously computed kernel fixed subgroup.
This identifies the ambient centralizer as the join with that fixed subgroup,
and proves self-centralization of both constructed elementary eights.
The image hypotheses retain the Figure 1 permutation in addition to Figure 2.
Source: Kleidman--Wilson (1988), Propositions 2.3.4(i), 2.3.5, Corollary 2.3.6.
-/

set_option backward.isDefEq.respectTransparency true
@[expose] public noncomputable section
namespace Janko4.LocalStructure.ElementaryEightGeometry
open Subgroup Cardinality KernelCount QuotientCount.Image SylowCore SylowCore.Transport
attribute [local irreducible] modelGroup matrixA matrixB localKernel max1Subgroup localX localY basis
local notation "L" => SylowCore.Local
local notation "E" => localKernel matrixA_mul_self matrixB_pow_four
local notation "π" => starProjection matrixA_mul_self matrixB_pow_four
local notation "e" => maskEquiv matrixA_mul_self matrixB_pow_four

/-- Any subgroup with the same whole quotient row has the same literal kernel
centralizer, independently of the choices of its lifts. -/
theorem selected_kernel_centralizer (A : Subgroup L) (r : Fin 2)
    (hrow : A.map π = pairRowImage (r.castLE (by decide))) :
    ((centralizer (A : Set L)).subgroupOf E).map (E).subtype = centralKernel r := by
  unfold centralKernel
  congr 1
  ext x
  obtain ⟨m,rfl⟩ := (e).surjective x
  change (e m : L) ∈ centralizer (A : Set L) ↔
    (e m : L) ∈ centralizer (liftClosure r : Set L)
  rw [mask_mem_pairRow_centralizer_iff A _ hrow,
    mask_mem_pairRow_centralizer_iff _ _ (liftClosure_projection r)]

theorem selected_kernel_le_centralizer (A : Subgroup L) (r : Fin 2)
    (hrow : A.map π = pairRowImage (r.castLE (by decide))) :
    centralKernel r ≤ centralizer (A : Set L) := by
  rw [← selected_kernel_centralizer A r hrow]
  rintro x ⟨y,hy,rfl⟩
  exact hy

/-- Every centralizer element projects into the actual row, with the original
quotient map, not just into an abstract group of order sixteen. -/
theorem selected_centralizer_projection_le (A : Subgroup L) (r : Fin 2)
    (hrow : A.map π = pairRowImage (r.castLE (by decide))) :
    (centralizer (A : Set L)).map π ≤ pairRowImage (r.castLE (by decide)) := by
  rw [← pairRow_quotient_self_centralizing r]
  rintro p ⟨x,hx,rfl⟩
  intro a ha
  rw [← hrow] at ha
  obtain ⟨y,hy,rfl⟩ := ha
  exact (map_mul π y x).symm.trans ((congrArg π (hx y hy)).trans (map_mul π x y))

/-- Removing a lift from the elementary subgroup leaves precisely the native
kernel fixed subgroup. -/
theorem selected_local_centralizer (A : Subgroup L) [IsElementaryAbelian 2 A]
    (r : Fin 2) (hrow : A.map π = pairRowImage (r.castLE (by decide))) :
    centralizer (A : Set L) = A ⊔ centralKernel r := by
  apply le_antisymm
  · intro g hg
    have hp := selected_centralizer_projection_le A r hrow (mem_map_of_mem π hg)
    rw [← hrow] at hp
    obtain ⟨a,ha,he⟩ := hp
    have hk : g * a⁻¹ ∈ E := by
      rw [← starProjection_ker, MonoidHom.mem_ker, map_mul, map_inv, he, mul_inv_cancel]
    have hc : g * a⁻¹ ∈ centralizer (A : Set L) :=
      (centralizer _).mul_mem hg ((centralizer _).inv_mem (A.le_centralizer ha))
    have hkc : g * a⁻¹ ∈ centralKernel r := by
      rw [← selected_kernel_centralizer A r hrow]
      exact ⟨⟨g * a⁻¹,hk⟩,hc,rfl⟩
    have hm := (A ⊔ centralKernel r).mul_mem
      ((le_sup_right : centralKernel r ≤ A ⊔ centralKernel r) hkc)
      ((le_sup_left : A ≤ A ⊔ centralKernel r) ha)
    simpa only [inv_mul_cancel_right] using hm
  · exact sup_le A.le_centralizer (selected_kernel_le_centralizer A r hrow)

/-- The entire calculated local centralizer has order 256, including every
kernel fibre of the literal quotient map. -/
theorem selected_local_centralizer_card (A : Subgroup L) [IsElementaryAbelian 2 A]
    (r : Fin 2) (hrow : A.map π = pairRowImage (r.castLE (by decide))) :
    Nat.card (centralizer (A : Set L)) = 256 := by
  let C := centralizer (A : Set L)
  have hmap : C.map π = pairRowImage (r.castLE (by decide)) := by
    apply le_antisymm (selected_centralizer_projection_le A r hrow)
    rw [← hrow]
    exact Subgroup.map_mono A.le_centralizer
  have hi : (E).relIndex C = 16 := by
    rw [← starProjection_ker, relIndex_ker, hmap, unprimed_pairRow_card]
  have hk : Nat.card ((E).subgroupOf C) = 16 := by
    calc
      _ = Nat.card (((E).subgroupOf C).map C.subtype) :=
        (card_map_of_injective C.subtype_injective).symm
      _ = Nat.card (C ⊓ E : Subgroup L) := by rw [subgroupOf_map_subtype, inf_comm]
      _ = Nat.card ((C.subgroupOf E).map (E).subtype) := by rw [subgroupOf_map_subtype]
      _ = Nat.card (C.subgroupOf E) := card_map_of_injective (E).subtype_injective
      _ = 16 := pairRow_kernel_centralizer_card A _ hrow
  have hc := ((E).subgroupOf C).card_mul_index
  change Nat.card ((E).subgroupOf C) * (E).relIndex C = Nat.card C at hc
  rw [hk, hi] at hc
  exact hc.symm

/-- Both literal elementary eights are their full centralizers inside max1. -/
theorem localEight_self_centralizing (r : Fin 2) :
    centralizer (localEight r : Set L) = localEight r := by
  rw [selected_local_centralizer _ r (localEight_projection r)]
  exact sup_eq_left.mpr le_sup_right

/-- The kernel seed of the original marked pair is in each constructed eight. -/
theorem seed_mem_nativeEight (r : Fin 2) :
    (InvolutionCentralizers.Second.seed : Model) ∈ nativeEight r := by
  have hm : kernelPairMasks r 0 = 1 := by revert r; decide +kernel
  have hs : nativeMask 1 = InvolutionCentralizers.Second.seed :=
    Simplicity.Max1Fusion.KernelOrbits.maskValue_one matrixA_mul_self matrixB_pow_four
  rw [← hs, ← hm]
  exact mem_map_of_mem (L).subtype (kernelPair_mem_localEight r 0)

/-- The actual seed centralizer localizes the entire ambient centralizer. -/
theorem seed_centralizer_le_local (X : Subgroup Model)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X) :
    centralizer (X : Set Model) ≤ L := by
  apply le_trans (centralizer_le (Set.singleton_subset_iff.mpr hs))
  exact InvolutionCentralizers.Second.ambient_le_max1

/-- The comparison uses the literal max1 inclusion on every centralizer element. -/
theorem seed_ambient_centralizer_map (X : Subgroup Model) (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X) :
    centralizer (X : Set Model) =
      (centralizer (X.subgroupOf L : Set L)).map (L).subtype := by
  apply le_antisymm
  · intro g hg
    refine ⟨⟨g,seed_centralizer_le_local X hs hg⟩,?_,rfl⟩
    intro a ha
    exact Subtype.ext (hg a ha)
  · rintro g ⟨a,ha,rfl⟩ x hx
    exact congrArg (fun z : L => (z : Model)) (ha ⟨x,hXL hx⟩ hx)

/-- Full ambient self-centralization of both native elementary groups of order 256. -/
theorem nativeEight_self_centralizing (r : Fin 2) :
    centralizer (nativeEight r : Set Model) = nativeEight r := by
  rw [seed_ambient_centralizer_map _ (nativeEight_le_local r) (seed_mem_nativeEight r)]
  have he : (nativeEight r).subgroupOf L = localEight r :=
    comap_map_eq_self_of_injective (L).subtype_injective _
  rw [he, localEight_self_centralizing]
  rfl

/-- Native selected-row calculation for an arbitrary elementary subgroup
containing the marked seed. Its full centralizer is its join with the exact
fixed subgroup of the original kernel. -/
theorem selected_ambient_centralizer (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    centralizer (X : Set Model) = X ⊔ (centralKernel r).map (L).subtype := by
  let : IsElementaryAbelian 2 (X.subgroupOf L) := IsElementaryAbelian.subgroupOf hXL
  rw [seed_ambient_centralizer_map X hXL hs, selected_local_centralizer _ r hrow,
    Subgroup.map_sup, map_subgroupOf_eq_of_le hXL]

/-- The selected ambient centralizer has exactly 256 elements. -/
theorem selected_ambient_centralizer_card (X : Subgroup Model) [IsElementaryAbelian 2 X]
    (hXL : X ≤ L) (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    Nat.card (centralizer (X : Set Model)) = 256 := by
  let : IsElementaryAbelian 2 (X.subgroupOf L) := IsElementaryAbelian.subgroupOf hXL
  rw [seed_ambient_centralizer_map X hXL hs, card_map_of_injective (L).subtype_injective]
  exact selected_local_centralizer_card _ r hrow

/-- The selected full ambient centralizer is elementary, with no assumption
about its centralizer or normalizer. -/
theorem selected_ambient_centralizer_elementary (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    IsElementaryAbelian 2 (centralizer (X : Set Model)) := by
  let : IsElementaryAbelian 2 (X.subgroupOf L) := IsElementaryAbelian.subgroupOf hXL
  have h := IsElementaryAbelian.sup_of_le_centralizer (p := 2)
    (selected_kernel_le_centralizer (X.subgroupOf L) r hrow)
  rw [← selected_local_centralizer _ r hrow] at h
  let : IsElementaryAbelian 2 (centralizer (X.subgroupOf L : Set L)) := h
  rw [seed_ambient_centralizer_map X hXL hs]
  exact IsElementaryAbelian.map_subtype

/-- The calculated centralizer is also self-centralizing in the entire model. -/
theorem selected_ambient_centralizer_self_centralizing (X : Subgroup Model)
    [IsElementaryAbelian 2 X] (hXL : X ≤ L)
    (hs : (InvolutionCentralizers.Second.seed : Model) ∈ X)
    (r : Fin 2) (hrow : (X.subgroupOf L).map π = pairRowImage (r.castLE (by decide))) :
    centralizer (centralizer (X : Set Model) : Set Model) = centralizer (X : Set Model) := by
  let : IsElementaryAbelian 2 (centralizer (X : Set Model)) :=
    selected_ambient_centralizer_elementary X hXL hs r hrow
  exact le_antisymm (centralizer_le X.le_centralizer) (centralizer _).le_centralizer

/-- The four actual word lifts, together with the native seed of the
original nonsingular pair. -/
def markedLocalRow (r : Fin 2) : Subgroup L :=
  liftClosure r ⊔ closure ({InvolutionCentralizers.Second.seed} : Set L)

def markedNativeRow (r : Fin 2) : Subgroup Model := (markedLocalRow r).map (L).subtype

theorem markedLocalRow_le_localEight (r : Fin 2) : markedLocalRow r ≤ localEight r := by
  apply sup_le le_sup_left
  apply (closure_le _).mpr
  apply Set.singleton_subset_iff.mpr
  have hs : nativeMask 1 = InvolutionCentralizers.Second.seed :=
    Simplicity.Max1Fusion.KernelOrbits.maskValue_one matrixA_mul_self matrixB_pow_four
  have hm : kernelPairMasks r 0 = 1 := by revert r; decide +kernel
  rw [← hs, ← hm]
  exact kernelPair_mem_localEight r 0

instance markedLocalRow_elementary (r : Fin 2) : IsElementaryAbelian 2 (markedLocalRow r) := by
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro a b
    apply Subtype.ext
    exact setLike_mul_comm (markedLocalRow_le_localEight r a.property)
      (markedLocalRow_le_localEight r b.property)
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro a
    apply Subtype.ext
    exact elemPow_eq_one_of_isElementaryAbelian (p := 2) (a : L)
      (markedLocalRow_le_localEight r a.property)

instance markedNativeRow_elementary (r : Fin 2) : IsElementaryAbelian 2 (markedNativeRow r) :=
  IsElementaryAbelian.map_subtype

theorem markedLocalRow_projection (r : Fin 2) :
    (markedLocalRow r).map π = pairRowImage (r.castLE (by decide)) := by
  apply le_antisymm
  · rw [← localEight_projection r]
    exact Subgroup.map_mono (markedLocalRow_le_localEight r)
  · rw [← liftClosure_projection r]
    exact Subgroup.map_mono le_sup_left

theorem markedLocalRow_centralizer (r : Fin 2) :
    centralizer (markedLocalRow r : Set L) = localEight r := by
  rw [selected_local_centralizer _ r (markedLocalRow_projection r)]
  apply le_antisymm (sup_le (markedLocalRow_le_localEight r) le_sup_right)
  exact sup_le (le_sup_left.trans le_sup_left) le_sup_right

/-- Full ambient centralizer calculations for the two displayed unprimed
native rows, with the original word lifts and seed retained. -/
theorem markedNativeRow_centralizer (r : Fin 2) :
    centralizer (markedNativeRow r : Set Model) = nativeEight r := by
  have hs : (InvolutionCentralizers.Second.seed : Model) ∈ markedNativeRow r := by
    change (InvolutionCentralizers.Second.seed : Model) ∈ (markedLocalRow r).map (L).subtype
    refine ⟨InvolutionCentralizers.Second.seed, ?_, rfl⟩
    exact (show closure ({InvolutionCentralizers.Second.seed} : Set L) ≤ markedLocalRow r
      from le_sup_right) (subset_closure (Set.mem_singleton _))
  rw [seed_ambient_centralizer_map (markedNativeRow r) (map_subtype_le _) hs]
  have he : (markedNativeRow r).subgroupOf L = markedLocalRow r :=
    comap_map_eq_self_of_injective (L).subtype_injective _
  rw [he, markedLocalRow_centralizer]
  rfl

end Janko4.LocalStructure.ElementaryEightGeometry
