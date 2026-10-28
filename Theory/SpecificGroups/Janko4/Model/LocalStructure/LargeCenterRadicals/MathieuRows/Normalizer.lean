module
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.ElementaryNormalizerCover.MathieuUniqueness
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.Mathieu.HallActors
public import Theory.GroupTheory.PCoreSurjective.OddExtension
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.Reductions

/-!
# Radical preimages in the native Mathieu local

Uniqueness of the elementary kernel of order 2048 puts the whole ambient
normalizer of every subgroup between that kernel and max1 inside max1.
Consequently the full normalizer of a Mathieu preimage is exactly the
preimage of the Mathieu normalizer. The literal restricted quotient map
lifts intrinsic two-cores and identifies their quotients. In particular the
kernel itself is a large-center radical with quotient M24.

This is the Mathieu local strategy of An--O'Brien--Wilson (2003), Section 4,
p.122, and its order-2048 row in Table 1, p.124. Kernel uniqueness is the
native form of Kleidman--Wilson (1988), Lemma 1.1.2(i). This leaf does not
assert that every large-center radical is placed in this local.
-/

@[expose] public noncomputable section
open Subgroup
namespace Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
open ElementaryNormalizerCover MathieuHallActors
attribute [local irreducible] modelGroup matrixA matrixB Cardinality.localKernel Cardinality.max1Subgroup

/-- Every overgroup of the kernel inside max1 has its whole ambient normalizer there. -/
theorem normalizer_le_max1 (P : Subgroup Model) (hEP : embeddedKernel ≤ P)
    (hPM : P ≤ max1) : normalizer (P : Set Model) ≤ max1 := by
  let : IsElementaryAbelian 2 kernel := localKernel_elementary _ _
  let : IsElementaryAbelian 2 embeddedKernel := IsElementaryAbelian.map max1.subtype
  intro g hg
  let E' := embeddedKernel.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 E' := IsElementaryAbelian.map (MulAut.conj g).toMonoidHom
  have hEP' : E' ≤ P := by
    rw [← mem_normalizer_iff_map_conj_eq.mp hg]
    exact map_mono hEP
  have hc : Nat.card E' = 2048 := by
    rw [card_map_of_injective (MulAut.conj g).injective,
      card_map_of_injective max1.subtype_injective, Cardinality.localKernel_card]
  have he := embedded_elementary_unique E' (hEP'.trans hPM) hc.ge
  have hm := mem_normalizer_iff_map_conj_eq.mpr he
  simpa only [embedded_localKernel_normalizer_eq_max1] using hm

/-- The actual ambient preimage through the fixed Mathieu quotient. -/
def preimage (A : Subgroup Sporadic.Mathieu.M24) : Subgroup Model :=
  (A.comap projection).map max1.subtype

theorem preimage_le_max1 (A : Subgroup Sporadic.Mathieu.M24) : preimage A ≤ max1 :=
  map_subtype_le _

theorem kernel_le_preimage (A : Subgroup Sporadic.Mathieu.M24) :
    embeddedKernel ≤ preimage A := by
  apply map_mono
  intro x hx
  change projection x ∈ A
  have he : projection x = 1 := by
    apply MonoidHom.mem_ker.mp
    rwa [projection_ker]
  rw [he]
  exact A.one_mem

theorem mem_preimage_iff (A : Subgroup Sporadic.Mathieu.M24) (x : max1) :
    (x : Model) ∈ preimage A ↔ projection x ∈ A := by
  constructor
  · rintro ⟨y,hy,he⟩
    have h : y = x := Subtype.ext he
    exact h ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

theorem preimage_subgroupOf (A : Subgroup Sporadic.Mathieu.M24) :
    (preimage A).subgroupOf max1 = A.comap projection :=
  comap_map_eq_self_of_injective max1.subtype_injective _

/-- Whole ambient normalizers are literal preimages of Mathieu normalizers. -/
theorem normalizer_preimage (A : Subgroup Sporadic.Mathieu.M24) :
    normalizer (preimage A : Set Model) = preimage (normalizer (A : Set Sporadic.Mathieu.M24)) := by
  have hN := normalizer_le_max1 (preimage A) (kernel_le_preimage A) (preimage_le_max1 A)
  rw [← map_subgroupOf_eq_of_le hN,
    subgroupOf_normalizer_eq (preimage_le_max1 A), preimage_subgroupOf,
    ← comap_normalizer_eq_of_surjective A projection_surjective]
  rfl

/-- The same literal projection, restricted to the ambient preimage. -/
def preimageProjection (A : Subgroup Sporadic.Mathieu.M24) : preimage A →* A :=
  (projection.comp (inclusion (preimage_le_max1 A))).codRestrict A
    (fun x => (mem_preimage_iff A _).mp x.property)

theorem preimageProjection_surjective (A : Subgroup Sporadic.Mathieu.M24) :
    Function.Surjective (preimageProjection A) := by
  intro a
  obtain ⟨x,hx⟩ := projection_surjective a.val
  exact ⟨⟨x, (mem_preimage_iff A x).mpr (hx ▸ a.property)⟩, Subtype.ext hx⟩

private theorem projection_kernel_two : IsPGroup 2 projection.ker := by
  rw [projection_ker, localKernel_eq_twoCore]
  exact pCore_isPGroup

theorem preimageProjection_kernel_two (A : Subgroup Sporadic.Mathieu.M24) :
    IsPGroup 2 (preimageProjection A).ker := by
  have he : (preimageProjection A).ker =
      projection.ker.comap (inclusion (preimage_le_max1 A)) := by
    ext x
    exact Subtype.ext_iff
  rw [he]
  exact projection_kernel_two.comap_of_injective _ (inclusion_injective _)

/-- The full intrinsic cores lift under the literal restricted map. -/
theorem preimageProjection_core (A : Subgroup Sporadic.Mathieu.M24) :
    (pCore 2 A).comap (preimageProjection A) = pCore 2 (preimage A) :=
  (preimageProjection A).comap_pCore_of_ker_isPGroup
    (preimageProjection_surjective A) (preimageProjection_kernel_two A)

/-- The core identity after embedding both sides in the native J4 carrier. -/
theorem preimage_core (A : Subgroup Sporadic.Mathieu.M24) :
    (preimage A).pCoreIn 2 = preimage (A.pCoreIn 2) := by
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    have hf : preimageProjection A y ∈ pCore 2 A := by
      change y ∈ (pCore 2 A).comap (preimageProjection A)
      rwa [preimageProjection_core]
    exact ⟨inclusion (preimage_le_max1 A) y,
      ⟨preimageProjection A y, hf, rfl⟩, rfl⟩
  · rintro ⟨y,⟨a,ha,he⟩,rfl⟩
    have hy : projection y ∈ A := he ▸ a.property
    let z : preimage A := ⟨y,(mem_preimage_iff A y).mpr hy⟩
    refine ⟨z,?_,rfl⟩
    rw [← preimageProjection_core]
    change preimageProjection A z ∈ pCore 2 A
    have hz : preimageProjection A z = a := Subtype.ext he.symm
    rwa [hz]

/-- Removing both intrinsic cores gives the actual Mathieu quotient. -/
noncomputable def preimageQuotientEquiv (A : Subgroup Sporadic.Mathieu.M24) :
    preimage A ⧸ pCore 2 (preimage A) ≃* A ⧸ pCore 2 A :=
  (preimageProjection A).quotientPCoreEquivOfSurjective
    (preimageProjection_surjective A) (preimageProjection_kernel_two A)

theorem preimageQuotientEquiv_mk (A : Subgroup Sporadic.Mathieu.M24) (x : preimage A) :
    preimageQuotientEquiv A (QuotientGroup.mk' (pCore 2 (preimage A)) x) =
      QuotientGroup.mk' (pCore 2 A) (preimageProjection A x) := by
  exact MonoidHom.quotientPCoreEquivOfSurjective_mk _ _ _ x

/-- Transport both full intrinsic cores along a group equivalence. -/
noncomputable def coreQuotientCongr {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    G ⧸ pCore 2 G ≃* H ⧸ pCore 2 H :=
  QuotientGroup.congr _ _ e (pCore_map_iso 2 e)

/-- The normalizer quotient uses the full core on both sides. -/
noncomputable def normalizerQuotientEquiv (A : Subgroup Sporadic.Mathieu.M24) :
    let N := normalizer (preimage A : Set Model)
    let H := normalizer (A : Set Sporadic.Mathieu.M24)
    N ⧸ pCore 2 N ≃* H ⧸ pCore 2 H :=
  (coreQuotientCongr (MulEquiv.subgroupCongr (normalizer_preimage A))).trans
    (preimageQuotientEquiv _)

/-- Radical core equations in M24 lift to the whole native normalizer. -/
theorem normalizer_preimage_core (A : Subgroup Sporadic.Mathieu.M24)
    (hA : (normalizer (A : Set Sporadic.Mathieu.M24)).pCoreIn 2 = A) :
    (normalizer (preimage A : Set Model)).pCoreIn 2 = preimage A := by
  rw [normalizer_preimage, preimage_core, hA]

/-- The preimage is nontrivial even when the Mathieu subgroup is trivial. -/
theorem preimage_ne_bot (A : Subgroup Sporadic.Mathieu.M24) : preimage A ≠ ⊥ := by
  intro he
  exact embedded_localKernel_isPRadical.1 (eq_bot_iff.mpr (he ▸ kernel_le_preimage A))

/-- Radicality of the native preimage, including the trivial Mathieu image. -/
theorem preimage_isPRadical (A : Subgroup Sporadic.Mathieu.M24)
    (hA : (normalizer (A : Set Sporadic.Mathieu.M24)).pCoreIn 2 = A) :
    (preimage A).IsPRadical 2 :=
  ⟨preimage_ne_bot A, normalizer_preimage_core A hA⟩

/-- The order-2048 row has its actual Mathieu quotient. -/
noncomputable def kernelNormalizerQuotientEquiv :
    let N := normalizer (embeddedKernel : Set Model)
    N ⧸ pCore 2 N ≃* Sporadic.Mathieu.M24 :=
  (coreQuotientCongr (MulEquiv.subgroupCongr embedded_localKernel_normalizer_eq_max1)).trans
    ((QuotientGroup.quotientMulEquivOfEq (localKernel_eq_twoCore _ _).symm).trans
      (localQuotientEquivM24 _ _))

/-- The elementary kernel has center of order 2048. -/
theorem kernel_center_card : Nat.card (center embeddedKernel) = 2048 := by
  let : IsElementaryAbelian 2 kernel := localKernel_elementary _ _
  let : IsElementaryAbelian 2 embeddedKernel := IsElementaryAbelian.map max1.subtype
  rw [center_eq_top, card_top, card_map_of_injective max1.subtype_injective,
    Cardinality.localKernel_card]

/-- The trivial Mathieu image lifts to the actual binary kernel. -/
theorem preimage_bot : preimage ⊥ = embeddedKernel := by
  change projection.ker.map max1.subtype = embeddedKernel
  rw [projection_ker]

/-- The restricted map has exactly the literal binary kernel as kernel. -/
theorem preimageProjection_ker (A : Subgroup Sporadic.Mathieu.M24) :
    (preimageProjection A).ker = embeddedKernel.subgroupOf (preimage A) := by
  ext x
  change (preimageProjection A x = 1) ↔ (x : Model) ∈ embeddedKernel
  rw [Subtype.ext_iff]
  exact (preimage_bot ▸ (mem_preimage_iff ⊥ (inclusion (preimage_le_max1 A) x))).symm

/-- Orders in the native preimage retain the full order-2048 kernel. -/
theorem preimage_card (A : Subgroup Sporadic.Mathieu.M24) :
    Nat.card (preimage A) = 2048 * Nat.card A := by
  have hc := (preimageProjection A).ker.card_mul_index
  rw [index_ker, MonoidHom.range_eq_top.mpr (preimageProjection_surjective A),
    card_top, preimageProjection_ker,
    Nat.card_congr (subgroupOfEquivOfLe (kernel_le_preimage A)).toEquiv,
    card_map_of_injective max1.subtype_injective, Cardinality.localKernel_card] at hc
  exact hc.symm

/-- Radical saturation supplies the actual native kernel in the placed radical. -/
theorem kernel_le_radical (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) : embeddedKernel ≤ P := by
  have h := le_of_normalizer_le_normalizer_of_pCore_normalizer_le P (max1.pCoreIn 2)
    hP.isPGroup (isPGroup_pCoreIn 2 max1) hP.2.le
    (hN.trans (max1.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image max1 (pCore 2 max1))))
  simpa only [pCoreIn, ← localKernel_eq_twoCore] using h

/-- The radical is the full preimage of its literal Mathieu image. -/
theorem radical_eq_preimage (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) :
    P = preimage ((P.subgroupOf max1).map projection) := by
  have hPM := P.le_normalizer.trans hN
  have hk : projection.ker ≤ P.subgroupOf max1 := by
    rw [projection_ker]
    intro x hx
    exact kernel_le_radical P hP hN (mem_map_of_mem max1.subtype hx)
  unfold preimage
  rw [comap_map_eq_self hk, map_subgroupOf_eq_of_le hPM]

/-- The image retains its full radical core equation; it may be trivial. -/
theorem radical_image_core (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) :
    (normalizer ((P.subgroupOf max1).map projection : Set Sporadic.Mathieu.M24)).pCoreIn 2 =
      (P.subgroupOf max1).map projection := by
  have hPM := P.le_normalizer.trans hN
  have hr := hP.subgroupOf_of_normalizer_normalizes max1 hPM (hN.trans max1.le_normalizer)
  have hk : projection.ker ≤ P.subgroupOf max1 := by
    rw [projection_ker]
    intro x hx
    exact kernel_le_radical P hP hN (mem_map_of_mem max1.subtype hx)
  exact map_normalizer_core_of_p_kernel _ hr.isPGroup hr.2 projection projection_surjective hk

/-- The actual full-core quotient of any placed radical is the quotient of its Mathieu image. -/
def radicalNormalizerQuotientEquiv (P : Subgroup Model) (hP : P.IsPRadical 2)
    (hN : normalizer (P : Set Model) ≤ max1) :
    let N := normalizer (P : Set Model)
    let H := normalizer ((P.subgroupOf max1).map projection : Set Sporadic.Mathieu.M24)
    N ⧸ pCore 2 N ≃* H ⧸ pCore 2 H :=
  (coreQuotientCongr (MulEquiv.subgroupCongr
    (congrArg (fun Q : Subgroup Model => normalizer (Q : Set Model))
      (radical_eq_preimage P hP hN)))).trans (normalizerQuotientEquiv _)


end Janko4.LocalStructure.LargeCenterRadicals.MathieuRows
