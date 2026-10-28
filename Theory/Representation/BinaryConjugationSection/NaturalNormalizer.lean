module
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Natural images of literal section normalizers

For a subgroup containing the coordinate kernel, membership is detected
in its quotient image. Equivariance therefore identifies its relative
normalizer with the preimage of the subspace stabilizer. A surjective
natural action gives the full stabilizer image; its normal two-core maps
into the geometric radical, by the two-block action on the subspace and
its quotient.

Source application: Aschbacher–Smith, The Classification of Quasithin
Groups, 13.8.29 and 13.8.32, printed pp.964–965. All normalizers are relative
to the original actor group, and the coordinate homomorphism is unchanged.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}
  (d : BinaryConjugationSection H U Z ρ)
  (π : H →* BinaryLinear.GL W) (hact : ∀ h w, ρ h w = π h w)

include hact

/-- The full preimage of a subspace stabilizer is the literal relative
normalizer whenever the original subgroup contains the coordinate kernel. -/
theorem natural_normalizer_iff (B : Subgroup G) (hBU : B ≤ U) (hZB : Z ≤ B) (h : H) :
    (h:G) ∈ normalizer (B:Set G) ↔ π h ∈ BinaryLinear.parabolic (d.imageSpace B) := by
  have hm (x : U) :
      (h:G)*(x:G)*(h:G)⁻¹ ∈ B ↔ π h (d.coordinates x).toAdd ∈ d.imageSpace B := by
    let y : U := ⟨(h:G)*(x:G)*(h:G)⁻¹,
      (mem_normalizer_iff.mp (d.normalized h.property) x).mp x.property⟩
    have he := d.coordinates_mem_imageSpace_iff_of_kernel_le B hZB y
    rw [d.equivariant,hact] at he
    exact he.symm
  constructor
  · intro hn w
    obtain ⟨x,hx⟩ := d.onto (Multiplicative.ofAdd w)
    have hx' : (d.coordinates x).toAdd = w := congrArg Multiplicative.toAdd hx
    rw [←hx',←hm,d.coordinates_mem_imageSpace_iff_of_kernel_le B hZB]
    exact (mem_normalizer_iff.mp hn x).symm
  · intro hp
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      exact (hm ⟨x,hBU hx⟩).mpr ((hp _).mpr
        ((d.coordinates_mem_imageSpace_iff_of_kernel_le B hZB _).mpr hx))
    · intro hx
      have hxU : x ∈ U := (mem_normalizer_iff.mp (d.normalized h.property) x).mpr (hBU hx)
      exact (d.coordinates_mem_imageSpace_iff_of_kernel_le B hZB ⟨x,hxU⟩).mp
        ((hp _).mp ((hm ⟨x,hxU⟩).mp hx))

/-- Surjectivity of the original natural action identifies the entire
relative seed-normalizer image, without an extra parabolic marking. -/
theorem natural_normalizer_image (honto : Function.Surjective π)
    (B : Subgroup G) (hBU : B ≤ U) (hZB : Z ≤ B) :
    ((H ⊓ normalizer (B:Set G)).subgroupOf H).map π =
      BinaryLinear.parabolic (d.imageSpace B) := by
  ext a
  constructor
  · rintro ⟨h,hh,rfl⟩
    exact (d.natural_normalizer_iff π hact B hBU hZB h).mp hh.2
  · intro ha
    obtain ⟨h,rfl⟩ := honto a
    exact ⟨h,⟨h.property,(d.natural_normalizer_iff π hact B hBU hZB h).mpr ha⟩,rfl⟩

/-- The actual relative normalizer's two-core acts in the geometric radical. -/
theorem natural_normalizer_core_image [Finite G] [FiniteDimensional (ZMod 2) W]
    (honto : Function.Surjective π) (B : Subgroup G) (hBU : B ≤ U) (hZB : Z ≤ B) :
    (((H ⊓ normalizer (B:Set G)).pCoreIn 2).subgroupOf H).map π ≤
      BinaryLinear.radical (d.imageSpace B) := by
  let R := H ⊓ normalizer (B:Set G)
  let P := BinaryLinear.parabolic (d.imageSpace B)
  let f : R →* P := (π.comp (inclusion (show R ≤ H from inf_le_left))).codRestrict P
    (fun r => (d.natural_normalizer_iff π hact B hBU hZB _).mp r.property.2)
  have hf : Function.Surjective f := by
    intro a
    have ha : a.val ∈ ((H ⊓ normalizer (B:Set G)).subgroupOf H).map π := by
      rw [d.natural_normalizer_image π hact honto B hBU hZB]
      exact a.property
    obtain ⟨h,hh,he⟩ := ha
    exact ⟨⟨h,hh⟩,Subtype.ext he⟩
  have hn : ((pCore 2 R).map f).Normal := Subgroup.Normal.map inferInstance f hf
  have hc : (pCore 2 R).map f ≤ pCore 2 P := le_sSup ⟨hn,pCore_isPGroup.map f⟩
  rintro a ⟨h,hh,rfl⟩
  obtain ⟨r,hr,he⟩ := hh
  have hp := mem_map_of_mem f hr
  have hrad := mem_map_of_mem P.subtype (hc hp)
  rw [BinaryLinear.SmallParabolicLevi.map_twoCore_eq_radical] at hrad
  have he' : inclusion (show R ≤ H from inf_le_left) r = h := Subtype.ext he
  change π (inclusion (show R ≤ H from inf_le_left) r) ∈ _ at hrad
  rwa [he'] at hrad
end Representation.BinaryConjugationSection
