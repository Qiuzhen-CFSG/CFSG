module
public import Theory.Representation.BinaryConjugationSection.FixedQuotientIndex
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# Sharp fixed-space indices in literal binary sections

Equality in the centralizer-index estimate forces every fixed coordinate
lift to centralize the actual actor. Thus the image of the original
centralizer is the entire fixed space. A second lemma lifts a spanning
sum of coordinate images through the retained section kernel.

The index proof uses strict decrease along proper inclusions of finite
subgroups. No splitting of the central kernel or fixed-point lifting
hypothesis is imposed.

Source application: DGS, *Groups and Graphs* (1985), 7.1 and 10.1--10.4,
printed pp.126 and 154--155; opposite Sylow fixed spaces in the b=1 case.
-/

public section
open Subgroup
namespace Representation.BinaryConjugationSection
open BinaryOffender
variable {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]

/-- Sharpness of the index estimate identifies the full fixed preimage. -/
theorem fixed_coordinates_iff_of_sharp_index
    {H U Z : Subgroup G} [Finite U]
    (σ : Representation (ZMod 2) J W) (π : H →* J)
    (d : BinaryConjugationSection H U Z (σ.comp π)) (A : Subgroup G)
    (hsharp : Nat.card (W ⧸ fixedSpace σ ((A.subgroupOf H).map π)) =
      (centralizer (A : Set G)).relIndex U) (u : U) :
    (d.coordinates u).toAdd ∈ fixedSpace σ ((A.subgroupOf H).map π) ↔
      (u : G) ∈ centralizer (A : Set G) := by
  let F := fixedSpace σ ((A.subgroupOf H).map π)
  let f : U →* Multiplicative (W ⧸ F) :=
    F.mkQ.toAddMonoidHom.toMultiplicative.comp d.coordinates
  have hf : Function.Surjective f := F.mkQ_surjective.comp d.onto
  have hker : (centralizer (A : Set G)).subgroupOf U ≤ f.ker := by
    intro a ha
    change F.mkQ (d.coordinates a).toAdd = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    intro b
    obtain ⟨h, hh, he⟩ := b.property
    change σ (b : J) (d.coordinates a).toAdd = _
    rw [← he]
    have hc : (⟨(h : G) * (a : G) * (h : G)⁻¹,
        (mem_normalizer_iff.mp (d.normalized h.property) a).mp a.property⟩ : U) = a := by
      apply Subtype.ext
      change (h : G) * (a : G) * (h : G)⁻¹ = (a : G)
      have hcomm : (h : G) * (a : G) = (a : G) * (h : G) := ha h hh
      rw [hcomm, mul_inv_cancel_right]
    have hd := d.equivariant h a
    rw [hc] at hd
    exact hd.symm
  have hi : f.ker.index = ((centralizer (A : Set G)).subgroupOf U).index := by
    rw [index_eq_card, Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective f hf).toEquiv]
    exact hsharp
  have he : (centralizer (A : Set G)).subgroupOf U = f.ker := by
    by_contra hn
    have hlt := index_strictAnti (lt_of_le_of_ne hker hn)
    exact (ne_of_lt hlt) hi
  have hm : u ∈ f.ker ↔ (d.coordinates u).toAdd ∈ F := by
    change F.mkQ (d.coordinates u).toAdd = 0 ↔ _
    exact Submodule.Quotient.mk_eq_zero F
  exact hm.symm.trans (by rw [← he]; rfl)

/-- Every fixed vector lifts to the original centralizer when the bound is sharp. -/
theorem image_centralizer_eq_fixed_of_sharp_index
    {H U Z : Subgroup G} [Finite U]
    (σ : Representation (ZMod 2) J W) (π : H →* J)
    (d : BinaryConjugationSection H U Z (σ.comp π)) (A : Subgroup G)
    (hsharp : Nat.card (W ⧸ fixedSpace σ ((A.subgroupOf H).map π)) =
      (centralizer (A : Set G)).relIndex U) :
    d.imageSpace (U ⊓ centralizer (A : Set G)) =
      fixedSpace σ ((A.subgroupOf H).map π) := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := (d.mem_imageSpace_iff _ _).mp hv
    exact (fixed_coordinates_iff_of_sharp_index σ π d A hsharp u).mpr hu.2
  · intro hv
    obtain ⟨u,hu⟩ := d.onto (Multiplicative.ofAdd v)
    have hc : (u : G) ∈ centralizer (A : Set G) :=
      (fixed_coordinates_iff_of_sharp_index σ π d A hsharp u).mp (hu.symm ▸ hv)
    exact (d.mem_imageSpace_iff _ _).mpr ⟨u,⟨u.property,hc⟩,congrArg Multiplicative.toAdd hu⟩

/-- Spanning coordinate images generate the original section when they contain its kernel. -/
theorem section_eq_sup_of_imageSpace_sup_top
    {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}
    (d : BinaryConjugationSection H U Z ρ) (A B : Subgroup G)
    (hA : A ≤ U) (hB : B ≤ U) (hZ : Z ≤ A ⊔ B)
    (hspan : d.imageSpace A ⊔ d.imageSpace B = ⊤) : U = A ⊔ B := by
  apply le_antisymm _ (sup_le hA hB)
  intro u hu
  have hv : (d.coordinates ⟨u,hu⟩).toAdd ∈ d.imageSpace A ⊔ d.imageSpace B := by
    rw [hspan]; trivial
  obtain ⟨x,hx,y,hy,hxy⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a,ha,hax⟩ := (d.mem_imageSpace_iff A x).mp hx
  obtain ⟨b,hb,hby⟩ := (d.mem_imageSpace_iff B y).mp hy
  have he : d.coordinates (a*b) = d.coordinates ⟨u,hu⟩ := by
    rw [map_mul]
    apply Multiplicative.toAdd.injective
    change (d.coordinates a).toAdd + (d.coordinates b).toAdd = _
    rw [hax,hby]
    exact hxy
  have hz : u*((a:G)*(b:G))⁻¹ ∈ Z := by
    apply (d.coordinates_eq_one_iff (⟨u,hu⟩*(a*b)⁻¹)).mp
    rw [map_mul,map_inv,he,mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using
    (A ⊔ B).mul_mem (hZ hz) (mul_mem_sup ha hb)
end Representation.BinaryConjugationSection
