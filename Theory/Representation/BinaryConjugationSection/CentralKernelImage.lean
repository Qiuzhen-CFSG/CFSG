module
public import Theory.Representation.BinaryConjugationSection.Ambient
public import Theory.GroupTheory.PerfectCentralCoverQuasisimple

/-!
# Literal section coordinates through a central kernel

For a perfect actor, a central quotient creates no new fixed vectors in a
section already contained in the actor: the preimage of the center under a
perfect central cover is its center. The given coordinates therefore descend
onto the literal image, with exactly its actor-centralizing kernel and the
specified quotient action. No splitting of a central extension is used.

Source application: the original moved image in Aschbacher--Smith 10.2.9,
printed p.750. The J₄ natural-plus-dual comparison supplies the actor marking.
-/

public noncomputable section
open Subgroup
namespace Representation.BinaryConjugationSection
variable {G K W : Type*} [Group G] [Group K] [AddCommGroup W] [Module (ZMod 2) W]
  {B E : Subgroup G} [Group.IsPerfect B]
  {ρ : Representation (ZMod 2) B W}

theorem exists_map_of_central_kernel
    (d : BinaryConjugationSection B E (E ⊓ centralizer (B : Set G)) ρ)
    (f : G →* K) (hk : f.ker ≤ center G)
    (σ : Representation (ZMod 2) (B.map f) W)
    (hσ : ∀ b, σ (f.subgroupMap B b) = ρ b) :
    Nonempty (BinaryConjugationSection (B.map f) (E.map f)
      ((E.map f) ⊓ centralizer (B.map f : Set K)) σ) := by
  let g := f.subgroupMap E
  have hg : Function.Surjective g := f.subgroupMap_surjective E
  have hker : g.ker ≤ d.coordinates.ker := by
    intro e he
    apply (d.coordinates_eq_one_iff e).mpr
    refine ⟨e.property,?_⟩
    have hf : f e = 1 := congrArg Subtype.val he
    exact (center_le_centralizer B) (hk hf)
  let c := g.liftOfSurjective hg ⟨d.coordinates,hker⟩
  have hc (e : E) : c (g e) = d.coordinates e :=
    g.liftOfRightInverse_comp_apply _ _ _ e
  have hfc : (f.subgroupMap B).ker ≤ center B := by
    intro b hb
    have hh : f b = 1 := congrArg Subtype.val hb
    exact mem_center_iff.mpr (fun a => Subtype.ext (mem_center_iff.mp (hk hh) a))
  let C : PerfectCentralCovering.Cover B (B.map f) :=
    ⟨f.subgroupMap B,f.subgroupMap_surjective B,inferInstance,hfc⟩
  have hfix (e : E) : (e : G) ∈ centralizer (B : Set G) ↔
      f e ∈ centralizer (B.map f : Set K) := by
    constructor
    · intro he
      rintro _ ⟨b,hb,rfl⟩
      simpa only [map_mul] using congrArg f (he b hb)
    · intro he
      have h : f.subgroupMap B (inclusion d.section_le e) ∈ center (B.map f) := by
        apply mem_center_iff.mpr
        intro b
        exact Subtype.ext (he b b.property)
      have hc : inclusion d.section_le e ∈ center B := by
        rw [←C.comap_center]
        exact h
      intro b hb
      exact congrArg B.subtype (mem_center_iff.mp hc ⟨b,hb⟩)
  refine ⟨{ section_le := map_mono d.section_le
            kernel_le := inf_le_left
            normalized := (map_mono d.normalized).trans (le_normalizer_map f)
            coordinates := c
            onto := ?_
            kernel_eq := ?_
            equivariant := ?_ }⟩
  · intro w
    obtain ⟨e,rfl⟩ := d.onto w
    exact ⟨g e,hc e⟩
  · ext x
    obtain ⟨e,rfl⟩ := hg x
    change c (g e) = 1 ↔ f e ∈ E.map f ∧ f e ∈ centralizer (B.map f : Set K)
    rw [hc,d.coordinates_eq_one_iff]
    exact ⟨fun he => ⟨mem_map_of_mem f e.property,(hfix e).mp he.2⟩,
      fun he => ⟨e.property,(hfix e).mpr he.2⟩⟩
  · intro b x
    obtain ⟨b,rfl⟩ := f.subgroupMap_surjective B b
    obtain ⟨e,rfl⟩ := hg x
    have heq : (⟨(f.subgroupMap B b : K) * (g e : K) * (f.subgroupMap B b : K)⁻¹, (mem_normalizer_iff.mp (((map_mono d.normalized).trans (le_normalizer_map f)) (mem_map_of_mem f b.property)) _).mp (g e).property⟩ : E.map f) =
        g ⟨(b:G)*e*(b:G)⁻¹,(mem_normalizer_iff.mp (d.normalized b.property) e).mp e.property⟩ := by
      apply Subtype.ext
      change f b * f e * (f b)⁻¹ = f ((b:G)*e*(b:G)⁻¹)
      simp only [map_mul,map_inv]
    rw [heq,hc,hc,hσ]
    exact d.equivariant b e
end Representation.BinaryConjugationSection
