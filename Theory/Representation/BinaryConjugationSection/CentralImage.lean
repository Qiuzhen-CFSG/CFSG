module
public import Theory.Representation.BinaryConjugationSection

/-!
# Reduced module sections survive a containing central quotient

If the kernel of a homomorphism is contained in the coordinate kernel of
a binary module section, its image still surjects onto the module. In a
containing central quotient this kernel inclusion follows whenever the
section kernel contains its fixed points under the original actor.

This is the literal subquotient comparison used in Aschbacher--Smith
10.2.9, printed p.750: V₁ ∩ Z(I) ≤ C_V₁(L). It retains fixed vectors and
requires neither irreducibility nor a split module.
-/

public section

open Subgroup
namespace Representation.BinaryConjugationSection
variable {G K : Type*} [Group G] [Group K] [Finite G]
  {H A B : Subgroup G} {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} (d : BinaryConjugationSection H A B ρ)

/-- A smaller kernel leaves an image at least as large as the coordinate module. -/
theorem card_le_range (f : A →* K) (hk : f.ker ≤ d.coordinates.ker) :
    Nat.card W ≤ Nat.card f.range := by
  let g := QuotientGroup.lift f.ker d.coordinates (fun a ha => MonoidHom.mem_ker.mp (hk ha))
  have hg : Function.Surjective g := by
    intro w
    obtain ⟨a,ha⟩ := d.onto w
    exact ⟨QuotientGroup.mk' f.ker a,ha⟩
  have hc := Nat.card_le_card_of_surjective g hg
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hc
  exact hc

include d in
/-- The reduced module is a quotient of its literal image in I/Z(I). -/
theorem card_le_central_image (I : Subgroup G) (hHI : H ≤ I) (hAI : A ≤ I)
    (hB : A ⊓ centralizer (H : Set G) ≤ B) :
    Nat.card W ≤ Nat.card ((A.subgroupOf I).map (QuotientGroup.mk' (center I))) := by
  let f := (QuotientGroup.mk' (center I)).comp (inclusion hAI)
  have hk : f.ker ≤ d.coordinates.ker := by
    intro a ha
    apply MonoidHom.mem_ker.mpr
    apply (d.coordinates_eq_one_iff a).mpr
    apply hB
    refine ⟨a.property,?_⟩
    have hz : inclusion hAI a ∈ center I := (QuotientGroup.eq_one_iff _).mp ha
    intro h hh
    exact congrArg I.subtype (mem_center_iff.mp hz (⟨h,hHI hh⟩ : I))
  have he : f.range = (A.subgroupOf I).map (QuotientGroup.mk' (center I)) := by
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact ⟨inclusion hAI a,a.property,rfl⟩
    · rintro ⟨a,ha,rfl⟩
      exact ⟨⟨a,ha⟩,rfl⟩
  simpa only [he] using d.card_le_range f hk
end Representation.BinaryConjugationSection
