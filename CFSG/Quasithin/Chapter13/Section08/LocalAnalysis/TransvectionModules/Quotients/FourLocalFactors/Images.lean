module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Sections
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.Irreducible

/-!
# Subgroup images in the literal section used in 13.8.6(4)

We form local invariant subspaces from actual subgroup images in B/Z,
and pull invariant subspaces back to subgroups of B. Compatibility with
conjugation identifies the acting subgroup with its image under the actor
map. Neither B nor the ambient group is assumed abelian.

These constructions support the two local planes on printed p.948 of
Aschbacher–Smith, *The Classification of Quasithin Groups* (1 March 2004).
The elementary quotient and its compatible action remain explicit here;
their construction in the source setup is a separate obligation.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

variable {G A : Type*} [Group G] [Group A]
variable (B Z : Subgroup G) [(Z.subgroupOf B).Normal]
  [IsElementaryAbelian 2 (B ⧸ Z.subgroupOf B)]

/-- The actual image of D in the elementary quotient B/Z. -/
def sectionImage (D : Subgroup G) : Submodule (ZMod 2) (Additive (B ⧸ Z.subgroupOf B)) :=
  AddSubgroup.toZModSubmodule 2
    (((D.subgroupOf B).map (QuotientGroup.mk' (Z.subgroupOf B))).toAddSubgroup)

/-- The inverse image in B, included into the original ambient group. -/
def sectionPreimage (W : Submodule (ZMod 2) (Additive (B ⧸ Z.subgroupOf B))) : Subgroup G :=
  ((Subgroup.toAddSubgroup.symm W.toAddSubgroup).comap
    (QuotientGroup.mk' (Z.subgroupOf B))).map B.subtype

theorem mem_sectionPreimage
    (W : Submodule (ZMod 2) (Additive (B ⧸ Z.subgroupOf B))) (b : B) :
    (b : G) ∈ sectionPreimage B Z W ↔
      Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) b) ∈ W := by
  constructor
  · rintro ⟨c, hc, he⟩
    exact (Subtype.ext he : c = b) ▸ hc
  · intro hb
    exact ⟨b, hb, rfl⟩

theorem denominator_le_sectionPreimage (hZB : Z ≤ B)
    (W : Submodule (ZMod 2) (Additive (B ⧸ Z.subgroupOf B))) :
    Z ≤ sectionPreimage B Z W := by
  intro z hz
  apply (mem_sectionPreimage B Z W ⟨z, hZB hz⟩).mpr
  have he : QuotientGroup.mk' (Z.subgroupOf B) ⟨z, hZB hz⟩ = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hz
  rw [he]
  exact W.zero_mem

theorem sectionPreimage_le :
    ∀ W : Submodule (ZMod 2) (Additive (B ⧸ Z.subgroupOf B)),
      sectionPreimage B Z W ≤ B := fun _ => map_subtype_le _

theorem sectionImage_le_iff (D : Subgroup G) (hDB : D ≤ B)
    (W : Submodule (ZMod 2) (Additive (B ⧸ Z.subgroupOf B))) :
    sectionImage B Z D ≤ W ↔ D ≤ sectionPreimage B Z W := by
  constructor
  · intro h d hd
    exact (mem_sectionPreimage B Z W ⟨d, hDB hd⟩).mpr (h ⟨⟨d, hDB hd⟩, hd, rfl⟩)
  · rintro h _ ⟨b, hb, rfl⟩
    exact (mem_sectionPreimage B Z W b).mp (h hb)

theorem sectionPreimage_eq_iff_top
    (W : Submodule (ZMod 2) (Additive (B ⧸ Z.subgroupOf B))) :
    sectionPreimage B Z W = B ↔ W = ⊤ := by
  constructor
  · intro he
    apply top_unique
    intro x _
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (Z.subgroupOf B) x.toMul
    exact (mem_sectionPreimage B Z W b).mp (he.symm ▸ b.property)
  · intro he
    apply le_antisymm (sectionPreimage_le B Z W)
    intro b hb
    apply (mem_sectionPreimage B Z W ⟨b, hb⟩).mpr
    rw [he]
    trivial

variable (P : Subgroup G) (π : P →* A)
  (hPB : P ≤ normalizer (B : Set G))
  (ρ : Representation (ZMod 2) A (Additive (B ⧸ Z.subgroupOf B)))
  (hρ : SectionConjugationAlong P B Z π hPB ρ)

/-- Ambient normalization gives invariance under the actual local actor image. -/
def localImage (R D : Subgroup G) (hRD : R ≤ normalizer (D : Set G)) :
    Subrepresentation (ρ.comp ((R.subgroupOf P).map π).subtype) where
  toSubmodule := sectionImage B Z D
  apply_mem_toSubmodule := by
    rintro ⟨_, p, hp, rfl⟩ _ ⟨b, hb, rfl⟩
    change ρ (π p) (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) b)) ∈ _
    rw [hρ]
    exact ⟨⟨(p : G) * (b : G) * (p : G)⁻¹,
      (mem_normalizer_iff.mp (hPB p.property) b).mp b.property⟩,
      (mem_normalizer_iff.mp (hRD hp) b).mp hb, rfl⟩

include hρ in
/-- An invariant subspace pulls back to a subgroup normalized by P. -/
theorem sectionPreimage_normalized (W : Subrepresentation ρ) :
    P ≤ normalizer (sectionPreimage B Z W.toSubmodule : Set G) := by
  apply le_normalizer_iff.mpr
  rintro p hp b ⟨u, hu, rfl⟩
  let v : B := ⟨p * (u : G) * p⁻¹,
    (mem_normalizer_iff.mp (hPB hp) u).mp u.property⟩
  refine ⟨v, ?_, rfl⟩
  change Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) v) ∈ W
  rw [show Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) v) =
    ρ (π ⟨p, hp⟩) (Additive.ofMul (QuotientGroup.mk' (Z.subgroupOf B) u)) from
      (hρ ⟨p, hp⟩ u).symm]
  exact W.apply_mem_toSubmodule _ hu

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FourLocalFactors

end
