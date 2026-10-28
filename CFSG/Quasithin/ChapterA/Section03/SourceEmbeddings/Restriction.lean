module

public import CFSG.Quasithin.ChapterA.Section03.Basic
public import Theory.GroupTheory.SylowSubnormalIntersection

/-!
# Restriction of the original local C-component condition

Shrink the actor subgroup to its intersection with an overgroup containing
the component, and transport the resulting component along the actual
subgroup inclusion. For a subnormal overgroup the intersection with the
original Sylow is again a full Sylow.

Source: the replacement of the ambient group by its containing component
in Aschbacher–Smith A.3.12, printed p.48.
-/

public section
open Subgroup
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G]

/-- Restrict to an overgroup of B, intersecting the original actor subgroup. -/
theorem local_restrict {B S L : Subgroup G}
    (hB : B ∈ localCComponents S) (hBL : B ≤ L) :
    B.subgroupOf L ∈ localCComponents (S.subgroupOf L) := by
  have hlocal : B ∈ localCComponents (S ⊓ L) := localCComponents_antitone inf_le_left hB
  let e := (subgroupOfEquivOfLe (sup_le hBL (show S ⊓ L ≤ L from inf_le_right))).symm
  have h := hlocal.map_equiv e
  have he : (B.subgroupOf (B ⊔ (S ⊓ L))).map e.toMonoidHom =
      (B.subgroupOf L).subgroupOf ((B ⊔ (S ⊓ L)).subgroupOf L) := by
    ext x
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact hb
    · intro hx
      exact ⟨⟨x, x.property⟩, hx, rfl⟩
  rw [he, subgroupOf_sup hBL inf_le_right] at h
  have hSL : (S ⊓ L).subgroupOf L = S.subgroupOf L := by
    ext x
    exact and_iff_left x.property
  rw [hSL] at h
  exact h

/-- Restriction uses the full intersection of the original Sylow, with no
new conjugation choice in the resulting local-component statement. -/
theorem exists_local_sylow_restriction [Finite G]
    (T : Sylow 2 G) {B L : Subgroup G}
    (hB : B ∈ localCComponents T) (hBL : B ≤ L) (hL : L.IsSubnormal) :
    ∃ S : Sylow 2 L, (S : Subgroup L) = (T : Subgroup G).subgroupOf L ∧
      B.subgroupOf L ∈ localCComponents S := by
  obtain ⟨S, hS⟩ := T.exists_subgroupOf_eq_of_subnormal L hL
  exact ⟨S, hS, hS.symm ▸ local_restrict hB hBL⟩

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
