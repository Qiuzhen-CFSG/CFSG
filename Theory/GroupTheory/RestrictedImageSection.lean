module

public import Theory.GroupTheory.SubgroupImageSection

/-!
# Restricting an image section to a quotient preimage

An actual section over `P.map q` restricts to any subgroup `F` of that image.
If the target subgroup is the literal preimage `F.comap q`, the restricted
section lands there automatically.  This is the map/comap bridge needed when
the Baumann image is a product of transposition four-groups.
-/

public section
open Subgroup
namespace Theory.GroupTheory

variable {G H : Type*} [Group G] [Group H]

theorem exists_restricted_comap_section
    (q : G →* H) (P R : Subgroup G) (F : Subgroup H)
    (σ : P.map q →* P)
    (hσ : (q.comp P.subtype).comp σ = (P.map q).subtype)
    (hR : R = F.comap q) (hF : F ≤ P.map q) :
    ∃ τ : F →* R,
      (q.comp R.subtype).comp τ = F.subtype := by
  let i : F →* P.map q := inclusion hF
  let s : F →* P := σ.comp i
  have hs (x : F) : q (s x) = (x : H) := by
    have hh := DFunLike.congr_fun hσ (i x)
    exact hh
  have hsR (x : F) : (s x : G) ∈ R := by
    rw [hR]
    change q (s x) ∈ F
    rw [hs x]
    exact x.property
  let τ : F →* R :=
    { toFun := fun x => ⟨s x, hsR x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp }
  refine ⟨τ,?_⟩
  ext x
  exact hs x

theorem exists_restricted_subgroup_comap_section
    (q : G →* H) (P R : Subgroup G) (F E : Subgroup H)
    (σ : P.map q →* P)
    (hσ : (q.comp P.subtype).comp σ = (P.map q).subtype)
    (hR : R = F.comap q) (hE : E ≤ P.map q) (hEF : E ≤ F) :
    ∃ τ : E →* R,
      (q.comp R.subtype).comp τ = E.subtype ∧
        ∀ x : E, ((τ x : R) : G) ∈ P := by
  let i : E →* P.map q := inclusion hE
  let s : E →* P := σ.comp i
  have hs (x : E) : q (s x) = (x : H) := by
    have hh := DFunLike.congr_fun hσ (i x)
    exact hh
  have hsR (x : E) : (s x : G) ∈ R := by
    rw [hR]
    change q (s x) ∈ F
    rw [hs x]
    exact hEF x.property
  let τ : E →* R :=
    { toFun := fun x => ⟨s x, hsR x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro x y; apply Subtype.ext; simp }
  refine ⟨τ, ?_, ?_⟩
  ext x
  exact hs x
  intro x
  exact (s x).property

end Theory.GroupTheory
