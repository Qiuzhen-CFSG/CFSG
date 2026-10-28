module

public import Stellmacher.MainDefs

/-!
# The N₂ condition passes to quotient groups

For finite groups, a surjective homomorphism carries Stellmacher's N₂
condition to its codomain: every normalizer of a nontrivial two-subgroup
there is solvable. No condition on the kernel is needed.

Given a nontrivial two-subgroup `Q` of the codomain, restrict the homomorphism
to the preimage `M` of `N(Q)`. The preimage `L` of `Q` is normal in `M`.
A Sylow two-subgroup of `L` maps onto `Q`, since surjections preserve Sylow
subgroups. Its image `A` in `M` therefore remains nontrivial in the original
group, and the N₂ hypothesis makes that ambient normalizer solvable. The
normalizer of `A` inside `M` is a subgroup of this solvable group.

Frattini's argument gives `N_M(A) L = M`. Since the image of `A` is already
all of `Q`, mapping this equality shows that `N_M(A)` surjects onto `N(Q)`.
Solvability descends through that surjection. The proof uses the exact
normalizer definition in `Stellmacher.MainDefs`, corresponding to the N₂
condition in the introduction of `refs/latex/stellmacher-n-group.tex`,
and Mathlib's Sylow and Frattini theorems. This inheritance supports applying
N₂ results to proper sections in the global recognition development.
-/

namespace Stellmacher

/-- The N₂ condition descends through every surjective homomorphism of finite groups. -/
public theorem isNTwoGroup_of_surjective
    {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (hG : IsNTwoGroup G) :
    IsNTwoGroup H := by
  rintro U ⟨Q, hQne, hQp, rfl⟩
  let N := Subgroup.normalizer (Q : Set H)
  let M := N.comap f
  let projection : M →* N := (f.comp M.subtype).codRestrict N (fun x => x.property)
  have hprojection : Function.Surjective projection := by
    intro x
    obtain ⟨g, hg⟩ := hf x.val
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change f g ∈ N
    exact hg ▸ x.property
  let QN := Q.subgroupOf N
  let L := QN.comap projection
  let _ : L.Normal := inferInstance
  let sylow : Sylow 2 L := Sylow.nonempty.some
  let A : Subgroup M := sylow.map L.subtype
  let restricted : L →* QN :=
    (projection.comp L.subtype).codRestrict QN (fun x => x.property)
  have hrestricted : Function.Surjective restricted := by
    intro x
    obtain ⟨g, hg⟩ := hprojection x.val
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    change projection g ∈ QN
    exact hg ▸ x.property
  have htop : (sylow.mapSurjective hrestricted : Subgroup QN) = ⊤ := by
    apply top_unique
    exact ((hQp.comap_subtype (K := N)).to_subgroup ⊤).le_sylow_of_normal _
  have hAimage : A.map projection = QN := by
    have h := congrArg (fun B : Subgroup QN => B.map QN.subtype) htop
    rw [← MonoidHom.range_eq_map, QN.range_subtype] at h
    change ((sylow : Subgroup L).map restricted).map QN.subtype = QN at h
    rw [Subgroup.map_map] at h
    change (sylow : Subgroup L).map (projection.comp L.subtype) = QN at h
    change ((sylow : Subgroup L).map L.subtype).map projection = QN
    rw [Subgroup.map_map]
    exact h
  let B : Subgroup G := A.map M.subtype
  have hBp : IsPGroup 2 B := (sylow.isPGroup'.map L.subtype).map M.subtype
  have hBne : B ≠ ⊥ := by
    intro hB
    have hA : A = ⊥ := (Subgroup.map_eq_bot_iff_of_injective A M.subtype_injective).mp hB
    have hQN : QN = ⊥ := by rw [← hAimage, hA, Subgroup.map_bot]
    apply hQne
    have h := congrArg (fun C : Subgroup N => C.map N.subtype) hQN
    rw [Subgroup.map_bot] at h
    exact (Subgroup.map_subgroupOf_eq_of_le Q.le_normalizer).symm.trans h
  have hfrattini : Subgroup.normalizer (A : Set M) ⊔ L = ⊤ :=
    sylow.normalizer_sup_eq_top
  have hLimage : L.map projection = QN :=
    Subgroup.map_comap_eq_self_of_surjective hprojection QN
  have hnormalizerImage : (Subgroup.normalizer (A : Set M)).map projection = ⊤ := by
    have h := congrArg (fun C : Subgroup M => C.map projection) hfrattini
    rw [Subgroup.map_sup, hLimage, ← MonoidHom.range_eq_map,
      projection.range_eq_top_of_surjective hprojection] at h
    rwa [sup_eq_left.mpr (hAimage ▸ Subgroup.map_mono A.le_normalizer)] at h
  let _ : Group.IsSolvable (Subgroup.normalizer (B : Set G)) :=
    hG _ ⟨B, hBne, hBp, rfl⟩
  let inclusion : Subgroup.normalizer (A : Set M) →*
      Subgroup.normalizer (B : Set G) :=
    ((M.subtype).comp (Subgroup.normalizer (A : Set M)).subtype).codRestrict _ (by
      intro x
      exact A.le_normalizer_map M.subtype ⟨x, x.property, rfl⟩)
  have hinclusion : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Subgroup.normalizer (B : Set G) => (x : G)) hxy
  let _ : Group.IsSolvable (Subgroup.normalizer (A : Set M)) :=
    Group.isSolvable_of_isSolvable_injective hinclusion
  let onto : Subgroup.normalizer (A : Set M) →* N :=
    projection.comp (Subgroup.normalizer (A : Set M)).subtype
  have honto : Function.Surjective onto := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hnormalizerImage
  exact Group.isSolvable_of_surjective honto

end Stellmacher
