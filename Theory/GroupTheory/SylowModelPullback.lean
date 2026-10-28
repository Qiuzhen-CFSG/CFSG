module
public import Mathlib.GroupTheory.Sylow
/-!
# Pulling back an embedded model with an aligned Sylow subgroup

An injective model map identifies its image with the model. Pulling this
image back through a surjection gives a surjection onto the model with the
literal restricted kernel. If that kernel is a p-group, the model Sylow
pulls back to a Sylow subgroup. Alignment of the image with a selected
ambient Sylow then lifts through the kernel.

This is the subgroup lifting step used for the E₉:C₄ model in
Aschbacher–Smith E.2.17, printed p.230.
-/
public section
open Subgroup

variable {G Q A : Type*} [Group G] [Group Q] [Group A]
  {p : ℕ}

/-- Lift a model and its aligned Sylow subgroup through a p-group kernel. -/
theorem Sylow.exists_model_pullback
    (q : G →* Q) (hq : Function.Surjective q) (hk : IsPGroup p q.ker)
    (j : A →* Q) (hj : Function.Injective j) (T : Sylow p G) (R : Sylow p A)
    (hRT : (R : Subgroup A).map j ≤ (T : Subgroup G).map q) :
    let L := j.range.comap q
    ∃ g : L →* A, Function.Surjective g ∧
      g.ker = q.ker.subgroupOf L ∧
      (∀ x : L, j (g x) = q x) ∧
      ∃ S : Sylow p L, (S : Subgroup L).map L.subtype ≤ T ∧
        (S : Subgroup L).map g = R := by
  classical
  dsimp only
  let L := j.range.comap q
  let qr : L →* j.range := (q.comp L.subtype).codRestrict j.range (fun x => x.property)
  have hqr : Function.Surjective qr := by
    intro x
    obtain ⟨y,hy⟩ := hq x
    refine ⟨⟨y,?_⟩,?_⟩
    · change q y ∈ j.range
      rw [hy]
      exact x.property
    · exact Subtype.ext hy
  let e := MonoidHom.ofInjective hj
  let g : L →* A := e.symm.toMonoidHom.comp qr
  have hg : Function.Surjective g := e.symm.surjective.comp hqr
  have hi (x : L) : j (g x) = q x := MonoidHom.apply_ofInjective_symm hj (qr x)
  have hker : g.ker = q.ker.subgroupOf L := by
    ext x
    change g x = 1 ↔ q x = 1
    rw [← hi x, ← j.map_one, hj.eq_iff]
  have hgp : IsPGroup p g.ker := by
    rw [hker]
    exact hk.comap_subtype
  let S := R.comapOfKerIsPGroup g hgp (by rw [MonoidHom.range_eq_top.mpr hg]; exact le_top)
  refine ⟨g,hg,hker,hi,S,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    have hxR : g x ∈ (R : Subgroup A) := hx
    have hxq : q x ∈ (T : Subgroup G).map q := by
      rw [← hi x]
      exact hRT (mem_map_of_mem j hxR)
    have hkerT : q.ker ≤ (T : Subgroup G) := hk.le_sylow_of_normal T
    have hpre : ((T : Subgroup G).map q).comap q = T := comap_map_eq_self hkerT
    exact hpre.le hxq
  · exact map_comap_eq_self_of_surjective hg (R : Subgroup A)
