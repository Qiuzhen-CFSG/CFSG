module
public import Theory.GroupTheory.SymmetricFourModelCoreData
public import Theory.GroupTheory.SymmetricFourSylowInvolution
public import Mathlib.GroupTheory.Sylow
/-!
# Trivial Sylow intersections and sections with a prime-power kernel

A faithful subgroup inherits trivial intersections of distinct Sylow
p-subgroups by embedding its Sylows in ambient Sylows. A surjective map with
p-group kernel inherits the same property by taking full Sylow preimages.
For p=2 the symmetric group on four letters obstructs this property: its
normal four-core lies in every Sylow, while its Sylows have order eight.

This section obstruction handles central two-covers in the Bender target
exclusion of Aschbacher–Smith 2.5.6, printed p.554.
-/
public section
open Subgroup
namespace Theory.GroupTheory.SylowIntersection
variable {G H : Type*} [Group G] [Group H]

/-- Equality of Sylow subgroups with nontrivial intersection descends to a subgroup. -/
theorem of_injective {p : ℕ} (f : H →* G) (hf : Function.Injective f)
    (h : ∀ P Q : Sylow p G, (P : Subgroup G) ⊓ Q ≠ ⊥ → P=Q) :
    ∀ P Q : Sylow p H, (P : Subgroup H) ⊓ Q ≠ ⊥ → P=Q := by
  intro P Q hne
  obtain ⟨P',hP'⟩ := P.exists_comap_eq_of_injective hf
  obtain ⟨Q',hQ'⟩ := Q.exists_comap_eq_of_injective hf
  have hi : (P' : Subgroup G) ⊓ Q' ≠ ⊥ := by
    intro hb
    apply hne
    apply le_bot_iff.mp
    intro x hx
    have hpx : f x ∈ P' := by
      change x ∈ (P' : Subgroup G).comap f
      rw [hP']; exact hx.1
    have hqx : f x ∈ Q' := by
      change x ∈ (Q' : Subgroup G).comap f
      rw [hQ']; exact hx.2
    have he : f x=1 := mem_bot.mp (hb ▸ ⟨hpx,hqx⟩)
    exact mem_bot.mpr (hf (he.trans (map_one f).symm))
  apply Sylow.ext
  rw [←hP',←hQ',h P' Q' hi]

/-- A quotient by a p-group kernel inherits the same intersection property. -/
theorem of_surjective {p : ℕ} (f : G →* H) (hf : Function.Surjective f)
    (hk : IsPGroup p f.ker)
    (h : ∀ P Q : Sylow p G, (P : Subgroup G) ⊓ Q ≠ ⊥ → P=Q) :
    ∀ P Q : Sylow p H, (P : Subgroup H) ⊓ Q ≠ ⊥ → P=Q := by
  intro P Q hne
  let P' := P.comapOfKerIsPGroup f hk (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top)
  let Q' := Q.comapOfKerIsPGroup f hk (by rw [MonoidHom.range_eq_top.mpr hf]; exact le_top)
  have hi : (P' : Subgroup G) ⊓ Q' ≠ ⊥ := by
    intro hb
    apply hne
    apply le_bot_iff.mp
    intro x hx
    obtain ⟨y,rfl⟩ := hf x
    have hy : y ∈ (P' : Subgroup G) ⊓ Q' := hx
    have he : y=1 := mem_bot.mp (hb ▸ hy)
    rw [he,map_one]
    exact one_mem _
  have he : (P : Subgroup H).comap f = (Q : Subgroup H).comap f :=
    congrArg Sylow.toSubgroup (h P' Q' hi)
  exact Sylow.ext ((Subgroup.comap_injective hf) he)

/-- S₄ is an obstruction to trivial intersections of Sylow two-subgroups. -/
theorem not_symmetric_four :
    ¬ (∀ P Q : Sylow 2 (Equiv.Perm (Fin 4)),
      (P : Subgroup (Equiv.Perm (Fin 4))) ⊓ Q ≠ ⊥ → P=Q) := by
  intro h
  let P : Sylow 2 (Equiv.Perm (Fin 4)) := default
  obtain ⟨z,hz,ho,_,hc,hP⟩ := symmetric_four_sylow_core_involution P ⟨MulEquiv.refl _⟩
  have hz1 : z≠1 := by intro he; simp [he] at ho
  let : Subsingleton (Sylow 2 (Equiv.Perm (Fin 4))) := ⟨fun Q R => by
    apply h Q R
    intro hb
    exact hz1 (mem_bot.mp (hb ▸ (show z∈(Q:Subgroup _)⊓R from
      ⟨pCore_isPGroup.le_sylow_of_normal Q hz,pCore_isPGroup.le_sylow_of_normal R hz⟩)))⟩
  let : (P : Subgroup (Equiv.Perm (Fin 4))).Normal := P.normal_of_subsingleton
  have hle : (P : Subgroup (Equiv.Perm (Fin 4))) ≤ pCore 2 (Equiv.Perm (Fin 4)) :=
    le_sSup ⟨inferInstance,P.isPGroup'⟩
  have hh := Subgroup.card_le_of_le hle
  change Nat.card P ≤ Nat.card (pCore 2 (Equiv.Perm (Fin 4))) at hh
  omega

/-- An actual S₄ subgroup excludes the Sylow intersection property. -/
theorem not_of_symmetric_four_embedding (f : Equiv.Perm (Fin 4) →* G)
    (hf : Function.Injective f) :
    ¬ (∀ P Q : Sylow 2 G, (P : Subgroup G) ⊓ Q ≠ ⊥ → P=Q) :=
  fun h => not_symmetric_four (of_injective f hf h)
end Theory.GroupTheory.SylowIntersection
