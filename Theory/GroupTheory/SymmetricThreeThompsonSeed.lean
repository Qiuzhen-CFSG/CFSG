module
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.SylowNormalGenerationFrattini
public import Stellmacher.ElementaryAbelianMaxJFixedIntersection

/-!
# Thompson generation detected by a central omega seed

A Sylow two-subgroup normally generates a finite group whose two-core
quotient is S₃. If its Thompson subgroup lies in the two-core, its central
omega subgroup is normal. When the Sylow subgroup centralizes that omega
subgroup, normal generation makes the whole group centralize it. Thus a
moved omega seed detects escape of the Thompson subgroup from the two-core.

The original paired-point groups in Aschbacher--Smith 13.2.12 use this
criterion on both vertices, before the B.5/F.6 comparison (printed p.882).
-/

public section
open Subgroup Stellmacher
open scoped IsMulCommutative

namespace Stellmacher.SymmetricThreeSeed
variable {D : Type*} [Group D] [Finite D]

/-- The literal Sylow subgroup normally generates an S₃ two-core extension. -/
theorem sylow_normally_generates
    (S : Sylow 2 D) (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 3)) :
    normalClosure (S : Set D) = ⊤ := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 D))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 D := by
    ext x
    change e (QuotientGroup.mk' _ x) = 1 ↔ x ∈ pCore 2 D
    rw [← e.map_one, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have he : (normalClosure (S : Set D)).map f = ⊤ := by
    rw [map_normalClosure _ _ hf]
    exact normalClosure_sylow_eq_top_of_involutions (S.mapSurjective hf)
      (symmetric_involutions_generate (Fin 3))
  have hker : f.ker ≤ normalClosure (S : Set D) :=
    hk ▸ (pCore_isPGroup.le_sylow_of_normal S).trans le_normalClosure
  have hh := congrArg (comap f) he
  rwa [comap_map_eq,comap_top,sup_of_le_left hker] at hh

/-- A moved central omega seed prevents Thompson containment in the two-core. -/
theorem thompson_not_le_core_of_moved_alpha
    (S : Sylow 2 D) (e : (D ⧸ pCore 2 D) ≃* Equiv.Perm (Fin 3))
    (hfix : (S : Subgroup D) ≤ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup D)) : Set D))
    (x : D) (hx : x ∈ omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup D)))
    (hmove : x ∉ center D) :
    ¬ elementaryAbelianMaxJ (S : Subgroup D) ≤ pCore 2 D := by
  intro hle
  have hj := elementaryAbelianMaxJ_eq_of_intermediate (S : Subgroup D) (pCore 2 D)
    hle (pCore_isPGroup.le_sylow_of_normal S)
  have hn : (elementaryAbelianMaxJ (S : Subgroup D)).Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    rw [←hj,←(pCore 2 D).normalizer_eq_top]
    exact normalizer_le_normalizer_elementaryAbelianMaxJ _
  let := hn
  let E := omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup D))
  have hEn : E.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    apply mem_normalizer_iff_map_conj_eq.mpr
    rw [← omegaOneCenterAmbient_map_injective _ (MulAut.conj g).injective]
    rw [mem_normalizer_iff_map_conj_eq.mp
      ((normalizer_eq_top_iff.mpr hn).ge (mem_top g))]
  let := hEn
  have hc : (⊤ : Subgroup D) ≤ centralizer (E : Set D) := by
    rw [←sylow_normally_generates S e]
    exact normalClosure_le_normal hfix
  apply hmove
  exact mem_center_iff.mpr (fun g => (hc (mem_top g) x hx).symm)
end Stellmacher.SymmetricThreeSeed
