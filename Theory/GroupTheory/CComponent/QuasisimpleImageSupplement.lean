module
public import Theory.GroupTheory.CComponent.QuasisimpleSupplement

/-!
# Sylow-invariant supplements in quasisimple images

A radical supplement invariant under an actual Sylow two-subgroup covers
any perfect image whose quotient by its two-core is quasisimple. The image
Sylow contains the target two-core, so the existing radical-supplement
rigidity theorem applies to the literal homomorphism image.

Source: the equal-star minimal replacement in Aschbacher--Smith 13.6.22,
printed p.932. Its actual source consumer is ComponentSelection.MinimalIntrinsic.
-/

public section
open Subgroup
namespace Theory.GroupTheory
/-- A Sylow-invariant radical supplement fills a quasisimple two-core image. -/
theorem map_radical_supplement_eq_top_of_quasisimple_twoCore
    {A B : Type*} [Group A] [Finite A] [Group B] [Finite B]
    [Group.IsPerfect B] [IsQuasisimple (B ⧸ pCore 2 B)]
    (f : A →* B) (hf : Function.Surjective f)
    (S : Sylow 2 A) (D : Subgroup A)
    (hn : (S : Subgroup A) ≤ normalizer (D : Set A))
    (hgen : solvableRadical A ⊔ D = ⊤) : D.map f = ⊤ := by
  have hgen' : solvableRadical B ⊔ D.map f = ⊤ := by
    apply top_unique
    rw [← map_top_of_surjective f hf, ← hgen, Subgroup.map_sup]
    exact sup_le_sup (map_solvableRadical_le_of_surjective f hf) le_rfl
  have hcore : pCore 2 B ≤ normalizer (D.map f : Set B) :=
    (pCore_isPGroup.le_sylow_of_normal (S.mapSurjective hf)).trans
      ((map_mono hn).trans (D.le_normalizer_map f))
  exact eq_top_of_radical_supplement_of_quasisimple_quotient
    (pCore 2 B) (D.map f) hcore hgen'

end Theory.GroupTheory
