module
public import Stellmacher.OmegaOneCenterMap
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import Theory.GroupTheory.WeakClosureSetFusion

/-!
# Baumann weak closure and centralizer fusion

An ambient automorphism taking Baum(S) into S preserves J(S), since
J(S) lies in Baum(S) and is weakly closed in S. It therefore preserves
Omega1 Z(J(S)); conjugate containment and equal orders identify Baum(S).
Burnside fusion consequently makes N(Baum(T)) control fusion in its full
centralizer for an ambient Sylow two-subgroup T.

The expressions use the elementary Thompson subgroup throughout.
Source: Aschbacher--Smith B.2.2--3 and A.1.35, pp.74--75 and 30;
application to the original pair in 13.2.8(1), p.880.
-/

public section
open Subgroup Stellmacher
namespace Stellmacher
variable {G : Type*} [Group G] [Finite G]

/-- The relative Baumann subgroup is weakly closed under ambient automorphisms. -/
theorem baumann_map_eq_of_le (S : Subgroup G) (e : G ≃* G)
    (hle : (S ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G)).map
      e.toMonoidHom ≤ S) :
    (S ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G)).map
      e.toMonoidHom = S ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) := by
  have hJB : elementaryAbelianMaxJ S ≤ (S ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G)) := by
    refine le_inf (sSup_le fun _ hA => hA.1) ?_
    apply le_centralizer_iff.mpr
    intro z hz
    exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hJ := elementaryAbelianMaxJ_map_eq_of_le S e ((map_mono hJB).trans hle)
  have hE : (omegaOneCenterAmbient (elementaryAbelianMaxJ S)).map e.toMonoidHom =
      omegaOneCenterAmbient (elementaryAbelianMaxJ S) := by
    rw [←omegaOneCenterAmbient_map_injective e.toMonoidHom e.injective,hJ]
  have hcent : (S ⊓ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G)).map
      e.toMonoidHom ≤ centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ S) : Set G) := by
    conv_rhs => rw [←hE]
    rintro _ ⟨x,hx,rfl⟩ _ ⟨z,hz,rfl⟩
    simpa only [map_mul] using congrArg e.toMonoidHom (hx.2 z hz)
  exact eq_of_le_of_card_ge (le_inf hle hcent)
    (card_map_of_injective e.injective).ge

/-- Fusion in the entire Baumann centralizer is controlled by its normalizer. -/
theorem baumann_normalizer_controls_centralizer_fusion (T : Sylow 2 G)
    {x y : G} (hx : x ∈ centralizer ((T : Subgroup G) ⊓
      centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G)) : Set G) : Set G))
    (hy : y ∈ centralizer ((T : Subgroup G) ⊓
      centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G)) : Set G) : Set G))
    (hxy : IsConj x y) :
    ∃ n ∈ normalizer ((T : Subgroup G) ⊓
      centralizer (omegaOneCenterAmbient (elementaryAbelianMaxJ (T : Subgroup G)) : Set G) : Set G),
      n * x * n⁻¹ = y :=
  T.weakly_closed_normalizer_controls_centralizer_fusion _ inf_le_left
    (fun g hg => mem_normalizer_iff_map_conj_eq.mpr
      (baumann_map_eq_of_le (T : Subgroup G) (MulAut.conj g) hg)) hx hy hxy
end Stellmacher
