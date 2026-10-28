module

public import Theory.SpecificGroups.BinaryLinear.CubicSylowGeneration
public import Theory.GroupTheory.CubicSylowExtension

/-!
# Cubic overgroups above a binary-linear quotient with inner Sylow action

The minimal parabolics of a binary full flag have index three and generate
the linear group. Inner automorphisms preserving its Sylow subgroup preserve
each of them. Lift these parabolics through the actual K/O₂(K) quotient and
adjoin the ambient Sylow subgroup T. If K escapes M, at least one lifted
index-three overgroup also escapes M.

Source application: the binary-linear rows in the terminal construction of
Aschbacher--Smith 12.9.1, printed p.863 of `refs/quasithin.pdf`. Innerness of
the actual T-action is an explicit premise; graph automorphisms can permute
minimal parabolics, so quotient isomorphism alone is insufficient.
-/

public section
open Subgroup
namespace BinaryLinear.CubicSylowExtension
open OuterCyclic
variable {G : Type*} [Group G] [Finite G]

/-- The actual inner quotient action supplies an escaping cubic overgroup of T. -/
theorem exists_cubic_overgroup {m : ℕ} (hm : 1 ≤ m)
    (T : Sylow 2 G) (K M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M)
    (hn : (T : Subgroup G) ≤ normalizer (K : Set G))
    (eK : (K ⧸ pCore 2 K) ≃* LinearGroup (m + 1))
    (hinner : ∀ (t : G) (ht : t ∈ (T : Subgroup G)),
      (pCore 2 K).quotientAut (K.normalizerMonoidHom ⟨t,hn ht⟩) ∈
        MulAut.innerSubgroup (K ⧸ pCore 2 K))
    (hKM : ¬ K ≤ M) :
    ∃ H : Subgroup G, (T : Subgroup G) ≤ H ∧ H ≤ K ⊔ (T : Subgroup G) ∧
      (T : Subgroup G).relIndex H = 3 ∧ ¬ H ≤ M := by
  apply Subgroup.CubicSylowExtension.exists_cubic_overgroup T K M hTM hn eK
    (MulAut.innerSubgroup _) ?_ ?_ hKM
  · intro t ht
    rw [← MulAut.map_innerSubgroup_congr eK]
    exact mem_map_of_mem (MulAut.congr eK).toMonoidHom (hinner t ht)
  · intro S N _ hlocal
    exact CubicSylowGeneration.sylow_inner_invariant_cubic_generation hm S N hlocal

end BinaryLinear.CubicSylowExtension
