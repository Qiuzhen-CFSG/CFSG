module

public import Theory.GroupTheory.PCoreResidualFrattiniImage

/-!
# Sylow intersections with a residual Frattini kernel

Assume a surjection kills the p-core and its kernel meets the p-residual
inside the residual's core–Frattini subgroup. Intersect a prescribed
Sylow subgroup with the kernel. Frattini's argument makes its normalizer
surject onto the target, and residual nongeneration makes that normalizer
contain the residual. The prescribed Sylow already normalizes the
intersection, so the intersection is normal and is exactly the p-core.

Source application: Aschbacher–Smith, Lemma 3.2.2(8), combined manuscript
of 1 March 2004, printed p.579: C_T(V)=O₂(M⁺T).
-/

public section
open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G]
  {p : ℕ} [Fact p.Prime]

/-- The original Sylow/kernel intersection is the prime core under the
precise residual Frattini kernel condition. -/
theorem sylow_inf_ker_eq_pCore_of_residual_frattini_kernel
    (f : G →* H) (hf : Function.Surjective f) (S : Sylow p G)
    (hkill : pCore p G ≤ f.ker)
    (hk : pResidual p G ⊓ f.ker ≤
      ((frattini ((pResidual p G) ⧸ pCore p (pResidual p G))).comap
        (QuotientGroup.mk' (pCore p (pResidual p G)))).map (pResidual p G).subtype) :
    (S : Subgroup G) ⊓ f.ker = pCore p G := by
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal f.ker
  let P := (U : Subgroup f.ker).map f.ker.subtype
  have hP : P = (S : Subgroup G) ⊓ f.ker := by
    change (U : Subgroup f.ker).map f.ker.subtype = _
    rw [hU, subgroupOf_map_subtype]
  have hS : (S : Subgroup G) ≤ normalizer (P : Set G) := by
    rw [hP]
    exact (le_inf S.toSubgroup.le_normalizer
      (f.ker.normalizer_eq_top ▸ le_top)).trans inf_normalizer_le_normalizer_inf
  have himage : (normalizer (P : Set G)).map f = ⊤ := by
    have hm := congrArg (map f) U.normalizer_sup_eq_top
    simpa only [Subgroup.map_sup, Subgroup.map_ker_self, sup_bot_eq,
      map_top_of_surjective _ hf] using hm
  have hcore : (pCore p (pResidual p G)).map (pResidual p G).subtype ≤ pCore p G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  have hcP : pCore p G ≤ P := by
    rw [hP]
    exact le_inf (pCore_isPGroup.le_sylow_of_normal S) hkill
  have hres : pResidual p G ≤ normalizer (P : Set G) := by
    have hh := pResidual_le_sup_of_frattini_kernel p (normalizer (P : Set G)) f
      (pCore p (pResidual p G)) (by rw [himage]; exact le_top) hk
    exact hh.trans (sup_le le_rfl (hcore.trans (hcP.trans P.le_normalizer)))
  have hn : normalizer (P : Set G) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top S]
    exact sup_le hres hS
  let : P.Normal := normalizer_eq_top_iff.mp hn
  have hPc : P ≤ pCore p G := le_sSup ⟨inferInstance, U.isPGroup'.map f.ker.subtype⟩
  exact hP.symm.trans (le_antisymm hPc hcP)

end MonoidHom
