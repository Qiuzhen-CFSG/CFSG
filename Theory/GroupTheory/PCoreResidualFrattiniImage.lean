module

public import Theory.GroupTheory.PResidual.FrattiniGeneration
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.PGroupCore

/-!
# Prime cores through residual Frattini kernels

A surjection preserves the p-core when its kernel intersects the p-residual
inside the inverse image of the Frattini subgroup modulo that residual's
p-core. Choose a Sylow subgroup in the preimage of the target p-core by
intersecting an ambient Sylow. Its normalizer maps onto the target by the
Frattini argument. Residual Frattini nongeneration then puts the residual
in this normalizer, while the chosen ambient Sylow already normalizes it.

This is the core-invariance step in Aschbacher–Smith, Lemma D.3.3,
combined manuscript of 1 March 2004, printed p.193.
-/

public section
open Subgroup
namespace MonoidHom
variable {G H : Type*} [Group G] [Group H] [Finite G]
  {p : ℕ} [Fact p.Prime]

theorem map_pCore_of_residual_frattini_kernel
    (f : G →* H) (hf : Function.Surjective f)
    (hk : pResidual p G ⊓ f.ker ≤
      ((frattini ((pResidual p G) ⧸ pCore p (pResidual p G))).comap
        (QuotientGroup.mk' (pCore p (pResidual p G)))).map (pResidual p G).subtype) :
    (pCore p G).map f = pCore p H := by
  let Q := (pCore p H).comap f
  let q : Q →* pCore p H := f.subgroupComap (pCore p H)
  have hq : Function.Surjective q := f.subgroupComap_surjective_of_surjective _ hf
  let S : Sylow p G := Sylow.nonempty.some
  obtain ⟨U, hU⟩ := S.exists_subgroupOf_eq_of_normal Q
  let P := (U : Subgroup Q).map Q.subtype
  have hP : P = (S : Subgroup G) ⊓ Q := by
    change (U : Subgroup Q).map Q.subtype = _
    rw [hU, subgroupOf_map_subtype]
  have hS : (S : Subgroup G) ≤ normalizer (P : Set G) := by
    rw [hP]
    exact (le_inf S.toSubgroup.le_normalizer
      (Q.normalizer_eq_top ▸ le_top)).trans inf_normalizer_le_normalizer_inf
  have hUt : (U.mapSurjective hq : Subgroup (pCore p H)) = ⊤ :=
    top_unique ((pCore_isPGroup.to_subgroup ⊤).le_sylow_of_normal _)
  have hQ : Q ≤ P ⊔ f.ker := by
    intro g hg
    have hx : (⟨f g, hg⟩ : pCore p H) ∈ (U.mapSurjective hq : Subgroup _) := by
      rw [hUt]
      exact mem_top _
    obtain ⟨s, hs, he⟩ := hx
    have hfs : f s = f g := congrArg Subtype.val he
    have hgk : g / (s : G) ∈ f.ker := by
      change f (g / (s : G)) = 1
      rw [map_div, hfs, div_self']
    have hm := (P ⊔ f.ker).mul_mem (mem_sup_right hgk)
      (mem_sup_left (mem_map_of_mem Q.subtype hs))
    change g / (s : G) * (s : G) ∈ P ⊔ f.ker at hm
    simpa only [div_mul_cancel] using hm
  have hgen : normalizer (P : Set G) ⊔ f.ker = ⊤ := by
    apply top_unique
    rw [← U.normalizer_sup_eq_top]
    exact sup_le le_sup_left (hQ.trans
      (sup_le (P.le_normalizer.trans le_sup_left) le_sup_right))
  have himage : (normalizer (P : Set G)).map f = ⊤ := by
    have hm := congrArg (map f) hgen
    have hfk : f.ker.map f = ⊥ := Subgroup.map_ker_self f
    simpa only [Subgroup.map_sup, hfk, sup_bot_eq, map_top_of_surjective _ hf] using hm
  have hcore : (pCore p (pResidual p G)).map (pResidual p G).subtype ≤ pCore p G :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  have hcP : pCore p G ≤ P := by
    rw [hP]
    refine le_inf (pCore_isPGroup.le_sylow_of_normal S) ?_
    exact map_le_iff_le_comap.mp
      (le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩)
  have hres : pResidual p G ≤ normalizer (P : Set G) := by
    have hh := pResidual_le_sup_of_frattini_kernel p (normalizer (P : Set G)) f
      (pCore p (pResidual p G)) (by rw [himage]; exact le_top) hk
    exact hh.trans (sup_le le_rfl (hcore.trans (hcP.trans P.le_normalizer)))
  have hn : normalizer (P : Set G) = ⊤ := by
    apply top_unique
    rw [← pResidual_sup_sylow_eq_top S]
    exact sup_le hres hS
  let : P.Normal := normalizer_eq_top_iff.mp hn
  have hc : P ≤ pCore p G := le_sSup ⟨inferInstance, U.isPGroup'.map Q.subtype⟩
  apply le_antisymm
  · exact le_sSup ⟨Normal.map inferInstance f hf, pCore_isPGroup.map f⟩
  · intro x hx
    have hxU : (⟨x, hx⟩ : pCore p H) ∈ (U.mapSurjective hq : Subgroup _) := by
      rw [hUt]
      exact mem_top _
    obtain ⟨s, hs, he⟩ := hxU
    exact ⟨s, hc (mem_map_of_mem Q.subtype hs), congrArg Subtype.val he⟩

end MonoidHom
