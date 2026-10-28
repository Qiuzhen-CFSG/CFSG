module

public import CFSG.Quasithin.ChapterG.Section06.Source
public import Theory.Representation.BinaryOffender.RankOneCentralizer
public import Theory.SpecificGroups.Symmetric.InnerAutomorphisms
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Faithful ambient placement from the original transvection

An element centralizing the normal closure centralizes every conjugate of the
original involution, hence fixes each binary displacement line pointwise.
Those lines span V by the original G.6.1 hypothesis. Faithfulness gives a
trivial centralizer of the normal closure.

If that normal closure has only inner automorphisms, its faithful ambient
conjugation action forces it to be the whole group. The actual S7 model
therefore identifies the original ambient actor without any fixed-extension
or module-normalizer reconstruction.
Source: Aschbacher–Smith, C.5.12, p.163, and G.6.4, pp.345–346.
-/

public section
open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterG.Section06
universe u v
variable {G : Type u} {V : Type v} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
variable {κ : CFSG.Quasithin.GroupClass} {ρ : Representation (ZMod 2) G V} {a : G}
  {Cover : Type u} [Group Cover] {q : Cover →* G}

theorem Hypotheses.rank_one_centralizer_normalClosure_eq_bot
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    centralizer (normalClosure ({a} : Set G) : Set G) = ⊥ := by
  let := h.finite_module
  apply (eq_bot_iff_forall _).mpr
  intro b hb
  apply h.faithful
  ext v
  have hfix : ∀ w ∈ conjugateDisplacementSpan ρ a ⊤, ρ b w = w := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨g, _, v, rfl⟩ := hw
      let t := g * a * g⁻¹
      have ht : t ∈ normalClosure ({a} : Set G) :=
        (inferInstance : (normalClosure ({a} : Set G)).Normal).conj_mem a
          (subset_normalClosure (Set.mem_singleton a)) g
      have hc : Commute t b := mem_centralizer_iff.mp hb t ht
      have ht1 : Module.finrank (ZMod 2) (LinearMap.range (ρ t - LinearMap.id)) = 1 := by
        have he := fixedCodim_zpowers_conj ρ a g
        simp only [fixedCodim_zpowers_eq_displacement_rank] at he
        exact he.trans hr
      have he : ρ g (ρ a v - v) = ρ t (ρ g v) - ρ g v := by
        simp only [t, map_sub, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
      rw [he]
      exact fixes_displacement_of_commute_rank_one ρ t b ht1 hc _
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul c x _ hx => rw [map_smul, hx]
  simpa only [map_one, Module.End.one_apply] using
    hfix v (h.generated.symm ▸ (Submodule.mem_top : v ∈ (⊤ : Submodule (ZMod 2) V)))

theorem Hypotheses.normalClosure_eq_top_of_inner_automorphisms
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (hinner : Function.Surjective (MulAut.conj : (normalClosure ({a} : Set G)) →*
      MulAut (normalClosure ({a} : Set G)))) :
    normalClosure ({a} : Set G) = ⊤ := by
  apply top_unique
  intro g _
  obtain ⟨k, hk⟩ := hinner (MulAut.conjNormal g)
  have hm : g ∈ (MulAut.innerSubgroup (normalClosure ({a} : Set G))).comap MulAut.conjNormal :=
    ⟨k, hk⟩
  rw [MulAut.conjNormal_comap_innerSubgroup,
    h.rank_one_centralizer_normalClosure_eq_bot hr, sup_bot_eq] at hm
  exact hm

theorem Hypotheses.ambient_symmetric_seven_of_normalClosure
    (h : Hypotheses κ ρ a q)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1)
    (e : normalClosure ({a} : Set G) ≃* Equiv.Perm (Fin 7)) :
    Nonempty (G ≃* Equiv.Perm (Fin 7)) := by
  have hi : Function.Surjective (MulAut.conj : (normalClosure ({a} : Set G)) →*
      MulAut (normalClosure ({a} : Set G))) := by
    intro f
    obtain ⟨p, hp⟩ := Equiv.Perm.conj_surjective_of_degree (by decide : 5 ≤ 7)
      (by decide) (MulAut.congr e f)
    refine ⟨e.symm p, ?_⟩
    apply (MulAut.congr e).injective
    rw [MulAut.congr_conj, e.apply_symm_apply]
    exact hp
  have htop := h.normalClosure_eq_top_of_inner_automorphisms hr hi
  exact ⟨(topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans e⟩
end CFSG.Quasithin.ChapterG.Section06
