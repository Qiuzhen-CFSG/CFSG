module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced
public import Theory.Representation.BinaryTransvectionGroups.RootForms.Exchange

/-!
# Root forms along the spanning orbit

Conjugation gives equal root orders along the orbit.  The rank-one exchange
identity consequently makes fixation symmetric.  Since the orbit spans the
space, a nonidentity root moves another center; thus there are two centers
and forms evaluating to one across them.

These are inputs for a three-dimensional root-form seed in the repair of
Aschbacher--Smith G.3.1, printed pp.337--338.  No local irreducibility is used.
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.Reduced
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (GL V)} {Δ : Set V}

theorem RootGeneratedOrbit.stable (r : RootGeneratedOrbit G Δ) :
    ∀ g ∈ G, ∀ x ∈ Δ, g x ∈ Δ := by
  obtain ⟨a, ha⟩ := r.orbit
  rw [ha]
  intro g hg x hx
  obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  exact MulAction.mem_orbit_iff.mpr ⟨(⟨g, hg⟩ : G) * k, rfl⟩

theorem RootGeneratedOrbit.rootGroup_card_eq (r : RootGeneratedOrbit G Δ)
    {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ) :
    Nat.card (rootGroup G x) = Nat.card (rootGroup G y) := by
  obtain ⟨a, rfl⟩ := r.orbit
  have hyx : y ∈ MulAction.orbit G x := by
    rw [MulAction.orbit_eq_iff.mpr hx]
    exact hy
  obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hyx
  change g.val x = y at hg
  rw [← hg, ← rootGroup_conjugate g.property x]
  exact Nat.card_congr ((MulAut.conj g.val).subgroupMap (rootGroup G x)).toEquiv

theorem RootGeneratedOrbit.rootForms_fixation_symm [Finite G]
    (r : RootGeneratedOrbit G Δ) {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ)
    (hfix : ∀ f ∈ rootForms G x, f y = 0) :
    ∀ g ∈ rootForms G y, g x = 0 :=
  BinaryTransvectionGroups.rootForms_fixation_symm (r.nonzero x hx) (r.nonzero y hy)
    (r.rootGroup_card_eq hx hy) hfix

theorem RootGeneratedOrbit.exists_moved_center (r : RootGeneratedOrbit G Δ)
    {x : V} (hx : x ∈ Δ) : ∃ y ∈ Δ, ∃ a ∈ rootGroup G x, a y ≠ y := by
  by_contra hn
  push Not at hn
  have hb : rootGroup G x = ⊥ := by
    apply bot_unique
    intro a ha
    change a = 1
    ext v
    have hv : v ∈ Submodule.span (ZMod 2) Δ := r.span_eq_top ▸ Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem y hy => exact hn y hy a ha
    | zero => exact a.map_zero
    | add v w _ _ hv hw => simp only [map_add, hv, hw]
    | smul c v _ hv => simp only [map_smul, hv]
  have hc := r.large_roots x hx
  rw [hb, Subgroup.card_bot] at hc
  omega

/-- A pair of actual orbit centers with root forms evaluating to one in
both directions. -/
theorem RootGeneratedOrbit.exists_moving_forms [Finite G] (r : RootGeneratedOrbit G Δ) :
    ∃ x ∈ Δ, ∃ y ∈ Δ, ∃ f ∈ rootForms G x, ∃ g ∈ rootForms G y,
      f y = 1 ∧ g x = 1 := by
  obtain ⟨x, hx⟩ := r.nonempty
  obtain ⟨y, hy, a, ha, hay⟩ := r.exists_moved_center hx
  obtain ⟨haG, f, hf, rfl⟩ := (mem_rootGroup_iff (r.nonzero x hx)).mp ha
  have hfm : f ∈ rootForms G x := (mem_rootForms hf).mpr haG
  have hfy : f y = 1 := by
    apply (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1)
    intro hzero
    apply hay
    simp [transvection, hzero]
  have hg : ∃ g ∈ rootForms G y, g x ≠ 0 := by
    by_contra hn
    push Not at hn
    have hz := r.rootForms_fixation_symm hy hx hn f hfm
    rw [hfy] at hz
    exact one_ne_zero hz
  obtain ⟨g, hg, hgx⟩ := hg
  exact ⟨x, hx, y, hy, f, hfm, g, hg, hfy,
    (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hgx⟩

end CFSG.Quasithin.ChapterG.Section03.Reduced
