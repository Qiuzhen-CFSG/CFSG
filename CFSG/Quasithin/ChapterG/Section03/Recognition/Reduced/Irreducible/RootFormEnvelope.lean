module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.Irreducible.RootOrbit

/-!
# Propagation of a root-form seed

A separated seed of dimension at least three determines the root forms at
all orbit centers outside the common kernel of its form space. To transfer
a form at such a center, choose a form in the seed envelope detecting that
center. The two forms have a common nonzero kernel vector in the seed, whose
root transfers the original form into the envelope. Equal root orders along
the orbit and the dimensions of evaluation kernels then give equality.

This is a conditional input to the repair of Aschbacher--Smith G.3.1, printed
pp.337--338. The seed remains an explicit hypothesis; neither irreducibility
nor a trivial two-core is required for this propagation step.
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.Reduced
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (GL V)} {Δ : Set V}
variable {W : Submodule (ZMod 2) V}
variable {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)}

/-- Two linear conditions leave a nonzero vector in the seed. Its root
transfers every form at a center detected by the envelope. -/
private theorem seed_rootForms_le [FiniteDimensional (ZMod 2) V]
    (s : IsRootFormSeed G Δ W E) {y : V} (hy : y ∉ E.dualCoannihilator) :
    rootForms G y ≤ E := by
  obtain ⟨g, hgE, hgy⟩ : ∃ g ∈ E, g y ≠ 0 := by
    simpa only [Submodule.mem_dualCoannihilator, not_forall, exists_prop] using hy
  have hgy1 : g y = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hgy
  intro f hf
  let p : W →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    (f.domRestrict W).prod (g.domRestrict W)
  have hdim : Module.finrank (ZMod 2) (ZMod 2 × ZMod 2) <
      Module.finrank (ZMod 2) W := by
    rw [Module.finrank_prod, Module.finrank_self]
    exact lt_of_lt_of_le (by decide) s.dimension_ge_three
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := p) hdim)
  have hfx : f (x : V) = 0 := congrArg Prod.fst hx
  have hgx : g (x : V) = 0 := congrArg Prod.snd hx
  have hxv : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hg : g ∈ rootForms G (x : V) := by
    rw [s.forms x x.property hxv]
    exact ⟨hgE, (mem_line_annihilator _ _).mpr hgx⟩
  have htransfer : f ∈ rootForms G (x : V) :=
    rootForm_transfer hf hfx (transvection_mem_rootGroup_of_form hg)
      (by simp [transvection, hgy1])
  rw [s.forms x x.property hxv] at htransfer
  exact htransfer.1

private theorem finrank_inf_annihilator_add_one [FiniteDimensional (ZMod 2) V]
    {x : V} (hx : x ∉ E.dualCoannihilator) :
    Module.finrank (ZMod 2) ↥(E ⊓ (centerLine x).dualAnnihilator) + 1 =
      Module.finrank (ZMod 2) E := by
  let e : E →ₗ[ZMod 2] ZMod 2 := (Module.Dual.eval (ZMod 2) V x).domRestrict E
  have he : e ≠ 0 := by
    intro hz
    apply hx
    rw [Submodule.mem_dualCoannihilator]
    intro f hf
    exact LinearMap.congr_fun hz ⟨f, hf⟩
  have hk : LinearMap.ker e = (E ⊓ (centerLine x).dualAnnihilator).comap E.subtype := by
    ext f
    change f.val x = 0 ↔ f.val ∈ E ∧ f.val ∈ (centerLine x).dualAnnihilator
    rw [mem_line_annihilator]
    exact ⟨fun h => ⟨f.property, h⟩, And.right⟩
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero he
  rw [hk, (Submodule.comapSubtypeEquivOfLe
    (show E ⊓ (centerLine x).dualAnnihilator ≤ E from inf_le_left)).finrank_eq] at hdim
  exact hdim

/-- A separated root-form seed of dimension at least three propagates along
the root orbit, without any irreducibility hypothesis. -/
theorem RootGeneratedOrbit.rootFormEnvelope_of_seed [Finite G]
    (r : RootGeneratedOrbit G Δ) (s : IsRootFormSeed G Δ W E) :
    IsRootFormEnvelope G Δ E := by
  let : FiniteDimensional (ZMod 2) V := r.finiteDimensional
  have hW : W ≠ ⊥ := Submodule.one_le_finrank_iff.mp
    (le_trans (by decide : 1 ≤ 3) s.dimension_ge_three)
  obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW
  have hxC : x ∉ E.dualCoannihilator := fun hx =>
    hx0 (Submodule.disjoint_def.mp s.separates x hxW hx)
  refine ⟨?_, ?_⟩
  · intro hE
    apply hxC
    simp [hE]
  · intro y hy
    by_cases hyC : y ∈ E.dualCoannihilator
    · exact Or.inl hyC
    right
    have hle : rootForms G y ≤ E ⊓ (centerLine y).dualAnnihilator :=
      le_inf (seed_rootForms_le s hyC) (rootForms_le_annihilator G y)
    have hdim : Module.finrank (ZMod 2) ↥(E ⊓ (centerLine x).dualAnnihilator) =
        Module.finrank (ZMod 2) ↥(E ⊓ (centerLine y).dualAnnihilator) := by
      have hx := finrank_inf_annihilator_add_one hxC
      have hy := finrank_inf_annihilator_add_one hyC
      omega
    let e := LinearEquiv.ofFinrankEq ↥(E ⊓ (centerLine x).dualAnnihilator)
      ↥(E ⊓ (centerLine y).dualAnnihilator) hdim
    have hc : Nat.card (rootForms G y) =
        Nat.card ↥(E ⊓ (centerLine y).dualAnnihilator) := by
      calc
        _ = Nat.card (rootGroup G y) := rootForms_card_eq G (r.nonzero y hy)
        _ = Nat.card (rootGroup G x) := r.rootGroup_card_eq hy (s.points x hxW hx0)
        _ = Nat.card (rootForms G x) := (rootForms_card_eq G hx0).symm
        _ = Nat.card ↥(E ⊓ (centerLine x).dualAnnihilator) := by rw [s.forms x hxW hx0]
        _ = _ := Nat.card_congr e.toEquiv
    let : Finite (rootForms G y) :=
      Finite.of_injective (rootFormsEquiv G (r.nonzero y hy))
        (rootFormsEquiv G (r.nonzero y hy)).injective
    let : Finite ↥(E ⊓ (centerLine y).dualAnnihilator) :=
      Nat.finite_of_card_ne_zero (hc ▸ Nat.card_pos.ne')
    have hsur := (Submodule.inclusion_injective hle).bijective_of_nat_card_le hc.ge
    apply le_antisymm hle
    intro f hf
    obtain ⟨g, hg⟩ := hsur.2 ⟨f, hf⟩
    have hgf : g.val = f := congrArg Subtype.val hg
    exact hgf ▸ g.property

end CFSG.Quasithin.ChapterG.Section03.Reduced
