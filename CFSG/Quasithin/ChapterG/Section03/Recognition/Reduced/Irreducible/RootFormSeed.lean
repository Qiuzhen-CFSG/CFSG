module

public import CFSG.Quasithin.ChapterG.Section03.Recognition.Reduced.Irreducible.RootOrbit

/-!
# A three-dimensional binary root-form seed

A spanning orbit of nonzero centers, with finite root groups of order greater
than two, contains a three-dimensional space whose seven nonzero vectors are
centers. Their root-form spaces are the hyperplanes in one common dual space,
and that dual space separates the three-dimensional space.

Start with mutually moving centers `x,y`. A nonzero root form vanishing at both
centers detects a third center `z`. Transfer of forms gives the root-form pencil
at `z` inside `E = rootForms G x ⊔ rootForms G y`. Three forms with independent
evaluations separate `span {x,y,z}`; conjugation by explicit transvections gives
the other four points and their pencils.

Source motivation: Aschbacher--Smith, combined manuscript of 1 March 2004,
G.3.1, printed pp.337--338. This is a local construction for the repaired
recognition argument, without global irreducibility or full-action recognition.
-/

@[expose] public section

open BinaryLinear BinaryTransvectionGroups
namespace CFSG.Quasithin.ChapterG.Section03.Reduced
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {G : Subgroup (GL V)} {Δ : Set V}

private theorem binary_scalar (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

private theorem transfer_form {x y : V} {f g : Module.Dual (ZMod 2) V}
    (hf : f ∈ rootForms G x) (hfy : f y = 0)
    (hg : g ∈ rootForms G y) (hgx : g x = 1) : f ∈ rootForms G y := by
  apply rootForm_transfer hf hfy (transvection_mem_rootGroup_of_form hg)
  simp [transvection, hgx]

private theorem moving_symm [Finite G] (r : RootGeneratedOrbit G Δ)
    {x y : V} (hx : x ∈ Δ) (hy : y ∈ Δ)
    {f : Module.Dual (ZMod 2) V} (hf : f ∈ rootForms G x) (hfy : f y = 1) :
    ∃ g ∈ rootForms G y, g x = 1 := by
  by_contra hn
  have hh : ∀ g ∈ rootForms G y, g x = 0 := by
    intro g hg
    rcases binary_scalar (g x) with hh | hh
    · exact hh
    · exact False.elim (hn ⟨g, hg, hh⟩)
  have hh := r.rootForms_fixation_symm hy hx hh f hf
  rw [hfy] at hh
  exact one_ne_zero hh

/-- A root at `x` moving `y` identifies the pencil at `x` in the sum of the two
root-form spaces. -/
private theorem pair_pencil {x y : V} {f : Module.Dual (ZMod 2) V}
    (hf : f ∈ rootForms G x) (hfy : f y = 1) :
    rootForms G x = (rootForms G x ⊔ rootForms G y) ⊓ (centerLine x).dualAnnihilator := by
  apply le_antisymm
  · exact le_inf le_sup_left (rootForms_le_annihilator G x)
  · intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hh.1
    have hbx : b x = 0 := by
      have hab := (mem_line_annihilator x (a + b)).mp hh.2
      simpa only [LinearMap.add_apply, rootForms_apply_center ha, zero_add] using hab
    exact (rootForms G x).add_mem ha (transfer_form hb hbx hf hfy)

/-- More than two forms cannot inject into the binary field by evaluation. -/
private theorem exists_kernel_form [Finite G] (r : RootGeneratedOrbit G Δ)
    {x : V} (hx : x ∈ Δ) (y : V) :
    ∃ u ∈ rootForms G x, u ≠ 0 ∧ u y = 0 := by
  by_contra hn
  have hz : ∀ u ∈ rootForms G x, u y = 0 → u = 0 := by
    intro u hu huy
    by_contra hu0
    exact hn ⟨u, hu, hu0, huy⟩
  have hi : Function.Injective (fun u : rootForms G x => u.val y) := by
    intro a b hab
    apply Subtype.ext
    apply sub_eq_zero.mp
    apply hz (a.val - b.val) ((rootForms G x).sub_mem a.property b.property)
    simpa only [LinearMap.sub_apply, sub_eq_zero] using hab
  have hc := Nat.card_le_card_of_injective _ hi
  rw [rootForms_card_eq G (r.nonzero x hx)] at hc
  have h2 : Nat.card (ZMod 2) = 2 := by simp
  rw [h2] at hc
  exact (not_le_of_gt (r.large_roots x hx)) hc

private theorem exists_detected_center (r : RootGeneratedOrbit G Δ)
    {u : Module.Dual (ZMod 2) V} (hu : u ≠ 0) : ∃ z ∈ Δ, u z = 1 := by
  by_contra hn
  have hz : ∀ z ∈ Δ, u z = 0 := by
    intro z hz
    rcases binary_scalar (u z) with hh | hh
    · exact hh
    · exact False.elim (hn ⟨z, hz, hh⟩)
  apply hu
  ext v
  have hv : v ∈ Submodule.span (ZMod 2) Δ := r.span_eq_top ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem z hz' => exact hz z hz'
  | zero => exact u.map_zero
  | add v w _ _ hv hw => simp [hv, hw]
  | smul a v _ hv => simp [hv]

private theorem form_conjugate {a : GL V} (ha : a ∈ G) {x : V}
    {f : Module.Dual (ZMod 2) V} (hf : f ∈ rootForms G x) :
    f.comp a.symm.toLinearMap ∈ rootForms G (a x) := by
  refine ⟨by simpa using hf.1, ?_⟩
  simpa only [transvection_conj] using G.mul_mem (G.mul_mem ha hf.2) (G.inv_mem ha)

/-- A transvection whose form lies in the envelope preserves that envelope
and carries the pencil identity to the image center. -/
private theorem pencil_transvection
    {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)} {x y : V}
    {h : Module.Dual (ZMod 2) V} (hh : h ∈ rootForms G x) (hhE : h ∈ E)
    (hy : rootForms G y = E ⊓ (centerLine y).dualAnnihilator) :
    rootForms G (transvection x h hh.1 y) =
      E ⊓ (centerLine (transvection x h hh.1 y)).dualAnnihilator := by
  let t := transvection x h hh.1
  have ht : t ∈ G := hh.2
  have hcomp (f : Module.Dual (ZMod 2) V) :
      f.comp t.toLinearMap = f + (f x) • h := by
    ext v
    simp [t, transvection, mul_comm]
  have hmem {f : Module.Dual (ZMod 2) V} (hf : f ∈ E) : f.comp t.toLinearMap ∈ E := by
    rw [hcomp]
    exact E.add_mem hf (E.smul_mem _ hhE)
  apply le_antisymm
  · intro f hf
    have hc := form_conjugate (G.inv_mem ht) hf
    have hc' : f.comp t.toLinearMap ∈ rootForms G y := by
      change f.comp t.symm.symm.toLinearMap ∈ rootForms G (t.symm (t y)) at hc
      simpa only [LinearEquiv.symm_symm, LinearEquiv.symm_apply_apply] using hc
    rw [hy] at hc'
    refine ⟨?_, rootForms_le_annihilator G (t y) hf⟩
    have he := E.sub_mem hc'.1 (E.smul_mem (f x) hhE)
    rwa [hcomp, add_sub_cancel_right] at he
  · intro f hf
    have hc : f.comp t.toLinearMap ∈ rootForms G y := by
      rw [hy]
      exact ⟨hmem hf.1, (mem_line_annihilator _ _).mpr
        ((mem_line_annihilator (t y) f).mp hf.2)⟩
    have hd := form_conjugate ht hc
    have he : (f.comp t.toLinearMap).comp t.symm.toLinearMap = f := by
      ext v
      exact congrArg f (t.apply_symm_apply v)
    rwa [he] at hd

/-- The common form detecting `z` transfers the adjusted forms to `z`.
Subtracting a multiple of one adjusted form proves the reverse containment. -/
private theorem third_pencil [Finite G] (r : RootGeneratedOrbit G Δ)
    {x y z : V} (hx : x ∈ Δ) (hy : y ∈ Δ) (hz : z ∈ Δ)
    {f g u : Module.Dual (ZMod 2) V}
    (hf : f ∈ rootForms G x) (hfy : f y = 1)
    (hg : g ∈ rootForms G y) (hgx : g x = 1)
    (hu : u ∈ rootForms G x) (huy : u y = 0) (huz : u z = 1) :
    let E := rootForms G x ⊔ rootForms G y
    ∃ F ∈ rootForms G x, ∃ H ∈ rootForms G y,
      F ∈ rootForms G z ∧ H ∈ rootForms G z ∧
      F y = 1 ∧ F z = 0 ∧ H x = 1 ∧ H z = 0 ∧
      rootForms G z = E ⊓ (centerLine z).dualAnnihilator := by
  dsimp only
  let E := rootForms G x ⊔ rootForms G y
  have hu' : u ∈ rootForms G y := transfer_form hu huy hg hgx
  obtain ⟨a, ha, hax⟩ := moving_symm r hx hz hu huz
  obtain ⟨b, hb, hby⟩ := moving_symm r hy hz hu' huz
  have transfer_x {k : Module.Dual (ZMod 2) V} (hk : k ∈ rootForms G x)
      (hkz : k z = 0) : k ∈ rootForms G z := transfer_form hk hkz ha hax
  have transfer_y {k : Module.Dual (ZMod 2) V} (hk : k ∈ rootForms G y)
      (hkz : k z = 0) : k ∈ rootForms G z := transfer_form hk hkz hb hby
  let F := f - f z • u
  let H := g - g z • u
  have hFx : F ∈ rootForms G x := (rootForms G x).sub_mem hf ((rootForms G x).smul_mem _ hu)
  have hHy : H ∈ rootForms G y := (rootForms G y).sub_mem hg ((rootForms G y).smul_mem _ hu')
  have hFz : F z = 0 := by simp [F, huz]
  have hHz : H z = 0 := by simp [H, huz]
  have hFy : F y = 1 := by simp [F, huy, hfy]
  have hHx : H x = 1 := by simp [H, hu.1, hgx]
  refine ⟨F, hFx, H, hHy, transfer_x hFx hFz, transfer_y hHy hHz,
    hFy, hFz, hHx, hHz, ?_⟩
  apply le_antisymm
  · intro k hk
    refine ⟨?_, rootForms_le_annihilator G z hk⟩
    have hk' : k - k x • H ∈ rootForms G z :=
      (rootForms G z).sub_mem hk ((rootForms G z).smul_mem _ (transfer_y hHy hHz))
    have hkx : (k - k x • H) x = 0 := by simp [hHx]
    have hmem := transfer_form hk' hkx hu huz
    have hsum : k - k x • H + k x • H ∈ E :=
      E.add_mem ((show rootForms G x ≤ E from le_sup_left) hmem)
        (E.smul_mem _ ((show rootForms G y ≤ E from le_sup_right) hHy))
    simpa using hsum
  · intro k hk
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hk.1
    have hab : a z + b z = 0 := (mem_line_annihilator _ _).mp hk.2
    have ha' : a - a z • u ∈ rootForms G z :=
      transfer_x ((rootForms G x).sub_mem ha ((rootForms G x).smul_mem _ hu)) (by simp [huz])
    have hb' : b - b z • u ∈ rootForms G z :=
      transfer_y ((rootForms G y).sub_mem hb ((rootForms G y).smul_mem _ hu')) (by simp [huz])
    have hh := (rootForms G z).add_mem ha' hb'
    rwa [sub_add_sub_comm, ← add_smul, hab, zero_smul, sub_zero] at hh

private theorem add_point_pencil (r : RootGeneratedOrbit G Δ)
    {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)} {x y : V}
    (hy : y ∈ Δ) {h : Module.Dual (ZMod 2) V}
    (hh : h ∈ rootForms G x) (hhE : h ∈ E) (hhy : h y = 1)
    (hp : rootForms G y = E ⊓ (centerLine y).dualAnnihilator) :
    x + y ∈ Δ ∧ rootForms G (x + y) = E ⊓ (centerLine (x + y)).dualAnnihilator := by
  have he : transvection x h hh.1 y = x + y := by simp [transvection, hhy, add_comm]
  exact ⟨he ▸ r.stable _ hh.2 y hy, he ▸ pencil_transvection hh hhE hp⟩

private theorem three_space_geometry
    {x y z : V} {f g u : Module.Dual (ZMod 2) V}
    (hfx : f x = 0) (hfy : f y = 1) (hfz : f z = 0)
    (hgx : g x = 1) (hgy : g y = 0) (hgz : g z = 0)
    (hux : u x = 0) (huy : u y = 0) (huz : u z = 1)
    {E : Submodule (ZMod 2) (Module.Dual (ZMod 2) V)}
    (hfE : f ∈ E) (hgE : g ∈ E) (huE : u ∈ E) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {x, y, z}) = 3 ∧
      Disjoint (Submodule.span (ZMod 2) {x, y, z}) E.dualCoannihilator := by
  have hlin : LinearIndependent (ZMod 2) ![x, y, z] := by
    apply LinearIndependent.of_pairwise_dual_eq_zero_one _ ![g, f, u]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · intro i
      fin_cases i <;> simp_all
  have hr : Set.range ![x, y, z] = ({x, y, z} : Set V) := by
    simp only [Matrix.range_cons, Matrix.range_empty, Set.union_empty, Set.singleton_union]
  constructor
  · rw [← hr, finrank_span_eq_card hlin, Fintype.card_fin]
  · apply Submodule.disjoint_def.mpr
    intro w hw hwE
    obtain ⟨a, b, c, rfl⟩ := Submodule.mem_span_triple.mp hw
    have ha := (Submodule.mem_dualCoannihilator _).mp hwE g hgE
    have hb := (Submodule.mem_dualCoannihilator _).mp hwE f hfE
    have hc := (Submodule.mem_dualCoannihilator _).mp hwE u huE
    simp only [map_add, map_smul, hgx, hgy, hgz, hfx, hfy, hfz, hux, huy, huz,
      smul_eq_mul, mul_one, mul_zero, add_zero, zero_add] at ha hb hc
    simp [ha, hb, hc]

/-- A spanning binary root orbit with root groups of order greater than two
contains a three-dimensional root-form seed. No irreducibility is required. -/
theorem RootGeneratedOrbit.exists_rootFormSeed [Finite G] (r : RootGeneratedOrbit G Δ) :
    ∃ W E, IsRootFormSeed G Δ W E := by
  obtain ⟨x, hx, y, hy, f, hf, g, hg, hfy, hgx⟩ := r.exists_moving_forms
  obtain ⟨u, hu, hu0, huy⟩ := exists_kernel_form r hx y
  obtain ⟨z, hz, huz⟩ := exists_detected_center r hu0
  let E := rootForms G x ⊔ rootForms G y
  have hxE : rootForms G x ≤ E := le_sup_left
  have hyE : rootForms G y ≤ E := le_sup_right
  obtain ⟨F, hFx, H, hHy, hFz, hHz, hFy, hFz0, hHx, hHz0, hpz⟩ :=
    third_pencil r hx hy hz hf hfy hg hgx hu huy huz
  have hpx : rootForms G x = E ⊓ (centerLine x).dualAnnihilator := pair_pencil hf hfy
  have hpy : rootForms G y = E ⊓ (centerLine y).dualAnnihilator := by
    simpa only [sup_comm] using pair_pencil hg hgx
  have hu' : u ∈ rootForms G y := transfer_form hu huy hg hgx
  have hxy := add_point_pencil r hy hFx (hxE hFx) hFy hpy
  have hxz := add_point_pencil r hz hu (hxE hu) huz hpz
  have hyz := add_point_pencil r hz hu' (hxE hu) huz hpz
  have hxyz := add_point_pencil r hyz.1 hu (hxE hu) (by simpa [huy] using huz) hyz.2
  have hgeometry := three_space_geometry hFx.1 hFy hFz0 hHx hHy.1 hHz0 hu.1 huy huz
    (hxE hFx) (hyE hHy) (hxE hu)
  refine ⟨Submodule.span (ZMod 2) {x, y, z}, E, ?_⟩
  refine ⟨by rw [hgeometry.1], ?_, hgeometry.2, ?_⟩
  · intro w hw hw0
    obtain ⟨a, b, c, rfl⟩ := Submodule.mem_span_triple.mp hw
    rcases binary_scalar a with rfl | rfl <;>
      rcases binary_scalar b with rfl | rfl <;>
      rcases binary_scalar c with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at hw0 ⊢
    · exact False.elim (hw0 rfl)
    · exact hz
    · exact hy
    · exact hyz.1
    · exact hx
    · exact hxz.1
    · exact hxy.1
    · simpa only [add_assoc] using hxyz.1
  · intro w hw hw0
    obtain ⟨a, b, c, rfl⟩ := Submodule.mem_span_triple.mp hw
    rcases binary_scalar a with rfl | rfl <;>
      rcases binary_scalar b with rfl | rfl <;>
      rcases binary_scalar c with rfl | rfl <;>
      simp only [zero_smul, one_smul, zero_add, add_zero] at hw0 ⊢
    · exact False.elim (hw0 rfl)
    · exact hpz
    · exact hpy
    · exact hyz.2
    · exact hpx
    · exact hxz.2
    · exact hxy.2
    · simpa only [add_assoc] using hxyz.2

end CFSG.Quasithin.ChapterG.Section03.Reduced
