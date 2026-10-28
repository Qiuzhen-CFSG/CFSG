module

public import Theory.Representation.BinaryTransvectionGroups.RootForms

/-!
# Exchange of binary root forms

Conjugating a transvection at x by a root at y which moves x transfers every
form vanishing at both centers to y.  Equal finite root orders then make
fixation symmetric.  These identities supply the local geometry for binary
root recognition without any assumption of complete reducibility.

Source motivation: Aschbacher--Smith G.3.1, printed pp.337--338; the proofs here
are direct rank-one linear calculations.
-/

@[expose] public section

open BinaryLinear
namespace BinaryTransvectionGroups
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem transvection_add_center (x y : V) (f : Module.Dual (ZMod 2) V)
    (hx : f x = 0) (hy : f y = 0) :
    transvection (x + y) f (by simp [hx, hy]) =
      transvection x f hx * transvection y f hy := by
  ext v
  simp [transvection, hy, smul_add]
  abel

theorem transvection_conj (g : GL V) (x : V) (f : Module.Dual (ZMod 2) V)
    (hx : f x = 0) :
    g * transvection x f hx * g⁻¹ = transvection (g x)
      (f.comp g.symm.toLinearMap) (by simpa using hx) := by
  ext v
  simp [transvection]

theorem form_apply_root {G : Subgroup (GL V)} {y : V}
    {f : Module.Dual (ZMod 2) V} (hf : f y = 0)
    {b : GL V} (hb : b ∈ rootGroup G y) (v : V) : f (b v) = f v := by
  have hd := (mem_centerLine_iff y (b v - v)).mp (hb.2.2 v)
  have he : f (b v - v) = 0 := by
    rcases hd with hd | hd <;> rw [hd] <;> simp [hf]
  exact sub_eq_zero.mp (by simpa using he)

theorem rootForm_transfer {G : Subgroup (GL V)} {x y : V}
    {f : Module.Dual (ZMod 2) V} (hf : f ∈ rootForms G x) (hfy : f y = 0)
    {b : GL V} (hb : b ∈ rootGroup G y) (hbx : b x = x + y) :
    f ∈ rootForms G y := by
  have hfc : f.comp b.symm.toLinearMap = f := by
    ext v
    exact form_apply_root hfy ((rootGroup G y).inv_mem hb) v
  have ht := G.mul_mem (G.mul_mem hb.1 hf.2) (G.inv_mem hb.1)
  rw [transvection_conj] at ht
  have ht' : transvection (x + y) f (by simp [hf.1, hfy]) ∈ G := by
    convert ht using 1
    simp only [hfc, hbx]
  rw [transvection_add_center x y f hf.1 hfy] at ht'
  exact (mem_rootForms hfy).mpr ((G.mul_mem_cancel_left hf.2).mp ht')

noncomputable def rootFormsEquiv (G : Subgroup (GL V)) {x : V} (hx : x ≠ 0) :
    rootForms G x ≃ rootGroup G x :=
  Equiv.ofBijective (fun f =>
    ⟨transvection x f.val f.property.1, transvection_mem_rootGroup_of_form f.property⟩) (by
      constructor
      · intro f g hfg
        apply Subtype.ext
        ext v
        apply smul_left_injective (ZMod 2) hx
        apply add_left_cancel (a := v)
        exact congrArg (fun a : rootGroup G x => a.val v) hfg
      · intro a
        obtain ⟨ha, f, hf, he⟩ := (mem_rootGroup_iff hx).mp a.property
        exact ⟨⟨f, (mem_rootForms hf).mpr (he ▸ ha)⟩, Subtype.ext he.symm⟩)

theorem rootForms_card_eq (G : Subgroup (GL V)) {x : V} (hx : x ≠ 0) :
    Nat.card (rootForms G x) = Nat.card (rootGroup G x) :=
  Nat.card_congr (rootFormsEquiv G hx)

theorem rootForms_fixation_symm {G : Subgroup (GL V)} [Finite G] {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hc : Nat.card (rootGroup G x) = Nat.card (rootGroup G y))
    (hfix : ∀ f ∈ rootForms G x, f y = 0) :
    ∀ g ∈ rootForms G y, g x = 0 := by
  intro g hg
  by_contra hng
  have hgx : g x = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hng
  let b := transvection y g hg.1
  have hb : b ∈ rootGroup G y := transvection_mem_rootGroup_of_form hg
  have hbx : b x = x + y := by simp [b, transvection, hgx]
  have hle : rootForms G x ≤ rootForms G y :=
    fun f hf => rootForm_transfer hf (hfix f hf) hb hbx
  let : Finite (rootForms G y) :=
    Finite.of_injective (rootFormsEquiv G hy) (rootFormsEquiv G hy).injective
  have hsur := (Submodule.inclusion_injective hle).bijective_of_nat_card_le (by
    rw [rootForms_card_eq G hy, rootForms_card_eq G hx, hc])
  obtain ⟨f, hf⟩ := hsur.2 ⟨g, hg⟩
  have hfg : f.val = g := congrArg Subtype.val hf
  exact hng (hfg ▸ f.property.1)

theorem rootForms_exchange {G : Subgroup (GL V)} {x y : V} {a b : GL V}
    (ha : a ∈ rootGroup G x) (hb : b ∈ rootGroup G y)
    (hay : a y = y + x) (hbx : b x = x + y) :
    rootForms G x ⊓ (centerLine y).dualAnnihilator =
      rootForms G y ⊓ (centerLine x).dualAnnihilator := by
  apply le_antisymm
  · intro f hf
    exact ⟨rootForm_transfer hf.1 ((mem_line_annihilator y f).mp hf.2) hb hbx,
      rootForms_le_annihilator G x hf.1⟩
  · intro f hf
    exact ⟨rootForm_transfer hf.1 ((mem_line_annihilator x f).mp hf.2) ha hay,
      rootForms_le_annihilator G y hf.1⟩

end BinaryTransvectionGroups
