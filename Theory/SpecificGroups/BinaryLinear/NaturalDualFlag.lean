module

public import Theory.SpecificGroups.BinaryLinear.NestedRadicals
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Fixed vectors for the natural-plus-dual action of a binary flag stabilizer

Let A be a line contained in a hyperplane H. Every finite invariant subspace
of even order in V ⊕ V* has a nonzero vector fixed by the stabilizer of A < H.
The radicals at A and H generate a two-group inside that stabilizer. Its
fixed vectors have natural component in A and dual component in the
annihilator of H: rank-one transvections detect both conditions. The full
stabilizer fixes these two binary lines pointwise.

The argument uses arbitrary subspaces throughout, so it applies to every
flag without choosing or presupposing a conjugating matrix. This is the
parabolic calculation excluding the natural-plus-dual alternative in
Aschbacher–Smith, combined manuscript (1 March 2004), the first paragraph
of the proof of 15.3.32, printed p.1132.
-/

public section

namespace BinaryLinear.NaturalDualFlag
open BinaryLinear
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

/-- The natural action and its contragredient in the same linear coordinates. -/
def action : GL V →* GL (V × Module.Dual (ZMod 2) V) where
  toFun g := g.prodCongr g.symm.dualMap
  map_one' := by ext <;> rfl
  map_mul' g h := by ext <;> rfl

@[simp] theorem action_fst (g : GL V) (v : V × Module.Dual (ZMod 2) V) :
    (action g v).1 = g v.1 := by unfold action; rfl

@[simp] theorem action_snd (g : GL V) (v : V × Module.Dual (ZMod 2) V) (x : V) :
    (action g v).2 x = v.2 (g.symm x) := by unfold action; rfl

/-- A binary line stabilizer fixes the line pointwise. -/
private theorem fixes_line {A : Submodule (ZMod 2) V} (hA : Module.finrank (ZMod 2) A = 1)
    {g : GL V} (hg : g ∈ parabolic A) {v : V} (hv : v ∈ A) : g v = v := by
  by_cases hv0 : v = 0
  · simp [hv0]
  have hspan := eq_span_singleton_of_mem_of_finrank_eq_one hA hv hv0
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hspan ▸ (hg v).mpr hv)
  have hc0 : c ≠ 0 := by
    intro hz
    exact hv0 (g.map_eq_zero_iff.mp (by simpa [hz] using hc.symm))
  have hc1 : c = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) c hc0
  simpa [hc1] using hc.symm

/-- The contragredient of a subspace stabilizer preserves its annihilator. -/
private theorem dual_parabolic {H : Submodule (ZMod 2) V} {g : GL V}
    (hg : g ∈ parabolic H) : g.symm.dualMap ∈ parabolic H.dualAnnihilator := by
  intro f
  simp only [Submodule.mem_dualAnnihilator, LinearEquiv.dualMap_apply]
  constructor
  · intro hf x hx
    simpa using hf (g x) ((hg x).mpr hx)
  · intro hf x hx
    exact hf (g.symm x) (((parabolic H).inv_mem hg x).mpr hx)

/-- Rank-one transvections force a radical-fixed covector to vanish on its subspace. -/
private theorem annihilates_of_fixed_radical {H : Submodule (ZMod 2) V} (hH : H ≠ ⊤)
    {f : Module.Dual (ZMod 2) V}
    (hf : ∀ g ∈ radical H, g.symm.dualMap f = f) : f ∈ H.dualAnnihilator := by
  obtain ⟨x, _, hx⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hH)
  obtain ⟨q, hqx, hq⟩ := H.exists_le_ker_of_notMem hx
  have hq1 : q x = 1 := (by decide : ∀ c : ZMod 2, c ≠ 0 → c = 1) _ hqx
  rw [Submodule.mem_dualAnnihilator]
  intro w hw
  have he := LinearMap.congr_fun (hf (transvection w q (hq hw)) (transvection_mem hw hq)) x
  change f (x + q x • w) = f x at he
  simpa [hq1] using he

/-- The two radicals of a nested flag form a two-group inside its stabilizer. -/
private theorem radical_sup_two {A H : Submodule (ZMod 2) V} (hAH : A ≤ H) :
    IsPGroup 2 (radical A ⊔ radical H : Subgroup (GL V)) :=
  (radical_two A).to_sup_of_normal_left' (radical_two H)
    ((radical_le_smaller_parabolic hAH).trans (parabolic_le_normalizer A))

private theorem radical_sup_le {A H : Submodule (ZMod 2) V} (hAH : A ≤ H) :
    radical A ⊔ radical H ≤ parabolic A ⊓ parabolic H :=
  sup_le (le_inf (radical_le_parabolic A) (radical_le_nested_parabolic hAH))
    (le_inf (radical_le_smaller_parabolic hAH) (radical_le_parabolic H))

/-- Every even finite invariant subspace has a nonzero vector fixed by the flag stabilizer. -/
theorem exists_fixed [FiniteDimensional (ZMod 2) V]
    {A H : Submodule (ZMod 2) V} (hAH : A ≤ H)
    (hA : Module.finrank (ZMod 2) A = 1)
    (hH : Module.finrank (ZMod 2) H + 1 = Module.finrank (ZMod 2) V)
    (W : Submodule (ZMod 2) (V × Module.Dual (ZMod 2) V)) [Finite W]
    (hW : 2 ∣ Nat.card W)
    (hstable : ∀ g ∈ parabolic A ⊓ parabolic H, ∀ w ∈ W, action g w ∈ W) :
    ∃ w ∈ W, w ≠ 0 ∧ ∀ g ∈ parabolic A ⊓ parabolic H, action g w = w := by
  let Q : Subgroup (GL V) := radical A ⊔ radical H
  have hQ := radical_sup_two hAH
  let : MulAction Q W := {
    smul g w := ⟨action g.val w.val, hstable g.val (radical_sup_le hAH g.property) w.val w.property⟩
    one_smul w := Subtype.ext (by change action 1 w.val = w.val; simp)
    mul_smul g h w := Subtype.ext (by
      change action (g.val * h.val) w.val = action g.val (action h.val w.val)
      rw [map_mul, LinearEquiv.mul_apply]) }
  have hz : (0 : W) ∈ MulAction.fixedPoints Q W := by
    rw [MulAction.mem_fixedPoints]
    intro q
    apply Subtype.ext
    exact (action q.val).map_zero
  obtain ⟨w, hw, hw0⟩ := hQ.exists_fixed_point_of_prime_dvd_card_of_fixed_point W hW hz
  have hfix (g : GL V) (hg : g ∈ Q) : action g w.val = w.val :=
    congrArg Subtype.val ((MulAction.mem_fixedPoints.mp hw) ⟨g, hg⟩)
  have hA0 : A ≠ ⊥ := by
    intro he
    have hh := hA
    rw [he, finrank_bot] at hh
    omega
  have hHt : H ≠ ⊤ := by
    intro he
    have hh := hH
    rw [he, finrank_top] at hh
    omega
  have hwA : w.val.1 ∈ A := (mem_iff_fixed_radical hA0 _).mpr (by
    intro g hg
    exact congrArg Prod.fst (hfix g ((show radical A ≤ Q from le_sup_left) hg)))
  have hwH : w.val.2 ∈ H.dualAnnihilator := annihilates_of_fixed_radical hHt (by
    intro g hg
    exact congrArg Prod.snd (hfix g ((show radical H ≤ Q from le_sup_right) hg)))
  have hdH : Module.finrank (ZMod 2) H.dualAnnihilator = 1 := by
    have hd := Subspace.finrank_add_finrank_dualAnnihilator_eq H
    omega
  refine ⟨w.val, w.property, ?_, ?_⟩
  · intro he
    exact hw0 (Subtype.ext he.symm)
  · intro g hg
    apply Prod.ext
    · exact fixes_line hA hg.1 hwA
    · exact fixes_line hdH (dual_parabolic hg.2) hwH

end BinaryLinear.NaturalDualFlag
