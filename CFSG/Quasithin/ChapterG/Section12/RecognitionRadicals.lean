module
public import CFSG.Quasithin.ChapterG.Section12.Conjugation
public import Theory.SpecificGroups.PSp4Three.Generation
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.Abel

/-!
# The point-radical branch of G.12 recognition

The literal point radical acts freely outside its perpendicular hyperplane.
Full transvections on that hyperplane force every nonzero invariant subspace
to contain its center. Two nonorthogonal good centers therefore generate an
irreducible action. If the hyperplane restriction has a nontrivial kernel,
that kernel contains the symplectic transvection. The radical is then
transitive outside the hyperplane, irreducibility gives all nonzero centers,
and symplectic transvection generation identifies the whole form stabilizer.

These are the geometric and full-symplectic branches of G.12.1, specifically
G.12.2(1), G.12.3 and G.12.5. The faithful-radical recognition cases remain
independent obligations; this module does not assert the full classification.
Source: Aschbacher--Smith, combined manuscript (1 March 2004), pp.370--371.
-/

public section
open Subgroup Module
namespace CFSG.Quasithin.ChapterG.Section12
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
variable {D : Subgroup (V ≃ₗ[ZMod 2] V)} {B : LinearMap.BilinForm (ZMod 2) V}
  (hB : B.IsAlt) (hnd : B.Nondegenerate)

private theorem bit_one {a : ZMod 2} (ha : a ≠ 0) : a = 1 := by
  exact (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) a |>.resolve_left ha

omit [FiniteDimensional (ZMod 2) V] in
include hB in
private theorem swap (x y : V) : B x y = B y x := by
  rw [← hB.neg_eq x y]
  exact (show ∀ a : ZMod 2, -a = a from by decide) (B x y) |>.symm

include hB hnd in
private theorem perp_perp {v z : V}
    (hz : ∀ w, B v w = 0 → B z w = 0) :
    z ∈ Submodule.span (ZMod 2) {v} := by
  rw [← B.orthogonal_orthogonal hnd hB.isRefl (Submodule.span (ZMod 2) {v}),
    LinearMap.BilinForm.orthogonal_span_singleton_eq_toLin_ker]
  intro w hw
  exact (swap hB w z).trans (hz w hw)

omit [FiniteDimensional (ZMod 2) V] in
private theorem span_bit {v z : V} (hz : z ∈ Submodule.span (ZMod 2) {v}) :
    z = 0 ∨ z = v := by
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hz
  rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 from by decide) c with rfl | rfl
  · exact Or.inl (zero_smul _ _)
  · exact Or.inr (one_smul _ _)

omit [FiniteDimensional (ZMod 2) V] in
include hnd in
private theorem outside_exists {v : V} (hv : v ≠ 0) : ∃ x, B v x = 1 := by
  have hn : B v ≠ 0 := fun hz => hv (hnd.1 v (fun x => LinearMap.congr_fun hz x))
  obtain ⟨x,hx⟩ := Module.Dual.range_eq_top_of_ne_zero hn ▸
    (show (1 : ZMod 2) ∈ (⊤ : Submodule (ZMod 2) (ZMod 2)) from trivial)
  exact ⟨x,hx⟩

private def tv (v : V) : V ≃ₗ[ZMod 2] V :=
  LinearEquiv.transvection (hB v)

omit [FiniteDimensional (ZMod 2) V] in
private theorem tv_apply (v x : V) : tv hB v x = x + B v x • v := rfl

omit [FiniteDimensional (ZMod 2) V] in
private theorem tv_preserves (v : V) : tv hB v ∈ formStabilizer B := by
  intro x y
  simp only [tv_apply, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hB v, mul_zero, add_zero]
  rw [swap hB x v]
  ring_nf
  rw [show (2 : ZMod 2) = 0 from by decide, mul_zero, add_zero]

include hnd in
/-- An isometry which fixes a perpendicular hyperplane is the identity or its transvection. -/
private theorem hyperplane_fixer {v : V} (hv : v ≠ 0)
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ formStabilizer B)
    (hf : ∀ w, B v w = 0 → a w = w) : a = 1 ∨ a = tv hB v := by
  obtain ⟨x,hx⟩ := outside_exists hnd hv
  have hd : a x - x ∈ Submodule.span (ZMod 2) {v} := by
    apply perp_perp hB hnd
    intro w hw
    have he := ha x w
    rw [hf w hw] at he
    simpa only [map_sub, LinearMap.sub_apply, sub_eq_zero] using he
  have he (y : V) : a y = y + B v y • (a x - x) := by
    have hy : B v (y - B v y • x) = 0 := by simp [hx]
    have hh := hf _ hy
    rw [map_sub, map_smul] at hh
    calc
      a y = (y - B v y • x) + B v y • a x := sub_eq_iff_eq_add.mp hh
      _ = _ := by module
  rcases span_bit hd with hd | hd
  · left
    ext y
    change a y = y
    rw [he, hd, smul_zero, add_zero]
  · right
    ext y
    rw [he,hd,tv_apply]

include hB hnd in
private theorem radical_semiregular (hD : D ≤ formStabilizer B) {v x : V}
    (hx : B v x = 1) {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ pointRadical D B v)
    (hax : a x = x) : a = 1 := by
  have hv : v ≠ 0 := by intro hv; simp [hv] at hx
  have hf (w : V) (hw : B v w = 0) : a w = w := by
    obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp (ha.2.2.2 w hw)
    have haw : a w = w + c • v := by rw [hc]; abel
    have he := hD ha.1 x w
    rw [hax, haw, map_add, map_smul, smul_eq_mul, swap hB x v, hx, mul_one] at he
    have hc0 : c = 0 := add_eq_left.mp he
    rw [haw, hc0, zero_smul, add_zero]
  rcases hyperplane_fixer hB hnd hv (hD ha.1) hf with h | h
  · exact h
  · rw [h,tv_apply,hx,one_smul] at hax
    exact (hv (add_eq_left.mp hax)).elim

include hB hnd in
private theorem good_nontrivial (_hD : D ≤ formStabilizer B) {v : V}
    (hv : GoodVector D B hB v) (hd : 4 ≤ finrank (ZMod 2) V) :
    ∃ a ∈ pointRadical D B v, a ≠ 1 := by
  by_contra! hn
  have hle : (B v).ker ≤ Submodule.span (ZMod 2) {v} := by
    intro w hw
    have hh := (hv.fixedSpace (⟨w,hw⟩ : (B v).ker)).mp (fun a => by
      change a.val w = w
      rw [hn a.val a.property]
      rfl)
    rcases span_bit hh with he | he
    · have : w = 0 := congrArg Subtype.val he
      rw [this]; exact Submodule.zero_mem _
    · have : w = v := congrArg Subtype.val he
      rw [this]; exact Submodule.mem_span_singleton_self _
  have hsmall := Submodule.finrank_mono hle
  rw [finrank_span_singleton hv.nonzero] at hsmall
  have hnB : B v ≠ 0 := fun he => hv.nonzero (hnd.1 v (fun w => LinearMap.congr_fun he w))
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hnB
  omega

include hB hnd in
private theorem good_mem_of_invariant (hD : D ≤ formStabilizer B) {v : V}
    (hv : GoodVector D B hB v) (hd : 4 ≤ finrank (ZMod 2) V)
    (U : Submodule (ZMod 2) V) (hne : U ≠ ⊥)
    (hU : ∀ a ∈ pointRadical D B v, ∀ w ∈ U, a w ∈ U) : v ∈ U := by
  by_contra hvU
  have hi (w : V) (hw : w ∈ U) (hp : B v w = 0) : w = 0 := by
    have hf : ∀ a : pointRadical D B v, a.val w = w := by
      intro a
      have hm := hv.displacement a ⟨w,hp⟩
      rcases span_bit hm with h | h
      · exact sub_eq_zero.mp h
      · apply (hvU ?_).elim
        have hm := U.sub_mem (hU a.val a.property w hw) hw
        change a.val w - w = v at h
        rwa [h] at hm
    have hh := (hv.fixedSpace ⟨w,hp⟩).mp hf
    rcases span_bit hh with h | h
    · exact congrArg Subtype.val h
    · apply (hvU ?_).elim
      have he : w = v := congrArg Subtype.val h
      rwa [he] at hw
  obtain ⟨x,hx,hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hxB : B v x = 1 := bit_one (fun hz => hx0 (hi x hx hz))
  obtain ⟨a,ha,ha1⟩ := good_nontrivial hB hnd hD hv hd
  apply ha1
  apply radical_semiregular hB hnd hD hxB ha
  apply sub_eq_zero.mp
  apply hi (a x-x) (U.sub_mem (hU a ha x hx) hx)
  have he := hD ha.1 v x
  rw [ha.2.1] at he
  simpa only [map_sub, sub_eq_zero] using he

/-- The two source radicals already act irreducibly. -/
theorem ClassificationHypotheses.radicals_irreducible {u v : V}
    (h : ClassificationHypotheses D B u v) :
    Irreducible (pointRadical D B u ⊔ pointRadical D B v) := by
  intro U hU
  by_cases hzero : U = ⊥
  · exact Or.inl hzero
  right
  have huU := good_mem_of_invariant h.alternating h.nondegenerate h.preserves
    h.good_u h.dimension U hzero (fun a ha => hU a ((show pointRadical D B u ≤ pointRadical D B u ⊔ pointRadical D B v from le_sup_left) ha))
  have hvU := good_mem_of_invariant h.alternating h.nondegenerate h.preserves
    h.good_v h.dimension U hzero (fun a ha => hU a ((show pointRadical D B v ≤ pointRadical D B u ⊔ pointRadical D B v from le_sup_right) ha))
  by_contra htop
  have hperp : B.orthogonal U ≠ ⊥ := by
    intro he
    have hh := B.orthogonal_orthogonal h.nondegenerate h.alternating.isRefl U
    rw [he, LinearMap.BilinForm.orthogonal_bot] at hh
    exact htop hh.symm
  have hstable : ∀ a ∈ pointRadical D B u ⊔ pointRadical D B v,
      ∀ w ∈ B.orthogonal U, a w ∈ B.orthogonal U := by
    intro a ha w hw z hz
    have haD : a ∈ D := (show pointRadical D B u ⊔ pointRadical D B v ≤ D from sup_le inf_le_left inf_le_left) ha
    have hzi := hU a⁻¹ (Subgroup.inv_mem _ ha) z hz
    have hp := h.preserves haD (a.symm z) w
    rw [a.apply_symm_apply] at hp
    exact hp.trans (hw _ hzi)
  have huP := good_mem_of_invariant h.alternating h.nondegenerate h.preserves
    h.good_u h.dimension (B.orthogonal U) hperp
    (fun a ha => hstable a ((show pointRadical D B u ≤ pointRadical D B u ⊔ pointRadical D B v from le_sup_left) ha))
  exact h.pairing (h.alternating.eq_iff.mp (huP v hvU))

theorem ClassificationHypotheses.irreducible {u v : V}
    (h : ClassificationHypotheses D B u v) : Irreducible D := by
  intro U hU
  exact h.radicals_irreducible U (fun a ha => hU a ((show pointRadical D B u ⊔ pointRadical D B v ≤ D from sup_le inf_le_left inf_le_left) ha))

include hB hnd in
private theorem radical_transitive (hD : D ≤ formStabilizer B) {v : V}
    (hv : GoodVector D B hB v) (ht : tv hB v ∈ D) {x y : V}
    (hx : B v x = 1) (hy : B v y = 1) :
    ∃ a ∈ pointRadical D B v, a x = y := by
  let φ : Module.Dual (ZMod 2) (B v).ker := (B (y-x)).comp (B v).ker.subtype
  have hφ : φ ⟨v,hB v⟩ = 0 := by
    change B (y-x) v = 0
    rw [swap hB, map_sub, hx, hy, sub_self]
  obtain ⟨a,ha⟩ := hv.full φ hφ
  have hav : a.val v = v := a.property.2.1
  have havx : B v (a.val x) = 1 := by
    have hh := hD a.property.1 v x
    rw [hav] at hh
    exact hh.trans hx
  have hd : a.val x - y ∈ Submodule.span (ZMod 2) {v} := by
    apply perp_perp hB hnd
    intro w hw
    have hh := hD a.property.1 x w
    have haw : a.val w = w + B (y-x) w • v := ha ⟨w,hw⟩
    rw [haw] at hh
    change B (a.val x) (w + B (y-x) w • v) = B x w at hh
    rw [map_add, map_smul, smul_eq_mul, swap hB (a.val x) v, havx,
      mul_one, map_sub, LinearMap.sub_apply] at hh
    rw [map_sub, LinearMap.sub_apply]
    have ht : ∀ a : ZMod 2, a + a = 0 := by decide
    linear_combination hh - ht (B y w) + ht (B x w)
  have htQ : tv hB v ∈ pointRadical D B v := by
    apply (mem_pointRadical_iff hD).mpr
    refine ⟨ht, ?_, ?_⟩
    · rw [tv_apply, hB v, zero_smul, add_zero]
    · intro w hw
      rw [tv_apply,hw,zero_smul,add_zero,sub_self]
      exact Submodule.zero_mem _
  rcases span_bit hd with hd | hd
  · exact ⟨a,a.property,sub_eq_zero.mp hd⟩
  · refine ⟨tv hB v * a.val, (pointRadical D B v).mul_mem htQ a.property, ?_⟩
    change tv hB v (a.val x) = y
    rw [tv_apply,havx,one_smul]
    have hadd : ∀ z : V, z+z=0 := by
      intro z
      simpa only [two_smul,zero_smul] using congrArg (fun c : ZMod 2 => c • z)
        (show (2 : ZMod 2) = 0 from by decide)
    have he : a.val x = v+y := sub_eq_iff_eq_add.mp hd
    rw [he]
    have := hadd v
    abel_nf at this ⊢
    rw [this,zero_add]

omit [FiniteDimensional (ZMod 2) V] in
include hB in
private theorem tv_conjugate (hD : D ≤ formStabilizer B)
    {a : V ≃ₗ[ZMod 2] V} (ha : a ∈ D) (v : V) :
    a * tv hB v * a⁻¹ = tv hB (a v) := by
  ext x
  change a (tv hB v (a.symm x)) = tv hB (a v) x
  rw [tv_apply,tv_apply,map_add,map_smul,a.apply_symm_apply]
  congr 1
  congr 1
  have hh := hD ha v (a.symm x)
  rw [a.apply_symm_apply] at hh
  exact hh.symm

include hB hnd in
private theorem full_of_transvections
    (hD : D ≤ formStabilizer B) (ht : ∀ v : V, tv hB v ∈ D) :
    D = formStabilizer B := by
  open Matrix.PSp4Three in
  obtain ⟨n,hn⟩ := AlternatingForm.even_finrank B hB hnd
  obtain ⟨e⟩ := Matrix.PSp4Three.exists_isometry n B hB hnd (by omega)
  have ee (x : Matrix.PSp4Three.Vector n (ZMod 2)) : e (e.symm x) = x := e.toLinearEquiv.apply_symm_apply x
  have ee' (x : V) : e.symm (e x) = x := e.toLinearEquiv.symm_apply_apply x
  let j : Matrix.PSp4Three.Sp n (ZMod 2) →* (V ≃ₗ[ZMod 2] V) := {
    toFun a := (e.toLinearEquiv.trans (Matrix.PSp4Three.toLinear a)).trans e.symm.toLinearEquiv
    map_one' := by ext x; simpa using ee' x
    map_mul' := by
      intro a b
      ext x
      simp [Matrix.PSp4Three.toLinear_apply, ee] }
  have hj (a : Matrix.PSp4Three.Sp n (ZMod 2)) (x : V) :
      j a x = e.symm (a • e x) := rfl
  have htrans (w : Matrix.PSp4Three.Vector n (ZMod 2)) (c : ZMod 2) :
      j (Matrix.PSp4Three.transvection w c) ∈ D := by
    rcases (show ∀ c : ZMod 2, c=0 ∨ c=1 from by decide) c with rfl | rfl
    · rw [Matrix.PSp4Three.transvection_zero, map_one]; exact D.one_mem
    · have he : j (Matrix.PSp4Three.transvection w 1) = tv hB (e.symm w) := by
        ext x
        rw [hj, Matrix.PSp4Three.transvection_apply,one_mul,map_add,map_smul,tv_apply]
        simp only [ee']
        congr 1
        congr 1
        have he := e.map_app (e.symm w) x
        rw [ee] at he
        exact he.trans (swap hB x (e.symm w))
      rw [he]; exact ht _
  have hall : ∀ a, j a ∈ D := by
    have hle : Matrix.PSp4Three.transvectionGroup n (ZMod 2) ≤ D.comap j := by
      apply (Subgroup.closure_le _).mpr
      rintro a ⟨w,c,rfl⟩
      exact htrans w c
    rw [Matrix.PSp4Three.transvectionGroup_eq_top] at hle
    exact fun a => hle (Subgroup.mem_top a)
  apply le_antisymm hD
  intro a ha
  let k := (e.symm.toLinearEquiv.trans a).trans e.toLinearEquiv
  have hk (x y : Matrix.PSp4Three.Vector n (ZMod 2)) :
      Matrix.PSp4Three.form (k x) (k y) = Matrix.PSp4Three.form x y := by
    change Matrix.PSp4Three.form (e (a (e.symm x))) (e (a (e.symm y))) = _
    rw [e.map_app,ha,← e.map_app]
    simp only [ee]
  have he : j (Matrix.PSp4Three.ofLinear k hk) = a := by
    ext x
    rw [hj,Matrix.PSp4Three.ofLinear_apply]
    simp [k,ee']
  rw [← he]
  exact hall _

/-- The nonfaithful point-radical branch of G.12.1 is the full symplectic group. -/
theorem ClassificationHypotheses.eq_formStabilizer_of_radical_kernel {u v : V}
    (h : ClassificationHypotheses D B u v)
    (hk : ∃ a ∈ pointRadical D B v, a ≠ 1 ∧
      ∀ w, B v w = 0 → a w = w) : D = formStabilizer B := by
  obtain ⟨a,ha,ha1,haf⟩ := hk
  have ht : tv h.alternating v ∈ D := by
    rcases hyperplane_fixer h.alternating h.nondegenerate h.good_v.nonzero
      (h.preserves ha.1) haf with he | he
    · exact (ha1 he).elim
    · exact he ▸ ha.1
  have hW : (B v).ker ≠ ⊤ := by
    intro he
    have hn := h.nondegenerate.1 v (fun x => he.ge (Submodule.mem_top : x ∈ (⊤ : Submodule (ZMod 2) V)))
    exact h.good_v.nonzero hn
  obtain ⟨b,hb,hbv⟩ := h.irreducible.exists_outside hW h.good_v.nonzero
  have hb1 : B v (b v) = 1 := bit_one hbv
  have hout (x : V) (hx : B v x = 1) : ∃ c ∈ D, c v = x := by
    obtain ⟨c,hc,he⟩ := radical_transitive h.alternating h.nondegenerate h.preserves h.good_v ht hb1 hx
    exact ⟨c*b,D.mul_mem hc.1 hb,he⟩
  have horbit (x : V) (hx : x ≠ 0) : ∃ c ∈ D, c v = x := by
    obtain ⟨c,hc,hcx⟩ := h.irreducible.exists_outside hW hx
    obtain ⟨b,hb,he⟩ := hout (c x) (bit_one hcx)
    refine ⟨c⁻¹*b,D.mul_mem (D.inv_mem hc) hb,?_⟩
    change c.symm (b v) = x
    rw [he,c.symm_apply_apply]
  apply full_of_transvections h.alternating h.nondegenerate h.preserves
  intro x
  by_cases hx : x = 0
  · subst x
    have he : tv h.alternating (0 : V) = 1 := by ext z; simp [tv_apply]
    rw [he]; exact D.one_mem
  · obtain ⟨c,hc,rfl⟩ := horbit x hx
    rw [← tv_conjugate h.alternating h.preserves hc]
    exact D.mul_mem (D.mul_mem hc ht) (D.inv_mem hc)

end CFSG.Quasithin.ChapterG.Section12
