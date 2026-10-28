module

public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.TwoBlocks
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Theory.GroupTheory.Commutator.ConjugateGeneration

/-!
# The two normalizer orbits in the three-by-two radical

For a three-space W inside a hyperplane H of a binary five-space, choose
x in H outside W and a functional f with kernel H. The ambient transvection
x f centralizes the factor R ∩ radical H. Its commutator with r in R is the
transvection (r x - x) f. A subgroup B of order sixteen with an order-two
intersection with this factor evaluates surjectively at x. Thus these
commutators give the entire factor, and B together with its conjugate
under this one simultaneous-normalizer element generates R.

For the second orbit, a nonidentity element of the hyperplane factor is a
transvection u f. The two-block action surjection lifts every automorphism
of W while fixing V/W, so its conjugates give every transvection w f.
A second ambient transvection supplies the other column of Hom(V/W,W).
All conjugators are elements of the actual normalizer in GL(V).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, B.4.9,
final paragraph on printed p.95. The argument proves both generation
statements without making an assumption about an upstairs representation.
-/

public section

open BinaryLinear Subgroup
namespace CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis.LinearGeneration
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

private theorem add_self (v : V) : v + v = 0 := by
  have h := add_smul (1 : ZMod 2) 1 v
  simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul] using h.symm

private theorem neg_eq (v : V) : -v = v := neg_eq_iff_add_eq_zero.mpr (add_self v)

private theorem functional_fixed {W : Submodule (ZMod 2) V}
    {f : V →ₗ[ZMod 2] ZMod 2} (hf : W ≤ f.ker)
    {r : BinaryLinear.GL V} (hr : r ∈ radical W) (v : V) : f (r v) = f v := by
  have h := hf (hr.2 v)
  change f (r v - v) = 0 at h
  simpa only [map_sub, sub_eq_zero] using h

private theorem conjugate_transvection {W : Submodule (ZMod 2) V}
    {f : V →ₗ[ZMod 2] ZMod 2} (hf : W ≤ f.ker) {x : V} (hx : f x = 0)
    {r : BinaryLinear.GL V} (hr : r ∈ radical W) :
    transvection x f hx * r * (transvection x f hx)⁻¹ =
      transvection (r x - x) f (hf (hr.2 x)) * r := by
  ext v
  change r (v + f v • x) + f (r (v + f v • x)) • x =
    r v + f (r v) • (r x - x)
  simp only [functional_fixed hf hr, map_add, map_smul, hx, smul_eq_mul,
    mul_zero, add_zero, sub_eq_add_neg, neg_eq, smul_add]
  abel

private theorem transvection_normalizes {W : Submodule (ZMod 2) V}
    (hW : W ≠ ⊥) {f : V →ₗ[ZMod 2] ZMod 2} (hf : W ≤ f.ker)
    {x : V} (hx : f x = 0) :
    transvection x f hx ∈ normalizer (radical W : Set (BinaryLinear.GL V)) := by
  rw [normalizer_radical hW]
  intro v
  constructor
  · intro hv
    have hf0 : f v = 0 := by
      have h := hf hv
      change f (v + f v • x) = 0 at h
      simpa [hx] using h
    simpa [transvection, hf0] using hv
  · intro hv
    simpa [transvection, show f v = 0 from hf hv] using hv

private theorem transvection_centralizes {W H : Submodule (ZMod 2) V}
    (hWH : W ≤ H) {f : V →ₗ[ZMod 2] ZMod 2} (hf : H ≤ f.ker)
    {x : V} (hx : x ∈ H) {r : BinaryLinear.GL V}
    (hr : r ∈ radical W) (hrH : r ∈ radical H) :
    transvection x f (hf hx) * r * (transvection x f (hf hx))⁻¹ = r := by
  rw [conjugate_transvection (hWH.trans hf) (hf hx) hr]
  ext v
  change r v + f (r v) • (r x - x) = r v
  simp [hrH.1 x hx]

private def evaluation (W : Submodule (ZMod 2) V) (x : V) :
    radical W →* Multiplicative W where
  toFun r := Multiplicative.ofAdd ⟨r.val x - x, r.property.2 x⟩
  map_one' := by apply Multiplicative.ext; apply Subtype.ext; simp
  map_mul' r s := by
    apply Multiplicative.ext
    apply Subtype.ext
    change r.val (s.val x) - x = (r.val x - x) + (s.val x - x)
    have h := r.property.1 (s.val x - x) (s.property.2 x)
    rw [map_sub] at h
    rw [sub_eq_iff_eq_add.mp h]
    abel

private theorem fixes_sup {W H : Submodule (ZMod 2) V} {x : V}
    (hH : H = W ⊔ Submodule.span (ZMod 2) {x}) (hWH : W ≤ H)
    {r : BinaryLinear.GL V} (hr : r ∈ radical W) : r ∈ radical H ↔ r x = x := by
  constructor
  · intro h
    apply h.1 x
    rw [hH]
    exact (show Submodule.span (ZMod 2) {x} ≤ W ⊔ Submodule.span (ZMod 2) {x} from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton x))
  · intro hx
    refine ⟨?_, fun v => hWH (hr.2 v)⟩
    have hker : H ≤ (r.toLinearMap - LinearMap.id).ker := by
      rw [hH]
      apply sup_le
      · intro w hw
        exact sub_eq_zero.mpr (hr.1 w hw)
      · apply Submodule.span_le.mpr
        intro v hv
        obtain rfl := Set.mem_singleton_iff.mp hv
        exact sub_eq_zero.mpr hx
    intro v hv
    exact sub_eq_zero.mp (hker hv)

private theorem hyperplane_shear {W H : Submodule (ZMod 2) V}
    {f : V →ₗ[ZMod 2] ZMod 2} (hf : H = f.ker) (hWH : W ≤ H)
    {z : V} (hz : f z = 1) {r : BinaryLinear.GL V}
    (hr : r ∈ radical W) (hrH : r ∈ radical H) :
    r = transvection (r z - z) f ((hWH.trans hf.le) (hr.2 z)) := by
  ext v
  change r v = v + f v • (r z - z)
  have hk : v - f v • z ∈ H := by
    rw [hf, LinearMap.mem_ker, map_sub, map_smul, hz, smul_eq_mul, mul_one, sub_self]
  have he := hrH.1 _ hk
  rw [map_sub, map_smul] at he
  rw [smul_sub]
  rw [sub_eq_iff_eq_add.mp he]
  abel

private theorem hyperplane_coordinates [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 5)
    {W H : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 3)
    (hH : Module.finrank (ZMod 2) H = 4) (hWH : W ≤ H) :
    ∃ x ∈ H, x ∉ W ∧ H = W ⊔ Submodule.span (ZMod 2) {x} ∧
      ∃ (f : V →ₗ[ZMod 2] ZMod 2) (z : V), H = f.ker ∧ f z = 1 := by
  have hex : ∃ x ∈ H, x ∉ W := by
    by_contra! he
    have hd := Submodule.finrank_mono he
    omega
  obtain ⟨x, hx, hxW⟩ := hex
  refine ⟨x, hx, hxW, ?_, ?_⟩
  · symm
    apply Submodule.eq_of_le_of_finrank_eq
      (sup_le hWH (Submodule.span_le.mpr (by simpa)))
    rw [Submodule.finrank_sup_span_singleton hxW, hW, hH]
  · have hHt : H ≠ ⊤ := by
      intro he
      rw [he, finrank_top, hV] at hH
      omega
    have hexz : ∃ z, z ∉ H := by
      by_contra! hz
      exact hHt (top_unique (fun v _ => hz v))
    obtain ⟨z, hz⟩ := hexz
    obtain ⟨f, hfz, hHf⟩ := H.exists_le_ker_of_notMem hz
    have hfz1 : f z = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hfz
    refine ⟨f, z, ?_, hfz1⟩
    apply Submodule.eq_of_le_of_finrank_eq hHf
    have hsurj : Function.Surjective f := fun a => ⟨a • z, by simp [hfz1]⟩
    have hd := f.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, hV] at hd
    omega

private theorem evaluation_surjective [FiniteDimensional (ZMod 2) V]
    {W H : Submodule (ZMod 2) V} {x : V}
    (hH : H = W ⊔ Submodule.span (ZMod 2) {x}) (hWH : W ≤ H)
    (hW : Module.finrank (ZMod 2) W = 3)
    (B : Subgroup (BinaryLinear.GL V)) (hBR : B ≤ radical W)
    (hB : Nat.card B = 16) (hC : Nat.card (B ⊓ radical H : Subgroup _) = 2) :
    Function.Surjective ((evaluation W x).comp (Subgroup.inclusion hBR)) := by
  let : Finite V := Module.finite_of_finite (ZMod 2)
  let : Finite (BinaryLinear.GL V) := Finite.of_injective
    (fun g : BinaryLinear.GL V => (g : V → V)) DFunLike.coe_injective
  let ev := (evaluation W x).comp (Subgroup.inclusion hBR)
  have hk : ev.ker = (B ⊓ radical H).subgroupOf B := by
    ext b
    change ev b = 1 ↔ b.val ∈ B ⊓ radical H
    constructor
    · intro he
      have hh := congrArg (fun y : Multiplicative W => (y.toAdd : V)) he
      change b.val x - x = 0 at hh
      exact ⟨b.property, (fixes_sup hH hWH (hBR b.property)).mpr (sub_eq_zero.mp hh)⟩
    · intro he
      apply Multiplicative.ext
      apply Subtype.ext
      change b.val x - x = 0
      exact sub_eq_zero.mpr ((fixes_sup hH hWH (hBR b.property)).mp he.2)
  have hkcard : Nat.card ev.ker = 2 := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show B ⊓ radical H ≤ B from inf_le_left)).toEquiv]
    exact hC
  apply ev.surjective_of_card_ker_le_div
  have hWcard : Nat.card (Multiplicative W) = 8 := by
    change Nat.card W = 8
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), hW, Nat.card_zmod]
    norm_num
  rw [hkcard, hB, hWcard]

/-- One quotient transvection suffices for the simultaneous-normalizer generation. -/
theorem first_generation [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 5)
    {W H : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 3)
    (hH : Module.finrank (ZMod 2) H = 4) (hWH : W ≤ H)
    (B : Subgroup (BinaryLinear.GL V)) (hBR : B ≤ radical W)
    (hB : Nat.card B = 16) (hC : Nat.card (B ⊓ radical H : Subgroup _) = 2) :
    radical W ≤ ⨆ n : (normalizer (radical W : Set (BinaryLinear.GL V)) ⊓
        normalizer (B ⊓ radical H : Set (BinaryLinear.GL V)) : Subgroup _),
      B.map (MulAut.conj n.val).toMonoidHom := by
  obtain ⟨x, hxH, hxW, hspan, f, z, hf, hfz⟩ := hyperplane_coordinates hV hW hH hWH
  let C := B ⊓ radical H
  let X := normalizer (radical W : Set (BinaryLinear.GL V)) ⊓ normalizer (C : Set _)
  let D := ⨆ n : X, B.map (MulAut.conj n.val).toMonoidHom
  have hBD : B ≤ D := by
    intro b hb
    exact (le_iSup (fun n : X => B.map (MulAut.conj n.val).toMonoidHom) 1)
      ⟨b, hb, by simp⟩
  have hW0 : W ≠ ⊥ := by intro he; rw [he, finrank_bot] at hW; omega
  let n := transvection x f (hf.le hxH)
  have hn : n ∈ X := by
    refine ⟨transvection_normalizes hW0 (hWH.trans hf.le) (hf.le hxH), ?_⟩
    apply Subgroup.centralizer_le_normalizer
    apply Subgroup.mem_centralizer_iff.mpr
    intro c hc
    exact (mul_inv_eq_iff_eq_mul.mp
      (transvection_centralizes hWH hf.le hxH (hBR hc.1) hc.2)).symm
  have hconj {b : BinaryLinear.GL V} (hb : b ∈ B) : n * b * n⁻¹ ∈ D :=
    (le_iSup (fun n : X => B.map (MulAut.conj n.val).toMonoidHom) ⟨n, hn⟩)
      ⟨b, hb, rfl⟩
  have hsurj := evaluation_surjective hspan hWH hW B hBR hB hC
  have ht (w : W) : transvection (w : V) f ((hWH.trans hf.le) w.property) ∈ D := by
    obtain ⟨b, hb⟩ := hsurj (Multiplicative.ofAdd w)
    have he : b.val x - x = (w : V) := congrArg (fun y : Multiplicative W => (y.toAdd : V)) hb
    have hid := conjugate_transvection (hWH.trans hf.le) (hf.le hxH) (hBR b.property)
    have heq : transvection (w : V) f ((hWH.trans hf.le) w.property) =
        (n * b.val * n⁻¹) * b.val⁻¹ := by
      apply (eq_mul_inv_iff_mul_eq).mpr
      rw [hid]
      congr 1
      ext v
      change v + f v • (w : V) = v + f v • (b.val x - x)
      rw [he]
    rw [heq]
    exact D.mul_mem (hconj b.property) (D.inv_mem (hBD b.property))
  intro r hr
  change r ∈ D
  obtain ⟨b, hb⟩ := hsurj (evaluation W x ⟨r, hr⟩)
  have he : b.val x = r x := by
    have hh := congrArg (fun y : Multiplicative W => (y.toAdd : V)) hb
    change b.val x - x = r x - x at hh
    exact sub_left_injective hh
  let k := b.val⁻¹ * r
  have hkR : k ∈ radical W := (radical W).mul_mem ((radical W).inv_mem (hBR b.property)) hr
  have hkx : k x = x := by
    change b.val.symm (r x) = x
    rw [← he, b.val.symm_apply_apply]
  have hkH : k ∈ radical H := (fixes_sup hspan hWH hkR).mpr hkx
  have hkD : k ∈ D := by
    rw [hyperplane_shear hf hWH hfz hkR hkH]
    exact ht ⟨k z - z, hkR.2 z⟩
  have hh := D.mul_mem (hBD b.property) hkD
  simpa only [k, mul_inv_cancel_left] using hh

private theorem transitive_nonzero (x y : V) (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g : BinaryLinear.GL V, g x = y := by
  let ex := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x hx
  let ey := LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V y hy
  obtain ⟨g, hg⟩ := Submodule.exists_linearEquiv_restrict_eq (ex.symm.trans ey)
  refine ⟨g, ?_⟩
  have h := hg (ex 1)
  simp only [LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply] at h
  simpa [ex, ey] using h.symm

private theorem move_center {W : Submodule (ZMod 2) V}
    {f : V →ₗ[ZMod 2] ZMod 2} (hf : W ≤ f.ker)
    (u w : W) (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ g : parabolic W,
      g.val * transvection (u : V) f (hf u.property) * g.val⁻¹ =
        transvection (w : V) f (hf w.property) := by
  obtain ⟨a, ha⟩ := transitive_nonzero u w hu hw
  obtain ⟨g, hg⟩ := SmallParabolicLevi.blockAction_surjective W (a, 1)
  have hga : SmallParabolicLevi.subspaceAction W g = a := congrArg Prod.fst hg
  have hgb : SmallParabolicLevi.quotientAction W g = 1 := congrArg Prod.snd hg
  have hgu : g.val u = (w : V) := by
    have he := LinearEquiv.congr_fun hga u
    simpa only [SmallParabolicLevi.subspaceAction_apply, ha] using congrArg Subtype.val he
  have hfg (v : V) : f (g.val v) = f v := by
    have he := LinearEquiv.congr_fun hgb (W.mkQ v)
    change W.mkQ (g.val v) = W.mkQ v at he
    have hh := hf ((Submodule.Quotient.eq W).mp he)
    change f (g.val v - v) = 0 at hh
    simpa only [map_sub, sub_eq_zero] using hh
  refine ⟨g, ?_⟩
  ext v
  change g.val (g.val.symm v + f (g.val.symm v) • (u : V)) = v + f v • (w : V)
  have hi : f (g.val.symm v) = f v := by
    simpa only [g.val.apply_symm_apply] using (hfg (g.val.symm v)).symm
  rw [map_add, map_smul, g.val.apply_symm_apply, hi, hgu]

/-- Any nontrivial subgroup of the hyperplane factor generates the whole
radical under its full normalizer. -/
theorem second_generation [FiniteDimensional (ZMod 2) V]
    (hV : Module.finrank (ZMod 2) V = 5)
    {W H : Submodule (ZMod 2) V} (hW : Module.finrank (ZMod 2) W = 3)
    (hH : Module.finrank (ZMod 2) H = 4) (hWH : W ≤ H)
    (C : Subgroup (BinaryLinear.GL V)) (hCR : C ≤ radical W)
    (hCH : C ≤ radical H) (hC : C ≠ ⊥) :
    radical W ≤ ⨆ n : normalizer (radical W : Set (BinaryLinear.GL V)),
      C.map (MulAut.conj n.val).toMonoidHom := by
  obtain ⟨x, hxH, hxW, hspan, f, z, hf, hfz⟩ := hyperplane_coordinates hV hW hH hWH
  let N := normalizer (radical W : Set (BinaryLinear.GL V))
  let D := ⨆ n : N, C.map (MulAut.conj n.val).toMonoidHom
  have hCD : C ≤ D := by
    intro c hc
    exact (le_iSup (fun n : N => C.map (MulAut.conj n.val).toMonoidHom) 1)
      ⟨c, hc, by simp⟩
  have hND : N ≤ normalizer (D : Set _) := le_normalizer_iSup_conjugates C N
  have hW0 : W ≠ ⊥ := by intro he; rw [he, finrank_bot] at hW; omega
  have hex : ∃ c ∈ C, c ≠ 1 := by
    by_contra! he
    exact hC ((Subgroup.eq_bot_iff_forall C).mpr he)
  obtain ⟨c, hc, hc1⟩ := hex
  let u : W := ⟨c z - z, (hCR hc).2 z⟩
  have hcu : c = transvection (u : V) f ((hWH.trans hf.le) u.property) :=
    hyperplane_shear hf hWH hfz (hCR hc) (hCH hc)
  have hu : u ≠ 0 := by
    intro hu0
    apply hc1
    rw [hcu]
    ext v
    change v + f v • (u : V) = v
    simp [hu0]
  have ht (w : W) : transvection (w : V) f ((hWH.trans hf.le) w.property) ∈ D := by
    by_cases hw : w = 0
    · have he : transvection (w : V) f ((hWH.trans hf.le) w.property) = 1 := by
        ext v
        change v + f v • (w : V) = v
        simp [hw]
      rw [he]
      exact D.one_mem
    obtain ⟨g, hg⟩ := move_center (hWH.trans hf.le) u w hu hw
    have hgN : g.val ∈ N := parabolic_le_normalizer W g.property
    rw [← hg, ← hcu]
    exact (Subgroup.mem_normalizer_iff.mp (hND hgN) c).mp (hCD hc)
  obtain ⟨l, hlx, hlW⟩ := W.exists_le_ker_of_notMem hxW
  have hlx1 : l x = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hlx
  let k : V →ₗ[ZMod 2] ZMod 2 := l - l z • f
  have hkW : W ≤ k.ker := by
    intro w hw
    change l w - l z * f w = 0
    rw [show l w = 0 from hlW hw, show f w = 0 from (hWH.trans hf.le) hw,
      mul_zero, sub_self]
  have hkx : k x = 1 := by
    change l x - l z * f x = 1
    rw [hlx1, show f x = 0 from hf.le hxH, mul_zero, sub_zero]
  have hkz : k z = 0 := by
    change l z - l z * f z = 0
    rw [hfz, mul_one, sub_self]
  let n := transvection z k hkz
  have hn : n ∈ N := transvection_normalizes hW0 hkW hkz
  have ht' (w : W) : transvection (w : V) k (hkW w.property) ∈ D := by
    let t := transvection (w : V) f ((hWH.trans hf.le) w.property)
    have htR : t ∈ radical W := transvection_mem w.property (hWH.trans hf.le)
    have htz : t z - z = (w : V) := by
      change (z + f z • (w : V)) - z = (w : V)
      simp only [hfz, one_smul, add_sub_cancel_left]
    have he : transvection (w : V) k (hkW w.property) = (n * t * n⁻¹) * t⁻¹ := by
      apply eq_mul_inv_iff_mul_eq.mpr
      rw [conjugate_transvection hkW hkz htR]
      congr 1
      ext v
      change v + k v • (w : V) = v + k v • (t z - z)
      rw [htz]
    rw [he]
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp (hND hn) t).mp (ht w))
      (D.inv_mem (ht w))
  intro r hr
  change r ∈ D
  let w : W := ⟨r x - x, hr.2 x⟩
  let b := transvection (w : V) k (hkW w.property)
  have hbR : b ∈ radical W := transvection_mem w.property hkW
  have hbx : b x = r x := by
    change x + k x • (r x - x) = r x
    rw [hkx, one_smul]
    abel
  let s := b⁻¹ * r
  have hsR : s ∈ radical W := (radical W).mul_mem ((radical W).inv_mem hbR) hr
  have hsH : s ∈ radical H := by
    apply (fixes_sup hspan hWH hsR).mpr
    change b.symm (r x) = x
    rw [← hbx, b.symm_apply_apply]
  have hsD : s ∈ D := by
    rw [hyperplane_shear hf hWH hfz hsR hsH]
    exact ht ⟨s z - z, hsR.2 z⟩
  have hh : b * s ∈ D := D.mul_mem (ht' w) hsD
  simpa only [s, mul_inv_cancel_left] using hh

end CFSG.Quasithin.ChapterB.NaturalExtensions.DoubleNatural.BinaryFive.SameAxis.LinearGeneration
