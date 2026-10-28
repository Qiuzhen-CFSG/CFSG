module
public import Theory.Representation.BinaryPairedTransvections.Fixed
public import Theory.Representation.BinaryNaturalDual

/-!
# Summand exchange for paired binary transvections

A quadratic isometry of the natural-plus-dual space that exchanges the two
pure summands conjugates each full center-root group to the corresponding
full axis-root group. The marking `t (0,d) = (c,0)` fixes the precise axis
for conjugation by `t⁻¹`; an involutivity assumption is unnecessary.

Preservation of the evaluation quadratic form gives the pairing identity
between the two off-diagonal blocks. Applying that identity to the two
terms of a paired transvection proves the literal conjugation formula.
The final theorem applies it to the partner fixed-space calculation,
discharging its conjugacy premise from the actual geometric hypotheses.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
original Lemma 15.3.56(6--7), printed p. 1148 (combined manuscript,
1 March 2004).
-/

public section
namespace BinaryPairedTransvections
open BinaryLinear BinaryTransvectionGroups Subgroup
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

private theorem paired_transvection_apply (c : E) (φ : Module.Dual (ZMod 2) E)
    (hφ : φ c = 0) (u : PairedSpace E) :
    pairedAction (BinaryLinear.transvection c φ hφ) u =
      u + φ u.1 • (c,0) + u.2 c • (0,φ) := by
  apply Prod.ext
  · simp [pairedAction, BinaryLinear.transvection]
  · ext v
    change u.2 (v + φ v • c) = (u.2 + φ u.1 • (0 : Module.Dual (ZMod 2) E) + u.2 c • φ) v
    simp [mul_comm]

private theorem swap_pairing (t : BinaryLinear.GL (PairedSpace E))
    (hq : ∀ u, BinaryNaturalDual.quadratic (t u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (t (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (t (0,f)).2 = 0)
    (v : E) (f : Module.Dual (ZMod 2) E) :
    (t (v,0)).2 ((t (0,f)).1) = f v := by
  have hh := hq (v,f)
  have he : (v,f) = (v,0) + (0,f) := by ext <;> simp
  rw [he, map_add] at hh
  simpa only [BinaryNaturalDual.quadratic_apply, Prod.fst_add, Prod.snd_add,
    hE, hD, add_zero, zero_add] using hh

private theorem natural_preimage (t : BinaryLinear.GL (PairedSpace E))
    (hE : ∀ v : E, (t (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (t (0,f)).2 = 0)
    (φ : Module.Dual (ZMod 2) E) : ∃ w : E, t (w,0) = (0,φ) := by
  obtain ⟨u, hu⟩ := t.surjective (0,φ)
  have he : u = (u.1,0) + (0,u.2) := by ext <;> simp
  have hfst := congrArg Prod.fst hu
  rw [he, map_add, Prod.fst_add, hE, zero_add] at hfst
  have hz : t (0,u.2) = 0 := Prod.ext hfst (hD u.2)
  have hu2 : u.2 = 0 := congrArg Prod.snd (t.map_eq_zero_iff.mp hz)
  refine ⟨u.1, ?_⟩
  have : (u.1,0) = u := by ext <;> simp [hu2]
  rwa [this]

private theorem conjugate_transvection (t : BinaryLinear.GL (PairedSpace E))
    (hq : ∀ u, BinaryNaturalDual.quadratic (t u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (t (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (t (0,f)).2 = 0)
    (c w : E) (d φ : Module.Dual (ZMod 2) E)
    (htd : t (0,d) = (c,0)) (htw : t (w,0) = (0,φ))
    (hφ : φ c = 0) (hw : d w = 0) :
    (MulAut.conj t⁻¹) (pairedAction (BinaryLinear.transvection c φ hφ)) =
      pairedAction (BinaryLinear.transvection w d hw) := by
  apply LinearEquiv.ext
  intro u
  apply t.injective
  change t (t.symm (pairedAction (BinaryLinear.transvection c φ hφ) (t u))) = _
  rw [t.apply_symm_apply]
  have hv (v : E) : (t (v,0)).2 c = d v := by
    simpa only [htd] using swap_pairing t hq hE hD v d
  have hf (f : Module.Dual (ZMod 2) E) : φ (t (0,f)).1 = f w := by
    simpa only [htw] using swap_pairing t hq hE hD w f
  have he : u = (u.1,0) + (0,u.2) := by ext <;> simp
  have htuf : φ (t u).1 = u.2 w := by
    rw [he, map_add, Prod.fst_add, hE, zero_add, hf]
    simp
  have htus : (t u).2 c = d u.1 := by
    rw [he, map_add, Prod.snd_add, hD, add_zero, hv]
    simp
  rw [paired_transvection_apply, paired_transvection_apply,
    map_add, map_add, map_smul, map_smul, htw, htd, htuf, htus]
  abel

/-- A quadratic isometry exchanging the two summands conjugates a full
center-root group to the marked full axis-root group. -/
theorem centerGroup_conjugate_eq_axisGroup
    (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0)
    (t : BinaryLinear.GL (PairedSpace E))
    (hq : ∀ u, BinaryNaturalDual.quadratic (t u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (t (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (t (0,f)).2 = 0)
    (htd : t (0,d) = (c,0)) :
    ((centerGroup c).map pairedAction).map (MulAut.conj t⁻¹).toMonoidHom =
      (axisGroup d).map pairedAction := by
  apply le_antisymm
  · rintro a ⟨b, ⟨g,hg,rfl⟩, rfl⟩
    obtain ⟨φ,hφ,rfl⟩ := (mem_centerGroup_iff c hc g).mp hg
    obtain ⟨w,htw⟩ := natural_preimage t hE hD φ
    have hw : d w = 0 := by
      have hh := swap_pairing t hq hE hD w d
      simpa only [htw, htd, hφ] using hh.symm
    exact ⟨BinaryLinear.transvection w d hw, transvection_mem_axisGroup d w hw,
      (conjugate_transvection t hq hE hD c w d φ htd htw hφ hw).symm⟩
  · rintro a ⟨g,hg,rfl⟩
    obtain ⟨_,w,hw,rfl⟩ := (mem_axisRootGroup_iff hd).mp hg
    let φ := (t (w,0)).2
    have htw : t (w,0) = (0,φ) := Prod.ext (hE w) rfl
    have hφ : φ c = 0 := by
      have hh := swap_pairing t hq hE hD w d
      simpa only [htw, htd, hw] using hh
    refine ⟨pairedAction (BinaryLinear.transvection c φ hφ), ?_, ?_⟩
    · apply mem_map_of_mem
      exact (mem_centerGroup_iff c hc _).mpr ⟨φ,hφ,rfl⟩
    · exact conjugate_transvection t hq hE hD c w d φ htd htw hφ hw

/-- The source's isometry and summand-exchange data discharge the conjugacy
premise in the paired-transvection fixed-space theorem. -/
theorem partner_fixedSpace_of_quadratic_exchange
    (c : E) (hc : c ≠ 0) (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0)
    (hdc : d c = 0) (t : BinaryLinear.GL (PairedSpace E))
    (hq : ∀ u, BinaryNaturalDual.quadratic (t u) = BinaryNaturalDual.quadratic u)
    (hE : ∀ v : E, (t (v,0)).1 = 0)
    (hD : ∀ f : Module.Dual (ZMod 2) E, (t (0,f)).2 = 0)
    (htc : t (c,0) = (0,d)) (htd : t (0,d) = (c,0)) :
    BinaryLinear.fixedSpace ((centerGroup c).map pairedAction ⊔ zpowers t) =
      Submodule.span (ZMod 2) {(c,d)} :=
  partner_fixedSpace c hc d hd hdc t htc htd
    (centerGroup_conjugate_eq_axisGroup c hc d hd t hq hE hD htd)

end BinaryPairedTransvections
