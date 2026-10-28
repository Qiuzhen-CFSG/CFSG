module
public import Theory.Representation.BinaryPairedTransvections.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule
/-!
# Fixed lines for paired binary transvections

The full transvections with center `c` and those with axis `ker d`, where
`d c = 0`, act on a vector space and its dual. Their common fixed space
is the product of the marked lines. An additional actor exchanging the
lines has fixed space equal to the diagonal line. The final theorem
identifies it with any marked nonzero fixed vector.

This is the linear calculation used in Aschbacher--Smith, original
Lemma 15.3.56(7), printed p. 1148. The hypotheses retain the literal
conjugation by the inverse that occurs in the source partner group.
-/

@[expose] public section
open Subgroup
namespace BinaryPairedTransvections
open BinaryLinear BinaryTransvectionGroups
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

abbrev PairedSpace (E : Type*) [AddCommGroup E] [Module (ZMod 2) E] :=
  E × Module.Dual (ZMod 2) E

/-- The literal natural-plus-contragredient action. -/
def pairedAction : GL E →* GL (PairedSpace E) where
  toFun g := g.prodCongr (contragredient g)
  map_one' := by ext v <;> rfl
  map_mul' a b := by ext v <;> rfl

theorem pairedAction_injective : Function.Injective (pairedAction (E := E)) := by
  intro a b he
  ext v
  exact congrArg (fun g : GL (PairedSpace E) => (g (v,0)).1) he

private theorem paired_radical_fixed {W : Submodule (ZMod 2) E}
    {g : GL E} (hg : g ∈ radical W) (x : E) (f : Module.Dual (ZMod 2) E)
    (hx : x ∈ W) (hf : f ∈ W.dualAnnihilator) : pairedAction g (x,f) = (x,f) := by
  apply Prod.ext
  · exact hg.1 x hx
  · exact ((contragredient_mem_radical_iff W g).mpr hg).1 f hf

private theorem dual_fixed_axis (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0)
    (f : Module.Dual (ZMod 2) E)
    (hf : ∀ a ∈ axisGroup d, contragredient a f = f) :
    f ∈ Submodule.span (ZMod 2) {d} := by
  change f ∈ centerLine d
  rw [← ker_dualAnnihilator, Submodule.mem_dualAnnihilator]
  intro w hw
  obtain ⟨v,hv⟩ := LinearMap.surjective hd 1
  have hh := congrArg (fun l : Module.Dual (ZMod 2) E => l v)
    (hf (transvection w d hw) (transvection_mem_axisGroup d w hw))
  change f (v + d v • w) = f v at hh
  rw [hv, one_smul, map_add] at hh
  exact add_eq_left.mp hh

/-- Both full transvection groups fix exactly the two marked lines. -/
theorem paired_fixedSpace (c : E) (hc : c ≠ 0)
    (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0) :
    BinaryLinear.fixedSpace ((pairGroup c d).map pairedAction) =
      (Submodule.span (ZMod 2) {c}).prod (Submodule.span (ZMod 2) {d}) := by
  ext u
  constructor
  · intro hu
    constructor
    · apply (mem_iff_fixed_radical (show Submodule.span (ZMod 2) {c} ≠ ⊥ from fun h => hc (by
        have hh := h ▸ Submodule.mem_span_singleton_self c
        exact hh)) u.1).mpr
      intro a ha
      have hh := hu (pairedAction a) (mem_map_of_mem _ (show a ∈ pairGroup c d from
        mem_sup_left (by simpa only [centerGroup_eq_radical] using ha)))
      exact congrArg Prod.fst hh
    · apply dual_fixed_axis d hd u.2
      intro a ha
      exact congrArg Prod.snd (hu (pairedAction a) (mem_map_of_mem _ (mem_sup_right ha)))
  · rintro ⟨hc',hd'⟩
    let S : Subgroup (GL E) := (MulAction.stabilizer (GL (PairedSpace E)) u).comap pairedAction
    have hS : pairGroup c d ≤ S := by
      apply sup_le
      · intro a ha
        change pairedAction a u = u
        apply paired_radical_fixed (by simpa only [centerGroup_eq_radical] using ha) u.1 u.2 hc'
        rw [Submodule.mem_dualAnnihilator]
        intro x hx
        obtain ⟨r,rfl⟩ := Submodule.mem_span_singleton.mp hx
        obtain ⟨s,hs⟩ := Submodule.mem_span_singleton.mp hd'
        rw [← hs, map_smul, LinearMap.smul_apply, hdc, smul_zero, smul_zero]
      · intro a ha
        change pairedAction a u = u
        apply paired_radical_fixed (by simpa only [axisGroup_eq_radical] using ha) u.1 u.2
        · obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hc'
          change d u.1 = 0
          rw [← hr,map_smul,hdc,smul_zero]
        · rwa [ker_dualAnnihilator]
    rintro _ ⟨a,ha,rfl⟩
    exact hS ha

/-- Exchanging the two marked fixed lines leaves precisely the diagonal line. -/
theorem exchanged_fixedSpace (c : E) (hc : c ≠ 0)
    (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0)
    (t : GL (PairedSpace E))
    (htc : t (c,0) = (0,d)) (htd : t (0,d) = (c,0)) :
    BinaryLinear.fixedSpace ((pairGroup c d).map pairedAction) ⊓ t.fixedSubmodule =
      Submodule.span (ZMod 2) {(c,d)} := by
  rw [paired_fixedSpace c hc d hd hdc]
  ext u
  constructor
  · rintro ⟨⟨hx,hf⟩,ht⟩
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b,hb⟩ := Submodule.mem_span_singleton.mp hf
    have hu : u = a • (c,0) + b • (0,d) := by
      apply Prod.ext
      · simpa only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero] using ha.symm
      · simpa only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add] using hb.symm
    have he : a = b := by
      have hh : t u = u := ht
      rw [hu,map_add,map_smul,map_smul,htc,htd] at hh
      have hh' := congrArg Prod.fst hh
      simp only [Prod.fst_add,Prod.smul_fst,smul_zero,zero_add,add_zero] at hh'
      exact ((smul_left_injective _ hc) hh').symm
    apply Submodule.mem_span_singleton.mpr
    refine ⟨a, ?_⟩
    rw [hu, ← he]
    ext <;> simp
  · rintro hu
    obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp hu
    refine ⟨⟨Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self c),
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)⟩,?_⟩
    change t (a • (c,d)) = a • (c,d)
    have he : (c,d) = (c,0) + (0,d) := by ext <;> simp
    rw [map_smul,he,map_add,htc,htd,add_comm]

/-- The source fixed line has binary dimension one. -/
theorem exchanged_fixedSpace_finrank (c : E) (hc : c ≠ 0)
    (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0)
    (t : GL (PairedSpace E))
    (htc : t (c,0) = (0,d)) (htd : t (0,d) = (c,0)) :
    Module.finrank (ZMod 2)
      ↥(BinaryLinear.fixedSpace ((pairGroup c d).map pairedAction) ⊓ t.fixedSubmodule) = 1 := by
  rw [exchanged_fixedSpace c hc d hd hdc t htc htd]
  exact finrank_span_singleton (fun h => hc (congrArg Prod.fst h))

private theorem fixedSpace_sup {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (A B : Subgroup (GL W)) :
    BinaryLinear.fixedSpace (A ⊔ B) = BinaryLinear.fixedSpace A ⊓ BinaryLinear.fixedSpace B := by
  ext v
  constructor
  · exact fun hv => ⟨fun a ha => hv a (mem_sup_left ha),fun b hb => hv b (mem_sup_right hb)⟩
  · rintro ⟨ha,hb⟩
    have hh : A ⊔ B ≤ MulAction.stabilizer (GL W) v := sup_le ha hb
    exact hh

private theorem fixedSpace_zpowers {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (t : GL W) : BinaryLinear.fixedSpace (zpowers t) = t.fixedSubmodule := by
  ext v
  constructor
  · intro hv
    exact hv t (mem_zpowers t)
  · intro hv
    exact (zpowers_le.mpr (show t ∈ MulAction.stabilizer (GL W) v from hv))

/-- On the source actor X⟨t⟩, exchanging the two full transvection groups and
their fixed lines leaves exactly the diagonal marked vector. -/
theorem partner_fixedSpace (c : E) (hc : c ≠ 0)
    (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0)
    (t : GL (PairedSpace E))
    (htc : t (c,0) = (0,d)) (htd : t (0,d) = (c,0))
    (hexchange : ((centerGroup c).map pairedAction).map (MulAut.conj t⁻¹).toMonoidHom =
      (axisGroup d).map pairedAction) :
    BinaryLinear.fixedSpace ((centerGroup c).map pairedAction ⊔ zpowers t) =
      Submodule.span (ZMod 2) {(c,d)} := by
  let J := (centerGroup c).map pairedAction ⊔ zpowers t
  have ht : t ∈ J := mem_sup_right (mem_zpowers t)
  have haxis : (axisGroup d).map pairedAction ≤ J := by
    rw [← hexchange]
    rintro _ ⟨a,ha,rfl⟩
    exact J.mul_mem (J.mul_mem (J.inv_mem ht) (mem_sup_left ha)) (J.inv_mem (J.inv_mem ht))
  have hpair : (pairGroup c d).map pairedAction ⊔ zpowers t = J := by
    rw [pairGroup, Subgroup.map_sup]
    apply le_antisymm
    · exact sup_le (sup_le le_sup_left haxis) le_sup_right
    · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  change BinaryLinear.fixedSpace J = _
  rw [← hpair, fixedSpace_sup, fixedSpace_zpowers]
  exact exchanged_fixedSpace c hc d hd hdc t htc htd

/-- A marked nonzero fixed vector identifies the source's distinguished line. -/
theorem partner_fixedSpace_eq_marked (c : E) (hc : c ≠ 0)
    (d : Module.Dual (ZMod 2) E) (hd : d ≠ 0) (hdc : d c = 0)
    (t : GL (PairedSpace E))
    (htc : t (c,0) = (0,d)) (htd : t (0,d) = (c,0))
    (hexchange : ((centerGroup c).map pairedAction).map (MulAut.conj t⁻¹).toMonoidHom =
      (axisGroup d).map pairedAction)
    (z : PairedSpace E) (hz : z ≠ 0)
    (hzfix : z ∈ BinaryLinear.fixedSpace ((centerGroup c).map pairedAction ⊔ zpowers t)) :
    BinaryLinear.fixedSpace ((centerGroup c).map pairedAction ⊔ zpowers t) =
      Submodule.span (ZMod 2) {z} := by
  rw [partner_fixedSpace c hc d hd hdc t htc htd hexchange] at hzfix ⊢
  have he : z = (c,d) := ((mem_centerLine_iff (c,d) z).mp hzfix).resolve_left hz
  rw [he]

end BinaryPairedTransvections
