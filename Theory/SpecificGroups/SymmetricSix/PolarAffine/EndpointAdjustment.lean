module

public import Theory.SpecificGroups.SymmetricSix.PolarAffine.CocycleRestriction
import Mathlib.Tactic.Group

/-!
# Selecting actual endpoint adjustments

A prescribed displacement on an endpoint can be realized on the original
hexad extension exactly when it has the binary quadratic plus principal
normal form. The construction uses the whole original kernel, not a chosen
complement. It fixes that kernel pointwise and preserves every subgroup
containing it. No assertion of universal endpoint cocycle extension is made.
-/

public noncomputable section
namespace Theory.SpecificGroups.SymmetricSix.PolarAffine
open Subgroup

/-- Every polar cocycle acts on the original extension, preserving its kernel
and quotient. Its fixed elements are exactly the zero-displacement elements. -/
theorem exists_original_cocycle_automorphism {D : Type*} [Group D]
    (q : D →* A6) (k : q.ker ≃* Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker), k (MulAut.conjNormal g a) =
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd))
    (δ : A6 → NaturalModule)
    (hδ : ∀ g h, δ (g*h) = polarAction g.val (δ h) + δ g) :
    ∃ α : MulAut D,
      (∀ g, q (α g) = q g) ∧
      (∀ a : q.ker, α a = (a : D)) ∧
      (∀ g, α g = (k.symm (Multiplicative.ofAdd (δ (q g))) : D) * g) ∧
      (∀ g, α (α g) = g) ∧
      (∀ g, α g = g ↔ δ (q g) = 0) ∧
      (∀ P : Subgroup D, q.ker ≤ P → P.map α.toMonoidHom = P) := by
  let j : NaturalModule → D := fun v => k.symm (Multiplicative.ofAdd v)
  have hj0 : j 0 = 1 := by simp [j]
  have hjadd (v w : NaturalModule) : j (v+w) = j v * j w := by
    change ((k.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : q.ker) : D) = _
    rw [map_mul]
    rfl
  have hjq (v : NaturalModule) : q (j v) = 1 := (k.symm (Multiplicative.ofAdd v)).property
  have hji : Function.Injective j := fun v w h =>
    Multiplicative.ofAdd.injective (k.symm.injective (Subtype.ext h))
  have hjconj (g : D) (v : NaturalModule) :
      j (polarAction (q g).val v) = g * j v * g⁻¹ := by
    have hh := congrArg (fun x : Multiplicative NaturalModule => (k.symm x : D))
      (hk g (k.symm (Multiplicative.ofAdd v)))
    simpa only [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply,
      toAdd_ofAdd, MulAut.conjNormal_apply, j] using hh.symm
  have hjself (v : NaturalModule) : j v * j v = 1 := by
    rw [←hjadd]
    have hh : v+v=0 := by ext i; exact CharTwo.add_self_eq_zero _
    rw [hh,hj0]
  have hδ0 : δ 1 = 0 := by
    have hh := hδ 1 1
    simp only [one_mul, Subgroup.coe_one, polarAction_one] at hh
    exact add_left_cancel (hh.symm.trans (add_zero (δ 1)).symm)
  let f : D → D := fun g => j (δ (q g)) * g
  have hfq (g : D) : q (f g) = q g := by simp only [f,map_mul,hjq,one_mul]
  have hfmul (g h : D) : f (g*h) = f g * f h := by
    dsimp only [f]
    rw [map_mul,hδ,add_comm (polarAction _ _) (δ _),hjadd,hjconj]
    group
  have hff (g : D) : f (f g) = g := by
    change j (δ (q (f g))) * (j (δ (q g)) * g) = g
    rw [hfq,←mul_assoc,hjself,one_mul]
  let α : MulAut D :=
    { toFun := f
      invFun := f
      left_inv := hff
      right_inv := hff
      map_mul' := hfmul }
  refine ⟨α,hfq,?_,fun _ => rfl,hff,?_,?_⟩
  · intro a
    change j (δ (q a)) * a = (a : D)
    rw [a.property,hδ0,hj0,one_mul]
  · intro g
    change j (δ (q g)) * g = g ↔ δ (q g) = 0
    rw [mul_eq_right, ←hj0, hji.eq_iff]
  · intro P hP
    apply le_antisymm
    · rintro x ⟨g,hg,rfl⟩
      exact P.mul_mem (hP (hjq _)) hg
    · intro g hg
      have hfg : α g ∈ P := P.mul_mem (hP (hjq _)) hg
      exact ⟨α g,hfg,hff g⟩

/-- The exact selection criterion for a displacement on an actual endpoint
inside the original hexad group. Both directions concern automorphisms of
that same group, fixing its whole kernel pointwise and its quotient. -/
theorem original_endpoint_adjustment_iff {D H : Type*} [Group D] [Group H]
    (q : D →* A6) (hq : Function.Surjective q)
    (k : q.ker ≃* Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker), k (MulAut.conjNormal g a) =
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd))
    (ι : H →* D) (f : H → NaturalModule) :
    (∃ α : MulAut D,
      (∀ g, q (α g) = q g) ∧
      (∀ a : q.ker, α a = (a : D)) ∧
      (∀ h, α (ι h) = (k.symm (Multiplicative.ofAdd (f h)) : D) * ι h) ∧
      (∀ P : Subgroup D, q.ker ≤ P → P.map α.toMonoidHom = P) ∧
      (∀ h, α (ι h) = ι h ↔ f h = 0)) ↔
    ∃ (b : ZMod 2) (v : NaturalModule),
      ∀ h, f h = b • quadratic (q (ι h)) + (polarAction (q (ι h)).val v - v) := by
  let j : NaturalModule → D := fun v => k.symm (Multiplicative.ofAdd v)
  have hji : Function.Injective j := fun v w h =>
    Multiplicative.ofAdd.injective (k.symm.injective (Subtype.ext h))
  have hjadd (v w : NaturalModule) : j (v+w) = j v * j w := by
    change ((k.symm (Multiplicative.ofAdd v * Multiplicative.ofAdd w) : q.ker) : D) = _
    rw [map_mul]
    rfl
  have hjconj (g : D) (v : NaturalModule) :
      j (polarAction (q g).val v) = g * j v * g⁻¹ := by
    have hh := congrArg (fun x : Multiplicative NaturalModule => (k.symm x : D))
      (hk g (k.symm (Multiplicative.ofAdd v)))
    simpa only [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply,
      toAdd_ofAdd, MulAut.conjNormal_apply, j] using hh.symm
  constructor
  · rintro ⟨α,hαq,hαk,hαf,_,_⟩
    let d : D → NaturalModule := fun g =>
      (k ⟨α g * g⁻¹, by simp only [MonoidHom.mem_ker, map_mul, map_inv,
        hαq, mul_inv_cancel]⟩).toAdd
    have hd (g : D) : j (d g) = α g * g⁻¹ := by
      exact congrArg Subtype.val (k.symm_apply_apply _)
    have hfiber (g h : D) (hgh : q g = q h) : d g = d h := by
      let a : q.ker := ⟨h⁻¹*g, by
        simp only [MonoidHom.mem_ker, map_mul, map_inv, hgh, inv_mul_cancel]⟩
      have ha := hαk a
      have hrep : g = h * (a : D) := by dsimp [a]; group
      have halpha : α g = α h * (h⁻¹*g) := by
        rw [hrep, map_mul, ha]
        group
      apply hji
      rw [hd, hd, halpha]
      group
    let s : A6 → D := fun x => Classical.choose (hq x)
    have hs (x : A6) : q (s x) = x := Classical.choose_spec (hq x)
    let δ : A6 → NaturalModule := fun x => d (s x)
    have hδq (g : D) : δ (q g) = d g := hfiber _ _ (hs _)
    have hrep (g : D) : α g = j (δ (q g)) * g := by
      rw [hδq,hd]
      group
    have hδ : ∀ g h, δ (g*h) = polarAction g.val (δ h) + δ g := by
      intro x y
      obtain ⟨g,rfl⟩ := hq x
      obtain ⟨h,rfl⟩ := hq y
      apply hji
      rw [add_comm (polarAction _ _) (δ _),hjadd,hjconj]
      have he : j (δ (q (g*h))) * (g*h) =
          (j (δ (q g)) * g) * (j (δ (q h)) * h) := by
        rw [←hrep, map_mul, ←hrep, ←hrep]
      rw [map_mul] at he
      apply mul_right_cancel (b := g*h)
      calc
        _ = (j (δ (q g)) * g) * (j (δ (q h)) * h) := he
        _ = _ := by group
    apply (restriction_extends_iff (q.comp ι) f).mp
    refine ⟨δ,hδ,?_⟩
    intro h
    apply hji
    apply mul_right_cancel (b := ι h)
    exact (hrep (ι h)).symm.trans (hαf h)
  · intro hf
    obtain ⟨δ,hδ,hr⟩ := (restriction_extends_iff (q.comp ι) f).mpr hf
    obtain ⟨α,hαq,hαk,hα,_,hfix,hpres⟩ := exists_original_cocycle_automorphism q k hk δ hδ
    refine ⟨α,hαq,hαk,(fun h => ?_),hpres,fun h => ?_⟩
    · rw [hα, show δ (q (ι h)) = f h from hr h]
    · rw [hfix, show δ (q (ι h)) = f h from hr h]

/-- Two actual endpoint maps with the same quotient marking can be aligned
exactly when their measured kernel displacement lies in the ambient cocycle
orbit. Thus the criterion can be applied directly to candidate markings. -/
theorem original_endpoint_alignment_iff {D H : Type*} [Group D] [Group H]
    (q : D →* A6) (hq : Function.Surjective q)
    (k : q.ker ≃* Multiplicative NaturalModule)
    (hk : ∀ (g : D) (a : q.ker), k (MulAut.conjNormal g a) =
      Multiplicative.ofAdd (polarAction (q g).val (k a).toAdd))
    (ι τ : H →* D) (hmark : ∀ h, q (τ h) = q (ι h)) :
    (∃ α : MulAut D,
      (∀ g, q (α g) = q g) ∧
      (∀ a : q.ker, α a = (a : D)) ∧
      (∀ h, α (ι h) = τ h) ∧
      (∀ P : Subgroup D, q.ker ≤ P → P.map α.toMonoidHom = P)) ↔
    ∃ (b : ZMod 2) (v : NaturalModule), ∀ h,
      (k ⟨τ h * (ι h)⁻¹, by
        simp only [MonoidHom.mem_ker, map_mul, map_inv, hmark, mul_inv_cancel]⟩).toAdd =
      b • quadratic (q (ι h)) + (polarAction (q (ι h)).val v - v) := by
  let f : H → NaturalModule := fun h =>
    (k ⟨τ h * (ι h)⁻¹, by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, hmark, mul_inv_cancel]⟩).toAdd
  have hf (h : H) : (k.symm (Multiplicative.ofAdd (f h)) : D) * ι h = τ h := by
    have he : (k.symm (Multiplicative.ofAdd (f h)) : D) = τ h * (ι h)⁻¹ :=
      congrArg Subtype.val (k.symm_apply_apply _)
    rw [he]
    group
  have hfzero (h : H) : f h = 0 ↔ τ h = ι h := by
    have hj0 : (k.symm (Multiplicative.ofAdd (0 : NaturalModule)) : D) = 1 := by simp
    constructor
    · intro hh
      have he := hf h
      rw [hh,hj0,one_mul] at he
      exact he.symm
    · intro hh
      have he : (k.symm (Multiplicative.ofAdd (f h)) : D) = 1 := by
        exact mul_right_cancel ((hf h).trans (hh.trans (one_mul (ι h)).symm))
      have hz := k.symm.injective (Subtype.ext (he.trans hj0.symm))
      exact Multiplicative.ofAdd.injective hz
  constructor
  · rintro ⟨α,hαq,hαk,hα,hpres⟩
    apply (original_endpoint_adjustment_iff q hq k hk ι f).mp
    refine ⟨α,hαq,hαk,(fun h => (hα h).trans (hf h).symm),hpres,fun h => ?_⟩
    rw [hα,hfzero]
  · intro hfsel
    obtain ⟨α,hαq,hαk,hα,hpres,_⟩ :=
      (original_endpoint_adjustment_iff q hq k hk ι f).mpr hfsel
    exact ⟨α,hαq,hαk,fun h => (hα h).trans (hf h),hpres⟩

end Theory.SpecificGroups.SymmetricSix.PolarAffine
