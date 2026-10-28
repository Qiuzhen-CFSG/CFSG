module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledLinearInvolutions
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCommonActors
public import Theory.Representation.SL3.NaturalDualFixed
-- Internal trace-pairing coordinates preserve the same original SL3 actor.
import all CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.LinearThreeCohomology

/-!
# Large elementary actors on the actual natural and twisted pair

The actual normalizing operator permutes the two inequivalent simple axes.
An exchanging operator has at most q³ fixed vectors. If all operators
preserve the axes, the first block is faithful on an exponent-two actor:
its kernel centralizes the whole SL3 pair and is therefore trivial.
The same-actor natural/dual comparison and field trace give literal dual
coordinates on the second block, with the same induced automorphism.
The paired fixed-space bound then applies to every actor of order above q.
Source: Aschbacher--Smith H.4.1, printed pp.383--385, refs/quasithin.pdf.
-/

public noncomputable section
open Representation Subgroup
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open ChapterB.QuasisimpleSource ChapterB.QuasisimpleSource.SourceCompletion

/-- The inequivalent twisted constituent has literal field-dual coordinates
with the same original SL3 actor, through the binary trace pairing. -/
theorem doubledLinear_second_dual_coordinates (F : BinaryField)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom))) :
    ∃ e : (Fin 3 → F.Carrier) ≃ₗ[ZMod 2] Module.Dual F.Carrier (Fin 3 → F.Carrier),
      ∀ g v, e (linearNatural F 3 (a g) v) = (specialLinearNatural 3).dual g (e v) := by
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  have hs : IsLinearNatural σ F 3 :=
    ⟨⟨MulEquiv.refl _,LinearEquiv.refl _ _,fun _ _ => rfl⟩⟩
  have ht : IsLinearNatural τ F 3 := ⟨⟨a,LinearEquiv.refl _ _,fun _ _ => rfl⟩⟩
  rcases linearThree_naturals_same_or_dual τ σ F F ht hs with hs' | hd'
  · obtain ⟨b⟩ := hs'
    exact (hne ⟨b.symm⟩).elim
  · obtain ⟨b⟩ := hd'
    let t := traceDualEquiv F 3
    have he (g) (φ : Module.Dual F.Carrier (Fin 3 → F.Carrier)) :
        t ((specialLinearNatural 3).dual g φ) = σ.dual g (t φ) := by
      apply LinearMap.ext
      intro v
      rfl
    refine ⟨b.toLinearEquiv.trans t.symm,?_⟩
    intro g v
    apply t.injective
    change t (t.symm (b (τ g v))) = t ((specialLinearNatural 3).dual g (t.symm (b v)))
    rw [t.apply_symm_apply,he,t.apply_symm_apply]
    exact LinearMap.congr_fun (b.isIntertwining' g) v

/-- A faithful exponent-two actor larger than the field fixes at most q³
vectors on the original inequivalent natural/twisted pair. Both blocks
induce the same literal automorphism of the original full SL3. -/
theorem doubledLinear_large_two_actor_fixed_card (F : BinaryField)
    (a : MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hne : ¬ Nonempty ((linearNatural F 3).Equiv
      ((linearNatural F 3).comp a.toMonoidHom)))
    {H : Type*} [Group H] [Finite H]
    (f : H →* (Module.End (ZMod 2)
      ((Fin 3 → F.Carrier) × (Fin 3 → F.Carrier)))ˣ)
    (hfi : Function.Injective f) (hsq : ∀ x : H, x^2=1)
    (α : H →* MulAut (Matrix.SpecialLinearGroup (Fin 3) F.Carrier))
    (hf : ∀ x g v, (f x).val (((linearNatural F 3).prod
      ((linearNatural F 3).comp a.toMonoidHom)) g v) =
      ((linearNatural F 3).prod ((linearNatural F 3).comp a.toMonoidHom))
        (α x g) ((f x).val v))
    (hlarge : Nat.card F.Carrier < Nat.card H) :
    Nat.card {v : (Fin 3 → F.Carrier) × (Fin 3 → F.Carrier) //
      ∀ x : H, (f x).val v = v} ≤ Nat.card F.Carrier ^ 3 := by
  classical
  let W := Fin 3 → F.Carrier
  let σ := linearNatural F 3
  let τ := σ.comp a.toMonoidHom
  let μ := σ.prod τ
  let : IsIrreducible σ := ExtensionConsequences.linearNatural_irreducible F (by decide)
  let : IsIrreducible τ := (irreducible_comp_surjective_iff
    a.toMonoidHom a.surjective σ).mpr inferInstance
  let E (x : H) := LinearMap.GeneralLinearGroup.toLinearEquiv (f x)
  have hE2 (x : H) (v : W × W) : E x (E x v) = v := by
    have hpow : (f x)^2=1 := by rw [←map_pow,hsq,map_one]
    exact congrArg (fun z : (Module.End (ZMod 2) (W × W))ˣ => z.val v) hpow
  have haxes (x : H) := irreducible_pair_normalizer_axes σ τ hne (α x) (E x) (hf x)
  by_cases hp : ∀ x : H, (∀ v : W, (E x (v,0)).2=0) ∧
      (∀ v : W, (E x (0,v)).1=0)
  · have he (x : H) (v : W × W) : E x v = ((E x (v.1,0)).1,(E x (0,v.2)).2) := by
      have hv : v=(v.1,0)+(0,v.2) := by simp
      calc
        E x v = E x (v.1,0)+E x (0,v.2) := by rw [←map_add,←hv]
        _ = _ := Prod.ext (by simpa using (hp x).2 v.2) (by simpa using (hp x).1 v.1)
    let b (x : H) : W →ₗ[ZMod 2] W :=
      (LinearMap.fst _ _ _).comp ((E x).toLinearMap.comp (LinearMap.inl _ _ _))
    let c (x : H) : W →ₗ[ZMod 2] W :=
      (LinearMap.snd _ _ _).comp ((E x).toLinearMap.comp (LinearMap.inr _ _ _))
    have hb2 (x : H) : Function.Involutive (b x) := by
      intro v
      have hh := congrArg Prod.fst (hE2 x (v,0))
      change (E x (E x (v,0))).1 = v at hh
      rw [he x (E x (v,0))] at hh
      exact hh
    have hc2 (x : H) : Function.Involutive (c x) := by
      intro v
      have hh := congrArg Prod.snd (hE2 x (0,v))
      rw [he x (E x (0,v))] at hh
      exact hh
    let β : H →* MulAut (Multiplicative W) := {
      toFun x := (LinearEquiv.ofInvolutive (b x) (hb2 x)).toAddEquiv.toMultiplicative
      map_one' := by
        apply MulEquiv.ext
        intro v
        change (E 1 (v.toAdd,0)).1 = v.toAdd
        change ((f 1).val (v.toAdd,0)).1 = v.toAdd
        rw [map_one]; rfl
      map_mul' x y := by
        apply MulEquiv.ext
        intro v
        change (E (x*y) (v.toAdd,0)).1 = (E x ((E y (v.toAdd,0)).1,0)).1
        change ((f (x*y)).val (v.toAdd,0)).1 = _
        rw [map_mul]
        have hh := congrArg Prod.fst (he x (E y (v.toAdd,0)))
        exact hh }
    let γ : H →* MulAut (Multiplicative W) := {
      toFun x := (LinearEquiv.ofInvolutive (c x) (hc2 x)).toAddEquiv.toMultiplicative
      map_one' := by
        apply MulEquiv.ext
        intro v
        change (E 1 (0,v.toAdd)).2 = v.toAdd
        change ((f 1).val (0,v.toAdd)).2 = v.toAdd
        rw [map_one]; rfl
      map_mul' x y := by
        apply MulEquiv.ext
        intro v
        change (E (x*y) (0,v.toAdd)).2 = (E x (0,(E y (0,v.toAdd)).2)).2
        change ((f (x*y)).val (0,v.toAdd)).2 = _
        rw [map_mul]
        have hh := congrArg Prod.snd (he x (E y (0,v.toAdd)))
        exact hh }
    have hb (x : H) (v : W) : (β x (Multiplicative.ofAdd v)).toAdd = (E x (v,0)).1 := rfl
    have hc (x : H) (v : W) : (γ x (Multiplicative.ofAdd v)).toAdd = (E x (0,v)).2 := rfl
    have hβ (x) (g) (v : W) :
        (β x (Multiplicative.ofAdd (specialLinearNatural 3 g v))).toAdd =
          specialLinearNatural 3 (α x g) ((β x (Multiplicative.ofAdd v)).toAdd) := by
      have hh := congrArg Prod.fst (hf x g (v,0))
      change (E x (specialLinearNatural 3 g v,specialLinearNatural 3 (a g) 0)).1 =
        specialLinearNatural 3 (α x g) (E x (v,0)).1 at hh
      rw [hb,hb]
      simpa only [map_zero] using hh
    have hγ (x) (g) (v : W) :
        (γ x (Multiplicative.ofAdd (τ g v))).toAdd =
          τ (α x g) ((γ x (Multiplicative.ofAdd v)).toAdd) := by
      have hh := congrArg Prod.snd (hf x g (0,v))
      change (E x (σ g 0,τ g v)).2 = τ (α x g) (E x (0,v)).2 at hh
      rw [hc,hc]
      simpa only [map_zero] using hh
    have hβi : Function.Injective β := by
      apply (injective_iff_map_eq_one _).mpr
      intro x hx
      have hα : α x = MulEquiv.refl _ := by
        apply MulEquiv.ext
        intro g
        apply specialLinearNatural_injective 3
        apply LinearMap.ext
        intro v
        have hh := hβ x g v
        rw [hx] at hh
        exact hh.symm
      have hid := irreducible_pair_centralizing_involution σ τ hne (E x) (hE2 x)
        (fun g v => by
          dsimp only [E,σ,τ]
          simpa only [hα,MulEquiv.refl_apply,LinearMap.GeneralLinearGroup.coe_toLinearEquiv] using hf x g v)
      apply hfi
      rw [map_one]
      apply Units.ext
      apply LinearMap.ext
      intro v
      exact LinearEquiv.congr_fun hid v
    obtain ⟨d,hd⟩ := doubledLinear_second_dual_coordinates F a hne
    let dm := d.toAddEquiv.toMultiplicative
    let δ := (MulAut.congr dm).toMonoidHom.comp γ
    have hδ (x) (g) (φ : Module.Dual F.Carrier W) :
        (δ x (Multiplicative.ofAdd ((specialLinearNatural 3).dual g φ))).toAdd =
          (specialLinearNatural 3).dual (α x g)
            ((δ x (Multiplicative.ofAdd φ)).toAdd) := by
      obtain ⟨v,rfl⟩ := d.surjective φ
      change d ((γ x (Multiplicative.ofAdd (d.symm ((specialLinearNatural 3).dual g (d v))))).toAdd) =
        (specialLinearNatural 3).dual (α x g)
          (d ((γ x (Multiplicative.ofAdd (d.symm (d v)))).toAdd))
      rw [←hd,d.symm_apply_apply,d.symm_apply_apply]
      change d ((γ x (Multiplicative.ofAdd (τ g v))).toAdd) = _
      rw [hγ]
      exact hd (α x g) _
    have hbig : Nat.card F.Carrier < Nat.card β.range := by
      rw [←Nat.card_congr (MonoidHom.ofInjective hβi).toEquiv]
      exact hlarge
    have hbnd := SL3NaturalFixed.paired_fixed_card_le β δ α hsq hβ hδ hbig
    let : Finite (Module.Dual F.Carrier W) := Finite.of_equiv W
      (SL3ParabolicNatural.dualVectorCoordinates (F := F.Carrier)).symm.toEquiv
    let X := {v : W // ∀ x, (β x (Multiplicative.ofAdd v)).toAdd=v}
    let Y := {φ : Module.Dual F.Carrier W // ∀ x, (δ x (Multiplicative.ofAdd φ)).toAdd=φ}
    let j : {v : W × W // ∀ x, E x v=v} → X × Y := fun v =>
      (⟨v.val.1,by
        intro x
        exact (congrArg Prod.fst (he x v)).symm.trans (congrArg Prod.fst (v.property x))⟩,
       ⟨d v.val.2,by
        intro x
        change d ((γ x (Multiplicative.ofAdd (d.symm (d v.val.2)))).toAdd)=d v.val.2
        rw [d.symm_apply_apply,hc]
        exact congrArg d ((congrArg Prod.snd (he x v)).symm.trans
          (congrArg Prod.snd (v.property x)))⟩)
    have hj : Function.Injective j := by
      intro v w hvw
      apply Subtype.ext
      exact Prod.ext (congrArg (fun z : X × Y => z.1.val) hvw)
        (d.injective (congrArg (fun z : X × Y => z.2.val) hvw))
    exact (Nat.card_le_card_of_injective j hj).trans ((Nat.card_prod X Y).le.trans hbnd)
  · obtain ⟨x,hx⟩ := not_forall.mp hp
    have hx := (haxes x).resolve_left hx
    have he (v : W × W) : (E x v).2=(E x (v.1,0)).2 := by
      have hv : v=(v.1,0)+(0,v.2) := by simp
      calc
        (E x v).2=(E x (v.1,0)).2+(E x (0,v.2)).2 := by rw [←Prod.snd_add,←map_add,←hv]
        _ = _ := by rw [hx.2,add_zero]
    have hi : Function.Injective (fun v : {v : W × W // ∀ y, E y v=v} => v.val.1) := by
      intro v w hvw
      change v.val.1=w.val.1 at hvw
      apply Subtype.ext
      apply Prod.ext hvw
      calc
        v.val.2=(E x v).2 := (congrArg Prod.snd (v.property x)).symm
        _=(E x (v.val.1,0)).2 := he _
        _=(E x (w.val.1,0)).2 := by rw [hvw]
        _=(E x w).2 := (he _).symm
        _=w.val.2 := congrArg Prod.snd (w.property x)
    exact (Nat.card_le_card_of_injective _ hi).trans_eq (by rw [Nat.card_fun,Nat.card_fin])

end CFSG.Quasithin.Chapter7.NormalizedSource
