module

public import Theory.FieldTheory.QuadraticFrobenius
public import Mathlib.Tactic

/-!
# Additive rigidity of the symplectic Sylow square map

In characteristic two, the square map on the central quotient is
`(b,v) ↦ (b²v,bv)`. Its zero set and its nonimage both recover the two
coordinate axes. Compatible additive automorphisms are consequently diagonal
semilinear or graph semilinear when the field degree exceeds two.

The mismatched axis case would force every element to satisfy `x⁴=x`;
the order of Frobenius excludes it. This is the intrinsic Sylow argument
used in the noncentral case of Aschbacher–Smith, 2.4.24.
-/

@[expose] public section

noncomputable section

namespace Theory.SpecificGroups.SymplecticFour.QuotientActors

variable {F : Type*} [Field F]

def axis (x : F × F) : Prop := x.1 = 0 ∨ x.2 = 0

def squareMap (x : F × F) : F × F := (x.1^2*x.2,x.1*x.2)

lemma squareMap_eq_zero (x : F × F) : squareMap x = 0 ↔ axis x := by
  constructor
  · intro h
    exact mul_eq_zero.mp (congrArg Prod.snd h)
  · rintro (h|h) <;> simp [squareMap,h]

lemma squareMap_range (y : F × F) :
    (∃ x, squareMap x = y) ↔ y = 0 ∨ (y.1 ≠ 0 ∧ y.2 ≠ 0) := by
  constructor
  · rintro ⟨⟨b,v⟩,rfl⟩
    by_cases hb : b=0
    · simp [squareMap,hb]
    by_cases hv : v=0
    · simp [squareMap,hv]
    exact Or.inr ⟨mul_ne_zero (pow_ne_zero _ hb) hv,mul_ne_zero hb hv⟩
  · rintro (rfl|⟨hr,hw⟩)
    · exact ⟨0,by simp [squareMap]⟩
    · refine ⟨(y.1/y.2,y.2^2/y.1),?_⟩
      apply Prod.ext <;> dsimp [squareMap] <;> field_simp

lemma axis_iff_nonsquare (y : F × F) :
    axis y ↔ y=0 ∨ ¬∃ x, squareMap x=y := by
  rw [squareMap_range]
  by_cases hy : y=0
  · simp [hy,axis]
  · simp [hy,axis]
    tauto

lemma axis_maps (a b : (F × F) ≃+ (F × F))
    (h : ∀ x, squareMap (a x)=b (squareMap x)) :
    (∀ x, axis (a x) ↔ axis x) ∧ (∀ x, axis (b x) ↔ axis x) := by
  constructor
  · intro x
    rw [←squareMap_eq_zero, h, map_eq_zero_iff b b.injective, squareMap_eq_zero]
  · intro y
    have hr : (∃ x,squareMap x=b y) ↔ ∃ x,squareMap x=y := by
      constructor
      · rintro ⟨x,hx⟩
        obtain ⟨z,rfl⟩ := a.surjective x
        exact ⟨z,b.injective ((h z).symm.trans hx)⟩
      · rintro ⟨x,rfl⟩
        exact ⟨a x,h x⟩
    rw [axis_iff_nonsquare,axis_iff_nonsquare,hr,map_eq_zero_iff b b.injective]

private lemma additive_axis (f : F →+ F × F) (h : ∀ x,axis (f x)) :
    (∀ x,(f x).1=0) ∨ (∀ x,(f x).2=0) := by
  classical
  by_cases h₁ : ∀ x,(f x).1=0
  · exact Or.inl h₁
  push Not at h₁
  obtain ⟨x,hx⟩ := h₁
  have hx' := (h x).resolve_left hx
  refine Or.inr (fun y => ?_)
  by_contra hy
  have hy' := (h y).resolve_right hy
  have hh := h (x+y)
  simp only [axis,map_add,Prod.fst_add,Prod.snd_add,hx',hy',add_zero,zero_add] at hh
  exact hh.elim hx hy

private lemma axis_preserving_form (a : (F × F) ≃+ (F × F))
    (h₁ : ∀ x,(a (x,0)).2=0) (h₂ : ∀ x,(a (0,x)).1=0) :
    ∃ f g : F ≃+ F, ∀ x, a x=(f x.1,g x.2) := by
  let f : F →+ F := (AddMonoidHom.fst F F).comp
    (a.toAddMonoidHom.comp (AddMonoidHom.inl F F))
  let g : F →+ F := (AddMonoidHom.snd F F).comp
    (a.toAddMonoidHom.comp (AddMonoidHom.inr F F))
  have he (x : F × F) : a x=(f x.1,g x.2) := by
    have hh := a.map_add (x.1,0) (0,x.2)
    apply Prod.ext
    · change (a x).1=(a (x.1,0)).1
      simpa only [Prod.mk_add_mk,add_zero,zero_add,Prod.mk.eta,Prod.fst_add,h₂,add_zero] using congrArg Prod.fst hh
    · change (a x).2=(a (0,x.2)).2
      simpa only [Prod.mk_add_mk,add_zero,zero_add,Prod.mk.eta,Prod.snd_add,h₁,zero_add] using congrArg Prod.snd hh
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      have hh : a (x,0)=a (y,0) := by rw [he,he,hxy]
      exact congrArg Prod.fst (a.injective hh)
    · intro y
      obtain ⟨x,hx⟩ := a.surjective (y,0)
      exact ⟨x.1,by simpa only [he] using congrArg Prod.fst hx⟩
  have hg : Function.Bijective g := by
    constructor
    · intro x y hxy
      have hh : a (0,x)=a (0,y) := by rw [he,he,hxy]
      exact congrArg Prod.snd (a.injective hh)
    · intro y
      obtain ⟨x,hx⟩ := a.surjective (0,y)
      exact ⟨x.2,by simpa only [he] using congrArg Prod.snd hx⟩
  exact ⟨AddEquiv.ofBijective f hf,AddEquiv.ofBijective g hg,he⟩

lemma axis_form (a : (F × F) ≃+ (F × F)) (ha : ∀ x,axis (a x) ↔ axis x) :
    (∃ f g : F ≃+ F, ∀ x, a x=(f x.1,g x.2)) ∨
    (∃ f g : F ≃+ F, ∀ x, a x=(f x.2,g x.1)) := by
  let i₁ : F →+ F × F := AddMonoidHom.inl F F
  let i₂ : F →+ F × F := AddMonoidHom.inr F F
  have hh₁ := additive_axis (a.toAddMonoidHom.comp i₁) (fun x => (ha _).mpr (Or.inr rfl))
  have hh₂ := additive_axis (a.toAddMonoidHom.comp i₂) (fun x => (ha _).mpr (Or.inl rfl))
  change (∀ x,(a (x,0)).1=0) ∨ (∀ x,(a (x,0)).2=0) at hh₁
  change (∀ x,(a (0,x)).1=0) ∨ (∀ x,(a (0,x)).2=0) at hh₂
  rcases hh₁ with h₁|h₁ <;> rcases hh₂ with h₂|h₂
  · obtain ⟨x,hx⟩ := a.surjective (1,0)
    have hh := congrArg Prod.fst (a.map_add (x.1,0) (0,x.2))
    simp only [Prod.mk_add_mk,add_zero,zero_add,Prod.fst_add,h₁,h₂,add_zero,hx] at hh
    exact (one_ne_zero hh).elim
  · let e := a.trans ((AddEquiv.prodComm : (F × F) ≃+ (F × F)))
    obtain ⟨f,g,hfg⟩ := axis_preserving_form e h₁ h₂
    refine Or.inr ⟨g,f,fun x => ?_⟩
    have hh := congrArg Prod.swap (hfg x)
    exact hh
  · exact Or.inl (axis_preserving_form a h₁ h₂)
  · obtain ⟨x,hx⟩ := a.surjective (0,1)
    have hh := congrArg Prod.snd (a.map_add (x.1,0) (0,x.2))
    simp only [Prod.mk_add_mk,add_zero,zero_add,Prod.snd_add,h₁,h₂,add_zero,hx] at hh
    exact (one_ne_zero hh).elim



lemma product_rigidity (f g h : F ≃+ F)
    (hh : ∀ x y, h (x*y)=f x*g y) :
    ∃ σ : F ≃+* F, (∀ x,f x=f 1*σ x) ∧ (∀ x,g x=g 1*σ x) := by
  have hc : f 1≠0 := fun he => one_ne_zero (f.injective (he.trans (map_zero f).symm))
  have hd : g 1≠0 := fun he => one_ne_zero (g.injective (he.trans (map_zero g).symm))
  have he (x) : h x=f x*g 1 := by simpa using hh x 1
  have hg (x) : f x*g 1=f 1*g x := (he x).symm.trans (by simpa using hh 1 x)
  have hm (x y) : f (x*y)*f 1=f x*f y := by
    apply mul_right_cancel₀ hd
    calc
      f (x*y)*f 1*g 1=f 1*(f (x*y)*g 1) := by ring
      _=f 1*h (x*y) := by rw [he]
      _=f x*(f 1*g y) := by rw [hh]; ring
      _=f x*(f y*g 1) := by rw [←hg]
      _=f x*f y*g 1 := by ring
  let σ₀ : F →+* F :=
    { toFun := fun x=>f x/f 1
      map_one' := div_self hc
      map_mul' := fun x y=>by
        field_simp
        exact hm x y
      map_zero' := by simp
      map_add' := fun x y=>by simp only [map_add,add_div] }
  have hσ : Function.Bijective σ₀ := by
    constructor
    · intro x y hxy
      apply f.injective
      exact (div_left_inj' hc).mp hxy
    · intro y
      obtain ⟨x,hx⟩ := f.surjective (y*f 1)
      refine ⟨x,?_⟩
      change f x/f 1=y
      rw [hx,mul_div_cancel_right₀ _ hc]
  let σ := RingEquiv.ofBijective σ₀ hσ
  refine ⟨σ,fun x=>?_,fun x=>?_⟩
  · change f x=f 1*(f x/f 1)
    field_simp
  · change g x=g 1*(f x/f 1)
    field_simp
    calc
      g x*f 1=f 1*g x := mul_comm _ _
      _=f x*g 1 := (hg x).symm
      _=g 1*f x := mul_comm _ _

variable [Finite F] [CharP F 2]

lemma fourth_power_not_identity {n : ℕ} (hF : Nat.card F=2^n) (hn : 2<n) :
    ¬∀ x : F,x^4=x := by
  intro h
  have he : frobeniusEquiv F 2 ^ 2=1 := by
    ext x
    change (x^2)^2=x
    simpa only [←pow_mul] using h x
  have hd : n∣2 := by
    rw [←FiniteField.frobeniusEquiv_orderOf_of_card hF]
    exact orderOf_dvd_of_pow_eq_one he
  exact (not_le.mpr hn) (Nat.le_of_dvd (by decide) hd)

lemma mismatched_axes_impossible {n : ℕ} (hF : Nat.card F=2^n) (hn : 2<n)
    (f g h k : F ≃+ F)
    (h₁ : ∀ x y, (f x)^2*g y=h (x*y))
    (h₂ : ∀ x y, f x*g y=k (x^2*y)) : False := by
  let f₂ := f.trans (frobeniusEquiv F 2).toAddEquiv
  obtain ⟨σ,hf,hg⟩ := product_rigidity f₂ g h (fun x y=>(h₁ x y).symm)
  have hc : f 1≠0 := fun he => one_ne_zero (f.injective (he.trans (map_zero f).symm))
  have hd : g 1≠0 := fun he => one_ne_zero (g.injective (he.trans (map_zero g).symm))
  have hk (y) : k y=f 1*g y := by simpa using (h₂ 1 y).symm
  have he (x) : f x=f 1*σ (x^2) := by
    apply mul_right_cancel₀ hd
    calc
      f x*g 1=k (x^2) := by simpa using h₂ x 1
      _=f 1*(g 1*σ (x^2)) := by rw [hk,hg]
      _=f 1*σ (x^2)*g 1 := by ring
  apply fourth_power_not_identity hF hn
  intro y
  obtain ⟨x,rfl⟩ := σ.surjective y
  have hx : (f x)^2=(f 1)^2*σ x := hf x
  rw [he,map_pow,mul_pow,←pow_mul] at hx
  exact mul_left_cancel₀ (pow_ne_zero _ hc) hx

lemma preserving_rigidity {n : ℕ} (hF : Nat.card F=2^n) (hn : 2<n)
    (a b : (F × F) ≃+ (F × F))
    (h : ∀ x,squareMap (a x)=b (squareMap x))
    (f g : F ≃+ F) (ha : ∀ x,a x=(f x.1,g x.2)) :
    ∃ σ : F ≃+* F, ∀ x,a x=(f 1*σ x.1,g 1*σ x.2) := by
  rcases axis_form b (axis_maps a b h).2 with ⟨u,v,hb⟩|⟨u,v,hb⟩
  · have hh (x y) : v (x*y)=f x*g y := by
      have hh := congrArg Prod.snd (h (x,y))
      simpa only [ha,hb,squareMap] using hh.symm
    obtain ⟨σ,hf,hg⟩ := product_rigidity f g v hh
    exact ⟨σ,fun x=>by rw [ha,hf,hg]⟩
  · apply False.elim
    apply mismatched_axes_impossible hF hn f g u v
    · intro x y
      have hh := congrArg Prod.fst (h (x,y))
      simpa only [ha,hb,squareMap] using hh
    · intro x y
      have hh := congrArg Prod.snd (h (x,y))
      simpa only [ha,hb,squareMap] using hh

def graphPlane : (F × F) ≃+ (F × F) :=
  (AddEquiv.prodComm : (F × F) ≃+ (F × F)).trans
    ((AddEquiv.refl F).prodCongr (frobeniusEquiv F 2).toAddEquiv)

def graphCenter : (F × F) ≃+ (F × F) :=
  (AddEquiv.prodComm : (F × F) ≃+ (F × F)).trans
    ((frobeniusEquiv F 2).toAddEquiv.prodCongr (AddEquiv.refl F))

lemma graphPlane_apply (x : F × F) : graphPlane x=(x.2,x.1^2) := rfl

lemma graphCenter_apply (x : F × F) : graphCenter x=(x.2^2,x.1) := rfl

lemma graph_compatible (x : F × F) : squareMap (graphPlane x)=graphCenter (squareMap x) := by
  apply Prod.ext <;> dsimp [squareMap,graphPlane_apply,graphCenter_apply]
  all_goals ring

lemma normal_form {n : ℕ} (hF : Nat.card F=2^n) (hn : 2<n)
    (a b : (F × F) ≃+ (F × F))
    (h : ∀ x,squareMap (a x)=b (squareMap x)) :
    ∃ c d : Fˣ, ∃ σ : F ≃+* F,
      (∀ x,a x=(c*σ x.1,d*σ x.2)) ∨
      (∀ x,a x=(c*σ x.2,d*(σ x.1)^2)) := by
  rcases axis_form a (axis_maps a b h).1 with ⟨f,g,ha⟩|⟨f,g,ha⟩
  · obtain ⟨σ,hσ⟩ := preserving_rigidity hF hn a b h f g ha
    have hc : f 1≠0 := fun he => one_ne_zero (f.injective (he.trans (map_zero f).symm))
    have hd : g 1≠0 := fun he => one_ne_zero (g.injective (he.trans (map_zero g).symm))
    exact ⟨Units.mk0 (f 1) hc,Units.mk0 (g 1) hd,σ,Or.inl hσ⟩
  · let a' := a.trans (graphPlane (F:=F)).symm
    let b' := b.trans (graphCenter (F:=F)).symm
    have h' (x) : squareMap (a' x)=b' (squareMap x) := by
      apply (graphCenter (F:=F)).injective
      rw [←graph_compatible]
      change squareMap (graphPlane (graphPlane.symm (a x)))=
        graphCenter (graphCenter.symm (b (squareMap x)))
      rw [AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply,h]
    let g' := g.trans (frobeniusEquiv F 2).symm.toAddEquiv
    have ha' (x) : a' x=(g' x.1,f x.2) := by
      change graphPlane.symm (a x)=_
      apply (graphPlane (F:=F)).injective
      rw [AddEquiv.apply_symm_apply,graphPlane_apply,ha]
      refine Prod.ext ?_ ?_
      · rfl
      · exact ((frobeniusEquiv F 2).apply_symm_apply (g x.1)).symm
    obtain ⟨σ,hσ⟩ := preserving_rigidity hF hn a' b' h' g' f ha'
    have hc : f 1≠0 := fun he => one_ne_zero (f.injective (he.trans (map_zero f).symm))
    have hd : g' 1≠0 := fun he => one_ne_zero (g'.injective (he.trans (map_zero g').symm))
    refine ⟨Units.mk0 (f 1) hc,Units.mk0 ((g' 1)^2) (pow_ne_zero _ hd),σ,Or.inr ?_⟩
    intro x
    have hh := congrArg (graphPlane (F:=F)) (hσ x)
    change graphPlane (graphPlane.symm (a x))=_ at hh
    rw [AddEquiv.apply_symm_apply,graphPlane_apply,mul_pow] at hh
    exact hh


end Theory.SpecificGroups.SymplecticFour.QuotientActors
