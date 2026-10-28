module
public import Theory.Representation.ScalarMultiplicity
public import Theory.Representation.BinaryDoubledNaturalCentralizer
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.NaturalDualCohomology
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.FullLinearSelfDual

/-!
# Centralizer of two binary natural-plus-dual pairs

Schur's lemma eliminates maps between the natural and dual constituents.
Each remaining block commutes with all elementary transvections and is
therefore scalar. On two copies, these blocks give an actual binary
multiplicity representation of degree two. The original faithful centralizer
embeds in the product of the two multiplicity linear groups, so its order
divides 36. The final transport retains the original component and its
marked action on the whole normalizer orbit.

SeedAlternativesComplete applies this bound to contradict strict enlargement,
then assembles the chosen-seed source alternatives. This is the centralizer
step of Aschbacher--Smith D.3.9(1), printed p.200, as used by D.3.13 and
3.2.5, pp.202,580; refs/quasithin.pdf.
-/

public noncomputable section
open Representation Subgroup
namespace CFSG.Quasithin.Chapter3.Section02.ChosenSource325
variable {D C E F : Type*} [Group D] [Group C]
  [AddCommGroup E] [Module (ZMod 2) E]
  [AddCommGroup F] [Module (ZMod 2) F]

private theorem repeated_cross_zero
    (σ : Representation (ZMod 2) D E) (τ : Representation (ZMod 2) D F)
    (hz : ∀ f : σ.IntertwiningMap τ, f = 0)
    (f : (Fin 2 → E) →ₗ[ZMod 2] (Fin 2 → F))
    (hf : ∀ d x, f (fun i => σ d (x i)) = fun i => τ d (f x i)) : f = 0 := by
  have hb (i j : Fin 2) (v : E) : f (Pi.single j v) i = 0 := by
    let b : σ.IntertwiningMap τ := {
      toLinearMap := (LinearMap.proj i).comp (f.comp (LinearMap.single (ZMod 2) (fun _ : Fin 2 => E) j))
      isIntertwining' d := by
        apply LinearMap.ext
        intro v
        have hp : (fun k => σ d ((Pi.single j v : Fin 2 → E) k)) = Pi.single j (σ d v) := by
          funext k
          by_cases h : j = k
          · subst k; simp
          · simp [Ne.symm h]
        change f (Pi.single j (σ d v)) i = τ d (f (Pi.single j v) i)
        simpa only [hp] using congrFun (hf d (Pi.single j v)) i }
    exact congrArg (fun f : σ.IntertwiningMap τ => f v) (hz b)
  apply LinearMap.ext
  intro x
  have hx : x = ∑ j : Fin 2, Pi.single j (x j) := by ext j; simp
  rw [hx,map_sum]
  ext i
  simp [Finset.sum_apply,hb]

private theorem mixed_support_actions
    (σ : Representation (ZMod 2) D E) (τ : Representation (ZMod 2) D F)
    (hστ : ∀ f : σ.IntertwiningMap τ, f = 0)
    (hτσ : ∀ f : τ.IntertwiningMap σ, f = 0)
    (ρ : Representation (ZMod 2) C ((Fin 2 → E) × (Fin 2 → F)))
    (hc : ∀ a d x y, ρ a (fun i => σ d (x i), fun i => τ d (y i)) =
      (fun i => σ d ((ρ a (x,y)).1 i), fun i => τ d ((ρ a (x,y)).2 i))) :
    ∃ (ρ₀ : Representation (ZMod 2) C (Fin 2 → E))
      (ρ₁ : Representation (ZMod 2) C (Fin 2 → F)),
      (∀ a x y, ρ a (x,y) = (ρ₀ a x, ρ₁ a y)) ∧
      (∀ a d x, ρ₀ a (fun i => σ d (x i)) = fun i => σ d (ρ₀ a x i)) ∧
      (∀ a d x, ρ₁ a (fun i => τ d (x i)) = fun i => τ d (ρ₁ a x i)) := by
  have hl (a : C) (x : Fin 2 → E) : (ρ a (x,0)).2 = 0 := by
    let f := (LinearMap.snd (ZMod 2) (Fin 2 → E) (Fin 2 → F)).comp
      ((ρ a).comp (LinearMap.inl (ZMod 2) (Fin 2 → E) (Fin 2 → F)))
    have hf : f = 0 := repeated_cross_zero σ τ hστ f (by
      intro d x
      change (ρ a (fun i => σ d (x i),0)).2 = fun i => τ d ((ρ a (x,0)).2 i)
      simpa only [Pi.zero_apply,map_zero,←Pi.zero_def] using congrArg Prod.snd (hc a d x 0))
    exact LinearMap.congr_fun hf x
  have hr (a : C) (y : Fin 2 → F) : (ρ a (0,y)).1 = 0 := by
    let f := (LinearMap.fst (ZMod 2) (Fin 2 → E) (Fin 2 → F)).comp
      ((ρ a).comp (LinearMap.inr (ZMod 2) (Fin 2 → E) (Fin 2 → F)))
    have hf : f = 0 := repeated_cross_zero τ σ hτσ f (by
      intro d x
      change (ρ a (0,fun i => τ d (x i))).1 = fun i => σ d ((ρ a (0,x)).1 i)
      simpa only [Pi.zero_apply,map_zero,←Pi.zero_def] using congrArg Prod.fst (hc a d 0 x))
    exact LinearMap.congr_fun hf y
  let T₀ (a : C) : Module.End (ZMod 2) (Fin 2 → E) :=
    (LinearMap.fst (ZMod 2) (Fin 2 → E) (Fin 2 → F)).comp
      ((ρ a).comp (LinearMap.inl (ZMod 2) (Fin 2 → E) (Fin 2 → F)))
  let T₁ (a : C) : Module.End (ZMod 2) (Fin 2 → F) :=
    (LinearMap.snd (ZMod 2) (Fin 2 → E) (Fin 2 → F)).comp
      ((ρ a).comp (LinearMap.inr (ZMod 2) (Fin 2 → E) (Fin 2 → F)))
  have hd (a : C) (x : Fin 2 → E) (y : Fin 2 → F) : ρ a (x,y) = (T₀ a x, T₁ a y) := by
    have hadd : ρ a (x,y) = ρ a (x,0) + ρ a (0,y) := by
      simpa using (ρ a).map_add (x,0) (0,y)
    apply Prod.ext
    · change (ρ a (x,y)).1 = (ρ a (x,0)).1
      rw [hadd]
      change (ρ a (x,0)).1 + (ρ a (0,y)).1 = _
      rw [hr, add_zero]
    · change (ρ a (x,y)).2 = (ρ a (0,y)).2
      rw [hadd]
      change (ρ a (x,0)).2 + (ρ a (0,y)).2 = _
      rw [hl, zero_add]
  let ρ₀ : Representation (ZMod 2) C (Fin 2 → E) := {
    toFun := T₀
    map_one' := by
      apply LinearMap.ext
      intro x
      change (ρ 1 (x,0)).1 = x
      simp only [map_one, Module.End.one_apply]
    map_mul' a b := by
      apply LinearMap.ext
      intro x
      change (ρ (a*b) (x,0)).1 = (ρ a ((ρ b (x,0)).1,0)).1
      rw [map_mul, Module.End.mul_apply, hd b x 0]
      simp only [map_zero] }
  let ρ₁ : Representation (ZMod 2) C (Fin 2 → F) := {
    toFun := T₁
    map_one' := by
      apply LinearMap.ext
      intro x
      change (ρ 1 (0,x)).2 = x
      simp only [map_one, Module.End.one_apply]
    map_mul' a b := by
      apply LinearMap.ext
      intro x
      change (ρ (a*b) (0,x)).2 = (ρ a (0,(ρ b (0,x)).2)).2
      rw [map_mul, Module.End.mul_apply, hd b 0 x]
      simp only [map_zero] }
  refine ⟨ρ₀,ρ₁,hd,?_,?_⟩
  · intro a d x
    change (ρ a (fun i => σ d (x i),0)).1 = fun i => σ d ((ρ a (x,0)).1 i)
    have hh := congrArg Prod.fst (hc a d x 0)
    simpa only [map_one, Module.End.one_apply, Pi.zero_apply, map_zero, ← Pi.zero_def] using hh
  · intro a d x
    change (ρ a (0,fun i => τ d (x i))).2 = fun i => τ d ((ρ a (0,x)).2 i)
    have hh := congrArg Prod.snd (hc a d 0 x)
    simpa only [map_one, Module.End.one_apply, Pi.zero_apply, map_zero, ← Pi.zero_def] using hh

private theorem eq_of_multiplicity_eq
    (ρ : Representation (ZMod 2) C (Fin 2 → E)) (μ : Representation (ZMod 2) C (Fin 2 → ZMod 2))
    (he : ∀ a c v, ρ a (fun i => c i • v) = fun i => μ a c i • v)
    (a b : C) (hab : μ a = μ b) : ρ a = ρ b := by
  apply LinearMap.ext
  intro x
  have hexp : x = ∑ i : Fin 2, Pi.single i (x i) := by ext i; simp
  rw [hexp, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hsing (v : E) : (fun j => (Pi.single i (1 : ZMod 2) : Fin 2 → ZMod 2) j • v) =
      Pi.single i v := by
    funext j
    by_cases h : i = j
    · subst j; simp
    · simp [Ne.symm h]
  rw [← hsing (x i), he, he, hab]


/-- Two copies of each distinct absolutely simple binary constituent have
centralizer order dividing 36, with a faithful original commuting actor. -/
theorem mixed_double_centralizer_card_dvd
    [Finite C] [Nontrivial E] [Nontrivial F]
    (σ : Representation (ZMod 2) D E) (τ : Representation (ZMod 2) D F)
    (hστ : ∀ f : σ.IntertwiningMap τ, f = 0)
    (hτσ : ∀ f : τ.IntertwiningMap σ, f = 0)
    (hs : ∀ (f : E →ₗ[ZMod 2] E), (∀ d v, f (σ d v) = σ d (f v)) →
      ∃ c : ZMod 2, ∀ v, f v = c • v)
    (ht : ∀ (f : F →ₗ[ZMod 2] F), (∀ d v, f (τ d v) = τ d (f v)) →
      ∃ c : ZMod 2, ∀ v, f v = c • v)
    (ρ : Representation (ZMod 2) C ((Fin 2 → E) × (Fin 2 → F)))
    (hfaith : Function.Injective ρ)
    (hc : ∀ a d x y, ρ a (fun i => σ d (x i), fun i => τ d (y i)) =
      (fun i => σ d ((ρ a (x,y)).1 i), fun i => τ d ((ρ a (x,y)).2 i))) :
    Nat.card C ∣ 36 := by
  obtain ⟨ρ₀,ρ₁,hd,h₀,h₁⟩ := mixed_support_actions σ τ hστ hτσ ρ hc
  obtain ⟨μ₀,he₀⟩ := ScalarMultiplicity.exists_multiplicity σ hs ρ₀ h₀
  obtain ⟨μ₁,he₁⟩ := ScalarMultiplicity.exists_multiplicity τ ht ρ₁ h₁
  let f := μ₀.asGroupHom.prod μ₁.asGroupHom
  have hf : Function.Injective f := by
    intro a b hab
    apply hfaith
    apply LinearMap.ext
    rintro ⟨x,y⟩
    rw [hd,hd]
    have h₀ab : μ₀ a = μ₀ b := congrArg Units.val (congrArg Prod.fst hab)
    have h₁ab : μ₁ a = μ₁ b := congrArg Units.val (congrArg Prod.snd hab)
    rw [eq_of_multiplicity_eq ρ₀ μ₀ he₀ a b h₀ab,
      eq_of_multiplicity_eq ρ₁ μ₁ he₁ a b h₁ab]
  have hb := Subgroup.card_dvd_of_injective f hf
  let e := (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin 2 → ZMod 2)).trans
    BinaryLinear.SmallParabolicLevi.linearTwoEquivSymmetricThree
  have he : Nat.card (Module.End (ZMod 2) (Fin 2 → ZMod 2))ˣ = 6 := by
    rw [Nat.card_congr e.toEquiv,Nat.card_perm,Nat.card_fin]
    rfl
  simpa only [Nat.card_prod,he] using hb

open ChapterB.QuasisimpleSource
open Representation.BinaryOffender
open scoped MatrixGroups

private theorem scalar_of_actionEquiv
    {D₁ D₂ E₁ E₂ : Type*} [Group D₁] [Group D₂]
    [AddCommGroup E₁] [Module (ZMod 2) E₁] [AddCommGroup E₂] [Module (ZMod 2) E₂]
    {σ : Representation (ZMod 2) D₁ E₁} {τ : Representation (ZMod 2) D₂ E₂}
    (a : ActionEquiv σ τ)
    (ht : ∀ (f : E₂ →ₗ[ZMod 2] E₂), (∀ d v, f (τ d v) = τ d (f v)) →
      ∃ c : ZMod 2, ∀ v, f v = c • v)
    (f : E₁ →ₗ[ZMod 2] E₁) (hf : ∀ d v, f (σ d v) = σ d (f v)) :
    ∃ c : ZMod 2, ∀ v, f v = c • v := by
  let F := a.linearEquiv.toLinearMap.comp (f.comp a.linearEquiv.symm.toLinearMap)
  have hF : ∀ d v, F (τ d v) = τ d (F v) := by
    intro d v
    obtain ⟨g,rfl⟩ := a.groupEquiv.surjective d
    obtain ⟨w,rfl⟩ := a.linearEquiv.surjective v
    change a.linearEquiv (f (a.linearEquiv.symm (τ (a.groupEquiv g) (a.linearEquiv w)))) =
      τ (a.groupEquiv g) (a.linearEquiv (f (a.linearEquiv.symm (a.linearEquiv w))))
    rw [←a.intertwines,a.linearEquiv.symm_apply_apply,a.linearEquiv.symm_apply_apply,hf,a.intertwines]
  obtain ⟨c,hc⟩ := ht F hF
  refine ⟨c,fun v => a.linearEquiv.injective ?_⟩
  have hh := hc (a.linearEquiv v)
  simpa only [F,LinearMap.comp_apply,LinearEquiv.coe_coe,a.linearEquiv.symm_apply_apply,map_smul] using hh

private theorem binary_natural_not_dual {d : ℕ} (hd : 3 ≤ d) :
    ¬ Nonempty ((linearNatural BinaryField.two d).Equiv (linearNatural BinaryField.two d).dual) := by
  rintro ⟨e⟩
  apply binary_not_surjective_of_selfDual (linearNatural BinaryField.two d) (by change 3 ≤ Module.finrank (ZMod 2) (Fin d → ZMod 2); simpa using hd) e
  intro g
  let l := LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Fin d → ZMod 2)
  obtain ⟨x,hx⟩ := (BinaryLinear.OuterCyclic.slEquivLinear d).surjective (l g)
  refine ⟨x,l.injective ?_⟩
  rw [←hx]
  apply LinearEquiv.ext
  intro v
  exact (BinaryLinear.OuterCyclic.slEquivLinear_apply d x v).symm

/-- The concrete mixed binary multiplicity action has the required order bound. -/
theorem binary_mixed_double_card_dvd
    {d : ℕ} (hd : 3 ≤ d) [Finite C]
    (ρ : Representation (ZMod 2) C
      ((Fin 2 → Fin d → ZMod 2) × (Fin 2 → Module.Dual (ZMod 2) (Fin d → ZMod 2))))
    (hf : Function.Injective ρ)
    (hc : ∀ a g x y, ρ a
      (fun i => linearNatural BinaryField.two d g (x i),
        fun i => (linearNatural BinaryField.two d).dual g (y i)) =
      (fun i => linearNatural BinaryField.two d g ((ρ a (x,y)).1 i),
        fun i => (linearNatural BinaryField.two d).dual g ((ρ a (x,y)).2 i))) :
    Nat.card C ∣ 36 := by
  let : NeZero d := ⟨by omega⟩
  let σ := linearNatural BinaryField.two d
  let τ := σ.dual
  let := ExtensionConsequences.linearNatural_irreducible BinaryField.two (by omega : 2 ≤ d)
  let := ExtensionConsequences.irreducible_of_equiv (dualNaturalEquiv d)
    (ExtensionConsequences.linearNatural_irreducible BinaryField.two (by omega : 2 ≤ d))
  have hz₁ : ∀ f : σ.IntertwiningMap τ, f = 0 := by
    intro f
    rcases IsIrreducible.bijective_or_eq_zero f with hb | hz
    · exact (binary_natural_not_dual hd ⟨f.ofBijective hb⟩).elim
    · exact hz
  have hz₂ : ∀ f : τ.IntertwiningMap σ, f = 0 := by
    intro f
    rcases IsIrreducible.bijective_or_eq_zero f with hb | hz
    · exact (binary_natural_not_dual hd ⟨(f.ofBijective hb).symm⟩).elim
    · exact hz
  have hs : ∀ (f : (Fin d → ZMod 2) →ₗ[ZMod 2] (Fin d → ZMod 2)),
      (∀ g v, f (σ g v) = σ g (f v)) → ∃ c : ZMod 2, ∀ v, f v = c • v := by
    intro f hf
    exact BinaryDoubledNatural.natural_centralizer_scalar (by omega : 2 ≤ d) f.toAddMonoidHom hf
  exact mixed_double_centralizer_card_dvd σ τ hz₁ hz₂ hs
    (fun f hf => scalar_of_actionEquiv (dualNaturalEquiv d) hs f hf) ρ hf hc


private def pairReorder (d : ℕ) :
    (((Fin d → ZMod 2) × Module.Dual (ZMod 2) (Fin d → ZMod 2)) ×
      ((Fin d → ZMod 2) × Module.Dual (ZMod 2) (Fin d → ZMod 2))) ≃ₗ[ZMod 2]
    ((Fin 2 → Fin d → ZMod 2) × (Fin 2 → Module.Dual (ZMod 2) (Fin d → ZMod 2))) :=
  (LinearEquiv.prodProdProdComm (ZMod 2) _ _ _ _).trans
    ((LinearEquiv.finTwoArrow (ZMod 2) (Fin d → ZMod 2)).symm.prodCongr
      (LinearEquiv.finTwoArrow (ZMod 2) (Module.Dual (ZMod 2) (Fin d → ZMod 2))).symm)

private theorem pairReorder_action (d : ℕ) (g : SL(d,ZMod 2)) (v) :
    pairReorder d (((naturalPlusDual d).prod (naturalPlusDual d)) g v) =
      (fun i => linearNatural BinaryField.two d g ((pairReorder d v).1 i),
        fun i => (linearNatural BinaryField.two d).dual g ((pairReorder d v).2 i)) := by
  apply Prod.ext <;> funext i <;> fin_cases i <;> rfl

/-- The actual centralizer of a faithfully marked double natural-plus-dual
component has order dividing 36. The group marking is retained throughout. -/
theorem binary_double_component_centralizer_card_dvd
    {H X : Type*} [Group H] [Finite H] [AddCommGroup X] [Module (ZMod 2) X]
    (ρ : Representation (ZMod 2) H X) (hf : Function.Injective ρ)
    (K : Subgroup H) {d : ℕ} (hd : 3 ≤ d)
    (a : ActionEquiv (ρ.comp K.subtype) ((naturalPlusDual d).prod (naturalPlusDual d))) :
    Nat.card (centralizer (K : Set H)) ∣ 36 := by
  let C := centralizer (K : Set H)
  let e := a.linearEquiv.trans (pairReorder d)
  let β : Representation (ZMod 2) C
      ((Fin 2 → Fin d → ZMod 2) × (Fin 2 → Module.Dual (ZMod 2) (Fin d → ZMod 2))) :=
    (e.conjAlgEquiv (ZMod 2)).toAlgHom.toMonoidHom.comp (ρ.comp C.subtype)
  have hb (c : C) (v) : β c v = e (ρ c.val (e.symm v)) := rfl
  have hβ : Function.Injective β := by
    intro c b hcb
    apply Subtype.ext
    apply hf
    apply LinearMap.ext
    intro v
    apply e.injective
    have hh := LinearMap.congr_fun hcb (e v)
    simpa only [hb,e.symm_apply_apply] using hh
  have he (k : K) (v : X) : e (ρ k.val v) =
      (fun i => linearNatural BinaryField.two d (a.groupEquiv k) ((e v).1 i),
        fun i => (linearNatural BinaryField.two d).dual (a.groupEquiv k) ((e v).2 i)) :=
    (congrArg (pairReorder d) (a.intertwines k v)).trans (pairReorder_action d _ _)
  have hcomm (c : C) (k : K) (v : X) : ρ c.val (ρ k.val v) = ρ k.val (ρ c.val v) := by
    have hh := congrArg ρ (mem_centralizer_iff.mp c.property k.val k.property).symm
    simpa only [map_mul,Module.End.mul_apply] using LinearMap.congr_fun hh v
  apply binary_mixed_double_card_dvd hd β hβ
  intro c g x y
  obtain ⟨k,rfl⟩ := a.groupEquiv.surjective g
  rw [hb,hb]
  have hpre : e.symm
      (fun i => linearNatural BinaryField.two d (a.groupEquiv k) (x i),
        fun i => (linearNatural BinaryField.two d).dual (a.groupEquiv k) (y i)) =
      ρ k.val (e.symm (x,y)) := by
    apply e.injective
    rw [e.apply_symm_apply,he,e.apply_symm_apply]
    rfl
  rw [hpre,hcomm,he]

end CFSG.Quasithin.Chapter3.Section02.ChosenSource325
