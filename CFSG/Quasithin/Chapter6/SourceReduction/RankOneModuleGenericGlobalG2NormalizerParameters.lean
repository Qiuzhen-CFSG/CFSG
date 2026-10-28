module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalG2RootNormalization
public import Theory.FieldTheory.FiniteAutomorphismOrder

/-!
# Counting the compatible six-root actions

The E,F product in the unique positive-root chart determines four mixed
parameter products. After dividing the two simple-root maps by their values
at one, these identities force one common field automorphism. Surjectivity
of squaring recovers the highest root as well, including over the four-element
field. Thus a faithful family of root-preserving actions has at most
(q-1)^2 n members when q=2^n.

The companion NormalizerOrder module applies this to conjugation by the
original Sylow/torus normalizer. No extension of a local automorphism to
the full G₂ model is assumed. Native root identities retain the attribution
and license in LICENSES/ATLAS.txt.
Source: the local extension and order steps of Aschbacher–Smith F.4.29,
F.4.43–44, printed pp.289,296, and 5.3.2–4, p.659 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup
open scoped CharTwo
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2NormalizerOrder
variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
private theorem parameter_products
    (a : MulAut (unipotent (K := F))) (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F,
      (a (unipotentEquiv v)).val = unipotentProduct (fun i => ρ i (v i)))
    (s t : F) :
    ρ 0 (s^2*t^3) = (ρ 4 s)^2*(ρ 5 t)^3 ∧
    ρ 1 (s*t^3) = ρ 4 s*(ρ 5 t)^3 ∧
    ρ 2 (s*t^2) = ρ 4 s*(ρ 5 t)^2 ∧
    ρ 3 (s*t) = ρ 4 s*ρ 5 t := by
  let x : Fin 6 → F := ![0,0,0,0,0,t]
  let y : Fin 6 → F := ![0,0,0,0,s,0]
  have hm : unipotentEquiv x * unipotentEquiv y =
      unipotentEquiv (unipotentProductParameters x y) :=
    Subtype.ext (unipotentProduct_mul x y)
  have hh := congrArg (fun u : unipotent (K := F) => (a u).val) hm
  rw [map_mul] at hh
  change (a (unipotentEquiv x)).val * (a (unipotentEquiv y)).val = _ at hh
  rw [ha,ha,ha,unipotentProduct_mul] at hh
  have he := unipotentProduct_injective hh
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  have h3 := congrFun he 3
  simp [x,y,unipotentProductParameters] at h0 h1 h2 h3
  exact ⟨h0.symm,h1.symm,h2.symm,h3.symm⟩

private theorem parameter_form
    (a : MulAut (unipotent (K := F))) (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F,
      (a (unipotentEquiv v)).val = unipotentProduct (fun i => ρ i (v i))) :
    ∃ (u v : Fˣ) (σ : F ≃+* F), ∀ (i : Fin 6) (x : F),
      ρ i x = (RootDiagonal.character u v ⟨i.val,by omega⟩ : F) * σ x := by
  have hp := parameter_products a ρ ha
  have he : ρ 4 1 ≠ 0 := fun hh => one_ne_zero ((ρ 4).injective (hh.trans (map_zero _).symm))
  have hf : ρ 5 1 ≠ 0 := fun hh => one_ne_zero ((ρ 5).injective (hh.trans (map_zero _).symm))
  have hm (s t : F) : ρ 4 1 * ρ 4 (s*t) = ρ 4 s * ρ 4 t := by
    apply mul_right_cancel₀ hf
    calc
      (ρ 4 1 * ρ 4 (s*t)) * ρ 5 1 = ρ 4 1 * ρ 3 (s*t) := by
        rw [(show ρ 3 (s*t) = ρ 4 (s*t)*ρ 5 1 by simpa using (hp (s*t) 1).2.2.2)]
        ring
      _ = ρ 4 s * (ρ 4 1 * ρ 5 t) := by rw [(hp s t).2.2.2]; ring
      _ = ρ 4 s * (ρ 4 t * ρ 5 1) := by
        rw [←(show ρ 3 t = ρ 4 1 * ρ 5 t by simpa using (hp 1 t).2.2.2),
          (show ρ 3 t = ρ 4 t * ρ 5 1 by simpa using (hp t 1).2.2.2)]
      _ = _ := by ring
  let σ : F ≃+* F :=
    { toFun := fun x => (ρ 4 1)⁻¹ * ρ 4 x
      invFun := fun x => (ρ 4).symm (ρ 4 1 * x)
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_add' := by intro x y; rw [map_add,mul_add]
      map_mul' := by
        intro s t
        apply mul_left_cancel₀ (pow_ne_zero 2 he)
        field_simp
        exact hm s t }
  let u : Fˣ := Units.mk0 (ρ 5 1) hf
  let v : Fˣ := Units.mk0 (ρ 4 1) he
  have h4 (x : F) : ρ 4 x = (v:F) * σ x := by
    dsimp [v,σ]
    rw [mul_inv_cancel_left₀ he]
  have h5 (x : F) : ρ 5 x = (u:F) * σ x := by
    apply mul_left_cancel₀ he
    calc
      ρ 4 1 * ρ 5 x = ρ 4 x * ρ 5 1 :=
        (show ρ 3 x = ρ 4 1 * ρ 5 x by simpa using (hp 1 x).2.2.2).symm.trans
          (by simpa using (hp x 1).2.2.2)
      _ = _ := by rw [h4]; change (v:F)*σ x*(u:F) = (v:F)*((u:F)*σ x); ring
  have h3 (x : F) : ρ 3 x = (v:F)*(u:F)*σ x := by
    have hh := (hp x 1).2.2.2
    rw [mul_one,h4,h5,map_one] at hh
    convert hh using 1; ring
  have h2 (x : F) : ρ 2 x = (v:F)*(u:F)^2*σ x := by
    have hh := (hp x 1).2.2.1
    rw [one_pow,mul_one,h4,h5,map_one] at hh
    convert hh using 1; ring
  have h1 (x : F) : ρ 1 x = (v:F)*(u:F)^3*σ x := by
    have hh := (hp x 1).2.1
    rw [one_pow,mul_one,h4,h5,map_one] at hh
    convert hh using 1; ring
  have h0 (x : F) : ρ 0 x = (v:F)^2*(u:F)^3*σ x := by
    obtain ⟨s,hs⟩ := Finite.surjective_of_injective (frobenius_inj F 2) x
    change s^2=x at hs
    have hh := (hp s 1).1
    rw [one_pow,mul_one,h4,h5,map_one] at hh
    rw [←hs,map_pow σ]
    convert hh using 1; ring
  refine ⟨u,v,σ,?_⟩
  intro i x
  fin_cases i <;> simp only [RootDiagonal.character, Matrix.cons_val,Fin.reduceFinMk,
    Units.val_mul,Units.val_pow_eq_pow_val] <;>
    first | exact (h0 x).trans (by ring) | exact (h1 x).trans (by ring)
          | exact (h2 x).trans (by ring) | exact (h3 x).trans (by ring)
          | exact h4 x | exact h5 x

/-- The two simple root scalars and a single field automorphism determine
every root-preserving action on the positive unipotent group. -/
theorem card_le_of_root_actions {A : Type*} [Finite A]
    (f : A → MulAut (unipotent (K := F))) (hf : Function.Injective f)
    (hact : ∀ a, ∃ ρ : Fin 6 → F ≃+ F, ∀ v : Fin 6 → F,
      (f a (unipotentEquiv v)).val = unipotentProduct (fun i => ρ i (v i)))
    {n : ℕ} (hF : Nat.card F = 2^n) : Nat.card A ≤ (Nat.card F-1)^2*n := by
  choose ρ hρ using hact
  choose u v σ hσ using fun a => parameter_form (f a) (ρ a) (hρ a)
  let code : A → Fˣ × Fˣ × (F ≃+* F) := fun a => (u a,v a,σ a)
  have hinj : Function.Injective code := by
    intro a b hab
    have hu : u a = u b := congrArg Prod.fst hab
    have hv : v a = v b := congrArg (fun x => x.2.1) hab
    have hs : σ a = σ b := congrArg (fun x => x.2.2) hab
    apply hf
    apply MulEquiv.ext
    intro x
    obtain ⟨p,rfl⟩ := unipotentEquiv.surjective x
    apply Subtype.ext
    rw [hρ,hρ]
    congr 1
    funext i
    rw [hσ,hσ,hu,hv,hs]
  let : Finite (F ≃+* F) := Finite.of_injective
    (fun a : F ≃+* F => (a : F → F)) DFunLike.coe_injective
  have hh := Nat.card_le_card_of_injective code hinj
  simpa only [Nat.card_prod,Nat.card_units,
    FiniteField.card_ringAut_of_card_prime_pow Nat.prime_two hF,pow_two,mul_assoc] using hh

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2NormalizerOrder
