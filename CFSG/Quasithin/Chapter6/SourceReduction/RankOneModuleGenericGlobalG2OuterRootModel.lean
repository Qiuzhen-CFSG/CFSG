module
public import Theory.AtlasPort.LinearGroups.G2.Unipotent
public import Theory.FieldTheory.ScalarTwistedFixedPoints
public import Theory.GroupAction.AutomorphismFixedSubgroup

/-!
# Fixed points of involutions preserving the six positive G₂ roots

The actual six-coordinate multiplication law forces a root-preserving
additive action to use one common field automorphism, with scalar weights
u²v³, uv³, uv², uv, u, v. If the action is an involution, the field action
is involutory. If that field action were trivial, characteristic two would
force all six weights to be one. Thus a nonidentity involution has a fixed
field of square-root order. Each scalar-twisted coordinate contributes at
most that many fixed points, giving the q³ bound.

The companion OuterCentralizer applies this calculation through the literal
right-parabolic marking. Its separate root-action premise remains explicit;
this module does not infer root preservation from an unmarked automorphism.

Source: Aschbacher–Smith F.4.37–38, printed pp.293–294 (`refs/quasithin.pdf`).
The root-coordinate formulas are the licensed ATLAS port, attributed in
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2OuterRootModel
open Atlas.G2
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] [CharP F 2] in
private theorem coordinate_product
    (a : MulAut (unipotent (K := F))) (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F, (a (unipotentEquiv v)).val =
      unipotentProduct (fun i => ρ i (v i))) (v w : Fin 6 → F) :
    (fun i => ρ i (unipotentProductParameters v w i)) =
      unipotentProductParameters (fun i => ρ i (v i)) (fun i => ρ i (w i)) := by
  have hp : unipotentEquiv (unipotentProductParameters v w) =
      unipotentEquiv v * unipotentEquiv w :=
    Subtype.ext (unipotentProduct_mul v w).symm
  have hh := congrArg (fun x : unipotent (K := F) => (a x).val) hp
  rw [map_mul] at hh
  change (a (unipotentEquiv (unipotentProductParameters v w))).val =
    (a (unipotentEquiv v)).val * (a (unipotentEquiv w)).val at hh
  rw [ha,ha,ha,unipotentProduct_mul] at hh
  exact unipotentProduct_injective hh

omit [Finite F] in
private theorem coordinate_products
    (a : MulAut (unipotent (K := F))) (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F, (a (unipotentEquiv v)).val =
      unipotentProduct (fun i => ρ i (v i))) (s t : F) :
    ρ 0 (s^2*t^3) = (ρ 4 s)^2*(ρ 5 t)^3 ∧
    ρ 1 (s*t^3) = ρ 4 s*(ρ 5 t)^3 ∧
    ρ 2 (s*t^2) = ρ 4 s*(ρ 5 t)^2 ∧
    ρ 3 (s*t) = ρ 4 s*ρ 5 t := by
  have hh := coordinate_product a ρ ha ![0,0,0,0,0,t] ![0,0,0,0,s,0]
  have h0 := congrFun hh 0
  have h1 := congrFun hh 1
  have h2 := congrFun hh 2
  have h3 := congrFun hh 3
  simp [unipotentProductParameters, CharTwo.sub_eq_add] at h0 h1 h2 h3
  exact ⟨h0,h1,h2,h3⟩

/-- Multiplication in the six actual root coordinates forces a common field
automorphism; six unrelated additive automorphisms cannot preserve this group law. -/
private theorem exists_scalar_field
    (a : MulAut (unipotent (K := F))) (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F, (a (unipotentEquiv v)).val =
      unipotentProduct (fun i => ρ i (v i))) :
    ∃ (σ : F ≃+* F) (c : Fin 6 → F), ∀ i x, ρ i x = c i * σ x := by
  let u := ρ 4 1
  let v := ρ 5 1
  have hu : u ≠ 0 := fun hh => one_ne_zero ((ρ 4).injective (hh.trans (map_zero (ρ 4)).symm))
  have hv : v ≠ 0 := fun hh => one_ne_zero ((ρ 5).injective (hh.trans (map_zero (ρ 5)).symm))
  have hprod (s t : F) := (coordinate_products a ρ ha s t).2.2.2
  have h3 (x : F) : ρ 3 x = ρ 4 x * v := by simpa only [mul_one] using hprod x 1
  have h5 (x : F) : ρ 5 x * u = ρ 4 x * v := by
    have hh := hprod 1 x
    rw [one_mul,h3] at hh
    exact (mul_comm _ _).trans hh.symm
  have hmul (s t : F) : ρ 4 (s*t) * u = ρ 4 s * ρ 4 t := by
    apply mul_right_cancel₀ hv
    calc
      ρ 4 (s*t)*u*v = (ρ 4 (s*t)*v)*u := by ring
      _ = (ρ 4 s*ρ 5 t)*u := by rw [←h3,hprod]
      _ = ρ 4 s*(ρ 5 t*u) := by ring
      _ = (ρ 4 s*ρ 4 t)*v := by rw [h5]; ring
  let σ : F ≃+* F :=
    { toFun := fun x => ρ 4 x / u
      invFun := fun x => (ρ 4).symm (u*x)
      left_inv := fun x => by
        change (ρ 4).symm (u*(ρ 4 x/u))=x
        rw [show u*(ρ 4 x/u)=ρ 4 x by field_simp]
        exact (ρ 4).symm_apply_apply x
      right_inv := fun x => by simp [hu]
      map_add' := fun x y => by rw [map_add,add_div]
      map_mul' := fun x y => by
        field_simp
        exact hmul x y }
  have h4 (x : F) : ρ 4 x = u * σ x := by dsimp [σ]; field_simp
  have h5' (x : F) : ρ 5 x = v * σ x := by
    apply mul_right_cancel₀ hu
    rw [h5,h4]
    ring
  refine ⟨σ,![u^2*v^3,u*v^3,u*v^2,u*v,u,v],?_⟩
  intro i x
  fin_cases i
  · change ρ 0 x=(u^2*v^3)*σ x
    obtain ⟨y,hy⟩ := Finite.surjective_of_injective (frobenius_inj F 2) x
    change y^2=x at hy
    rw [←hy]
    have hh := (coordinate_products a ρ ha y 1).1
    simp only [one_pow,mul_one] at hh
    rw [hh,h4,map_pow]
    change (u*σ y)^2*v^3=(u^2*v^3)*(σ y)^2
    ring
  · change ρ 1 x=(u*v^3)*σ x
    have hh := (coordinate_products a ρ ha x 1).2.1
    simp only [one_pow,mul_one] at hh
    rw [hh,h4]
    change (u*σ x)*v^3=(u*v^3)*σ x
    ring
  · change ρ 2 x=(u*v^2)*σ x
    have hh := (coordinate_products a ρ ha x 1).2.2.1
    simp only [one_pow,mul_one] at hh
    rw [hh,h4]
    change (u*σ x)*v^2=(u*v^2)*σ x
    ring
  · change ρ 3 x=(u*v)*σ x
    rw [h3,h4]
    ring
  · exact h4 x
  · exact h5' x

/-- A nonidentity involution acting separately on the six marked roots fixes
at most q³ elements of the actual unipotent group. -/
theorem fixed_card_le_cube
    (a : MulAut (unipotent (K := F))) (ρ : Fin 6 → F ≃+ F)
    (ha : ∀ v : Fin 6 → F, (a (unipotentEquiv v)).val =
      unipotentProduct (fun i => ρ i (v i)))
    (ha2 : a^2=1) (hane : a≠1) : Nat.card a.fixedSubgroup ≤ Nat.card F^3 := by
  have hact (v : Fin 6 → F) : a (unipotentEquiv v) =
      unipotentEquiv (fun i => ρ i (v i)) := Subtype.ext (ha v)
  have hrho (i : Fin 6) (x : F) : ρ i (ρ i x)=x := by
    have hh := congrArg (fun b : MulAut (unipotent (K := F)) =>
      b (unipotentEquiv (fun _ : Fin 6 => x))) ha2
    change a (a (unipotentEquiv (fun _ : Fin 6 => x))) =
      unipotentEquiv (fun _ : Fin 6 => x) at hh
    rw [hact,hact] at hh
    exact congrFun (unipotentEquiv.injective hh) i
  obtain ⟨σ,c,hc⟩ := exists_scalar_field a ρ ha
  have hcoeff (i : Fin 6) : c i * σ (c i)=1 := by
    have hh := hrho i 1
    simpa only [hc,map_one,mul_one] using hh
  have hσ : Function.Involutive σ := by
    intro x
    have hh := hrho 0 x
    rw [hc,hc,map_mul,←mul_assoc,hcoeff,one_mul] at hh
    exact hh
  have hσne : σ ≠ RingEquiv.refl F := by
    intro he
    apply hane
    have hcone (i : Fin 6) : c i=1 := by
      apply frobenius_inj F 2
      change c i^2=1^2
      have hh := hcoeff i
      simpa only [he,RingEquiv.refl_apply,pow_two,one_mul] using hh
    apply MulEquiv.ext
    intro x
    obtain ⟨v,rfl⟩ := unipotentEquiv.surjective x
    rw [hact]
    change unipotentEquiv (fun i => ρ i (v i)) = unipotentEquiv v
    congr 1
    funext i
    simp only [hc,hcone,he,RingEquiv.refl_apply,one_mul]
  let f : a.fixedSubgroup → ((i : Fin 6) → {x : F // c i * σ x=x}) := fun x i =>
    ⟨unipotentEquiv.symm x.val i, by
      have hh : a x.val=x.val := (MulAut.mem_fixedSubgroup a x.val).mp x.property
      have hp := hact (unipotentEquiv.symm x.val)
      rw [unipotentEquiv.apply_symm_apply,hh] at hp
      have hi := congrFun (congrArg unipotentEquiv.symm hp) i
      simpa only [Equiv.symm_apply_apply,hc] using hi.symm⟩
  have hf : Function.Injective f := by
    intro x y he
    apply Subtype.ext
    apply unipotentEquiv.symm.injective
    funext i
    exact congrArg Subtype.val (congrFun he i)
  calc
    Nat.card a.fixedSubgroup ≤ Nat.card ((i : Fin 6) → {x : F // c i * σ x=x}) :=
      Nat.card_le_card_of_injective f hf
    _ = ∏ i : Fin 6, Nat.card {x : F // c i * σ x=x} := Nat.card_pi
    _ ≤ ∏ _i : Fin 6, Nat.card (FixedBy.subfield F σ) :=
      Finset.prod_le_prod' (fun i _ => FiniteField.card_scalar_fixed_le σ (c i))
    _ = Nat.card (FixedBy.subfield F σ)^6 := by simp
    _ = Nat.card F^3 := by
      rw [show 6=2*3 from rfl,pow_mul,FiniteField.card_involution_fixed_sq σ hσ hσne]

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global.G2OuterRootModel
