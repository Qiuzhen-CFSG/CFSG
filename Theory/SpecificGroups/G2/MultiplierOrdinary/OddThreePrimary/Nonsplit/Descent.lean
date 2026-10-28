module
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit.Lang
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit.Sylow
import all Theory.SpecificGroups.G2.MultiplierOrdinary.OddThreePrimary.Split
import all Theory.SpecificGroups.G2.MultiplierOrdinary.OddSplitTorus

/-!
# Rational descent of the nonsplit torus and its Weyl normalizer

For a solution Frob(u)=u·w₀, conjugation by u takes the product of two
norm-one groups into the Frobenius-fixed octonion automorphisms. The Weyl
cycle, the reflection swapping the torus parameters, and w₀ itself commute
with w₀ and descend through the same conjugation. The coefficient-field
embedding is injective, so their multiplication and conjugation equations
descend literally. The nonsplit torus index argument then constructs
`LocalData F`, including its full Sylow three-subgroup.

The only extra premise is the single Lang equation. `Nonsplit.Lang` constructs
its witness and the parent `Nonsplit` module discharges this premise.
No identification of an abstract unitary group with an octonion subgroup is
assumed. The internal imports reuse the already checked Weyl identities
without changing the split branch's public interface.

Source: the ordinary G₂ entry underlying Aschbacher–Smith I.1.1–I.1.4,
printed pp.407–408, and GLS III §6.1. The model and Weyl maps are attributed
ATLAS ports; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
namespace Atlas.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit
open Subgroup Atlas.SplitOctonion PRegularClasses.FieldExtension PRegularClasses.RationalFusion
noncomputable section
variable {F : Type*} [Field F]

private theorem fieldEmbedding_torus {K : Type*} [Field K] (f : F →+* K) (l m : Fˣ) :
    fieldEmbedding f (torus l m) = torus (Units.map f.toMonoidHom l) (Units.map f.toMonoidHom m) := by
  have hc (x : Carrier F) : coeffMap f ((torus l m : Model F).val x) =
      (torus (Units.map f.toMonoidHom l) (Units.map f.toMonoidHom m) : Model K).val (coeffMap f x) := by
    ext i
    fin_cases i <;> simp [coeffMap,torus,torusEquiv,torusLinear,torusWeights]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (fieldEmbedding f (torus l m)).val (basisVector j) = _
  rw [fieldEmbedding_basis]
  have hj := hc (basisVector j)
  rw [coeffMap_basisVector] at hj
  simpa only [basisVector,LinearEquiv.coe_coe] using hj

private theorem fieldEmbedding_weylR {K : Type*} [Field K] (f : F →+* K) :
    fieldEmbedding f weylR = weylR := by
  have hc (x : Carrier F) : coeffMap f ((weylR : Model F).val x) =
      (weylR : Model K).val (coeffMap f x) := by
    ext i
    fin_cases i <;> simp [coeffMap,weylR,weylREquiv,weylRLinear,weylRApply]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (fieldEmbedding f (weylR)).val (basisVector j) = _
  rw [fieldEmbedding_basis]
  have hj := hc (basisVector j)
  rw [coeffMap_basisVector] at hj
  simpa only [basisVector,LinearEquiv.coe_coe] using hj

private theorem fieldEmbedding_weylS {K : Type*} [Field K] (f : F →+* K) :
    fieldEmbedding f weylS = weylS := by
  have hc (x : Carrier F) : coeffMap f ((weylS : Model F).val x) =
      (weylS : Model K).val (coeffMap f x) := by
    ext i
    fin_cases i <;> simp [coeffMap,weylS,weylSEquiv,weylSLinear,weylSApply]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (fieldEmbedding f (weylS)).val (basisVector j) = _
  rw [fieldEmbedding_basis]
  have hj := hc (basisVector j)
  rw [coeffMap_basisVector] at hj
  simpa only [basisVector,LinearEquiv.coe_coe] using hj

private theorem longestWeyl_commutes_swap : Commute (longestWeyl : Model F) weylS := by
  change longestWeyl * weylS = weylS * longestWeyl
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [longestWeyl,pow_succ,weylR,weylS,weylREquiv,weylSEquiv,
    weylRLinear,weylSLinear,weylRApply,weylSApply]

variable [Finite F]
private def descend (x : Model (AlgebraicClosure F)) (hx : frobenius F x = x) : Model F :=
  Classical.choose ((frobenius_fixed_iff F x).mp hx)

private theorem embedding_descend (x : Model (AlgebraicClosure F)) (hx : frobenius F x = x) :
    fieldEmbedding (algebraMap F (AlgebraicClosure F)) (descend x hx) = x :=
  Classical.choose_spec ((frobenius_fixed_iff F x).mp hx)

private def descendHom {A : Type*} [Group A] (ρ : A →* Model (AlgebraicClosure F))
    (hρ : ∀ a, frobenius F (ρ a) = ρ a) : A →* Model F where
  toFun a := descend (ρ a) (hρ a)
  map_one' := by
    apply fieldEmbedding_injective (algebraMap F (AlgebraicClosure F))
    simp only [embedding_descend,map_one]
  map_mul' a b := by
    apply fieldEmbedding_injective (algebraMap F (AlgebraicClosure F))
    simp only [embedding_descend,map_mul]

private theorem embedding_descendHom {A : Type*} [Group A] (ρ : A →* Model (AlgebraicClosure F))
    (hρ : ∀ a, frobenius F (ρ a) = ρ a) (a : A) :
    fieldEmbedding (algebraMap F (AlgebraicClosure F)) (descendHom ρ hρ a) = ρ a :=
  embedding_descend (ρ a) (hρ a)

private theorem conjugate_fixed (u g : Model (AlgebraicClosure F))
    (hu : frobenius F u = u * longestWeyl)
    (hg : longestWeyl * frobenius F g * longestWeyl⁻¹ = g) :
    frobenius F (u*g*u⁻¹) = u*g*u⁻¹ := by
  rw [map_mul,map_mul,map_inv,hu]
  calc
    _ = u * (longestWeyl * frobenius F g * longestWeyl⁻¹) * u⁻¹ := by group
    _ = _ := by rw [hg]

private def rootTorus {K : Type*} [Field K] (n : ℕ) :
    rootsOfUnity n K × rootsOfUnity n K →* Model K where
  toFun a := torus a.1.val a.2.val
  map_one' := torusHom.map_one
  map_mul' a b := torusHom.map_mul (a.1.val,a.2.val) (b.1.val,b.2.val)

private theorem rootTorus_injective {K : Type*} [Field K] (n : ℕ) :
    Function.Injective (rootTorus (K := K) n) := by
  intro a b h
  have hp : (a.1.val,a.2.val) = (b.1.val,b.2.val) :=
    torusHom_injective (K := K) h
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hp)) (Subtype.ext (congrArg Prod.snd hp))

private theorem descendHom_injective {A : Type*} [Group A]
    (ρ : A →* Model (AlgebraicClosure F)) (hρ : ∀ a, frobenius F (ρ a) = ρ a)
    (hi : Function.Injective ρ) : Function.Injective (descendHom ρ hρ) := by
  intro a b hab
  apply hi
  have he := congrArg (fieldEmbedding (algebraMap F (AlgebraicClosure F))) hab
  simpa only [embedding_descendHom] using he

private theorem conjugated_torus_fixed {p : ℕ} [CharP F p]
    (hF : Nat.card F = p) (u : Model (AlgebraicClosure F))
    (hu : frobenius F u = u * longestWeyl)
    (l m : rootsOfUnity (p+1) (AlgebraicClosure F)) :
    frobenius F (u * torus l.val m.val * u⁻¹) = u * torus l.val m.val * u⁻¹ := by
  let := Fintype.ofFinite F
  let K := AlgebraicClosure F
  have hCpow (a : rootsOfUnity (p+1) K) : (a.val)^p = a.val⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact (mem_rootsOfUnity _ _).mp a.property
  have hCfrob (a : rootsOfUnity (p+1) K) :
      Units.map (FiniteField.frobeniusAlgHom F K).toRingHom.toMonoidHom a.val = a.val⁻¹ := by
    apply Units.ext
    change (a.val : K)^Fintype.card F = _
    rw [← Nat.card_eq_fintype_card,hF]
    exact congrArg Units.val (hCpow a)
  apply conjugate_fixed u _ hu
  change longestWeyl * fieldEmbedding (FiniteField.frobeniusAlgHom F K).toRingHom
    (torus l.val m.val) * longestWeyl⁻¹ = torus l.val m.val
  rw [fieldEmbedding_torus,hCfrob,hCfrob]
  have hi : torus l.val⁻¹ m.val⁻¹ = (torus l.val m.val)⁻¹ :=
    map_inv torusHom (l.val,m.val)
  change inverter * torus l.val⁻¹ m.val⁻¹ * inverter⁻¹ = _
  rw [inverter_torus,hi,inv_inv]

private theorem conjugated_fixed_of_commute (u g : Model (AlgebraicClosure F))
    (hu : frobenius F u = u * longestWeyl)
    (hf : frobenius F g = g) (hw : Commute longestWeyl g) :
    frobenius F (u*g*u⁻¹) = u*g*u⁻¹ := by
  apply conjugate_fixed u g hu
  rw [hf,hw.eq,mul_assoc,mul_inv_cancel,mul_one]

/-- A solution of the single longest-Weyl Lang equation supplies the actual
nonsplit torus, all rational normalizers, and the full Sylow configuration. -/
theorem exists_localData_of_lang {p : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = p) (hd : 3 ∣ p+1)
    (u : Model (AlgebraicClosure F)) (hu : frobenius F u = u * longestWeyl) :
    Nonempty (LocalData F) := by
  let := Fintype.ofFinite F
  let K := AlgebraicClosure F
  let C : Type _ := rootsOfUnity (p+1) K
  let e := fieldEmbedding (algebraMap F K)
  let D := (MulAut.conj u).toMonoidHom
  let ρ : C × C →* Model K := D.comp (rootTorus (p+1))
  have hρ (a : C × C) : frobenius F (ρ a) = ρ a :=
    conjugated_torus_fixed hF u hu a.1 a.2
  let ι := descendHom ρ hρ
  have hι (a : C × C) : e (ι a) = D (torus a.1.val a.2.val) := embedding_descendHom ρ hρ a
  have hιinj : Function.Injective ι := descendHom_injective ρ hρ
    ((MulAut.conj u).injective.comp (rootTorus_injective (K := K) (p+1)))
  let c₀ : Model K := (weylR*weylS)^2
  have hc₀ : frobenius F c₀ = c₀ := by
    change fieldEmbedding _ ((weylR*weylS)^2) = _
    rw [map_pow,map_mul,fieldEmbedding_weylR,fieldEmbedding_weylS]
  have hs₀ : frobenius F (weylS : Model K) = weylS := fieldEmbedding_weylS _
  have hw₀ : frobenius F (longestWeyl : Model K) = longestWeyl := by
    change fieldEmbedding _ ((weylR*weylS)^3) = (weylR*weylS)^3
    rw [map_pow,map_mul,fieldEmbedding_weylR,fieldEmbedding_weylS]
  have hcw : Commute (longestWeyl : Model K) c₀ := (Commute.refl (weylR*weylS)).pow_pow 3 2
  let c := descend (D c₀) (conjugated_fixed_of_commute u c₀ hu hc₀ hcw)
  let s := descend (D weylS) (conjugated_fixed_of_commute u weylS hu hs₀ longestWeyl_commutes_swap)
  let w := descend (D longestWeyl) (conjugated_fixed_of_commute u longestWeyl hu hw₀ (Commute.refl _))
  have hec : e c = D c₀ := embedding_descend (D c₀)
    (conjugated_fixed_of_commute u c₀ hu hc₀ hcw)
  have hes : e s = D weylS := embedding_descend (D weylS)
    (conjugated_fixed_of_commute u weylS hu hs₀ longestWeyl_commutes_swap)
  have hew : e w = D longestWeyl := embedding_descend (D longestWeyl)
    (conjugated_fixed_of_commute u longestWeyl hu hw₀ (Commute.refl _))
  dsimp only [e] at hι hec hes hew
  have hn : ((p+1 : ℕ) : K) ≠ 0 := by simp
  let : NeZero ((p+1 : ℕ) : K) := ⟨hn⟩
  have hcard : Nat.card C = Nat.card F + 1 := by
    rw [hF]
    exact HasEnoughRootsOfUnity.natCard_rootsOfUnity K (p+1)
  apply exists_localData_of_torus ι hιinj hcard (hF ▸ hd) c s w
  · apply fieldEmbedding_injective (algebraMap F K)
    rw [map_pow,hec,← map_pow]
    have hcube : c₀^3 = 1 := cycle_cube
    rw [hcube,map_one,map_one]
  · rintro ⟨a,ha⟩
    have he := congrArg e ha
    rw [hι,hec] at he
    have he' : torus a.1.val a.2.val = c₀ := (MulAut.conj u).injective he
    exact cycle_not_mem_torus (F := K) ⟨(a.1.val,a.2.val),he'⟩
  · intro l m
    apply fieldEmbedding_injective (algebraMap F K)
    simp only [map_mul,map_inv,hec,hι]
    change D c₀ * D (torus l.val m.val) * (D c₀)⁻¹ =
      D (torus (m.val*l.val⁻¹) l.val⁻¹)
    simpa only [map_mul,map_inv,cycle,c₀] using congrArg D (cycle_torus l.val m.val)
  · intro l m
    apply fieldEmbedding_injective (algebraMap F K)
    simp only [map_mul,map_inv,hes,hι]
    simpa only [map_mul,map_inv] using congrArg D (OddSplitTorus.weylS_torus l.val m.val)
  · intro l m
    apply fieldEmbedding_injective (algebraMap F K)
    simp only [map_mul,map_inv,hew,hι]
    simpa only [map_mul,map_inv,inverter,longestWeyl] using
      congrArg D (inverter_torus l.val m.val)
  · apply Commute.of_map (f := e) (fieldEmbedding_injective (algebraMap F K))
    rw [hew,hec]
    exact hcw.map D
end
end Atlas.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit
end
