module
public import Theory.SpecificGroups.G2.PRegularClasses.RationalFusion.Frobenius
public import Theory.SpecificGroups.G2.MultiplierOrdinary.OddQuadraticTorus.OrthogonalRankOne
public import Theory.AtlasPort.LinearGroups.G2.WeylMaps
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# An explicit longest-Weyl Lang witness in the G₂ octonion model

The longest Weyl element is the image of (J,J) under the quaternion
SL₂ × SL₂ homomorphism, where J has rows (0,1) and (-1,0). To solve
Frob(A)=AJ, choose a with a^(p²)=-a and a primitive (p+1)-st root l.
The rows (a,-Frob(a)) and (la,-Frob(la)) are independent and have
Frobenius-fixed determinant. Scaling the second row by its inverse produces
A in SL₂. The literal quaternion action then gives Frob(u)=u·w₀ in G₂.

Coefficient-map compatibility is proved on arbitrary octonion vectors
before specializing to basis vectors. No general Lang theorem, unitary
comparison, or connectedness assumption is used.

Source: the nonsplit-torus construction underlying the ordinary G₂ entry in
Aschbacher–Smith I.1.1–I.1.4, printed pp.407–408, and GLS III §6.1.
Coordinates, Weyl maps, and the octonion model use the licensed ATLAS port;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section
namespace Atlas.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit
open Matrix Atlas.SplitOctonion PRegularClasses.FieldExtension PRegularClasses.RationalFusion
open OddQuadraticTorus.OrthogonalRankOne
open scoped MatrixGroups
noncomputable section
variable {F : Type*} [Field F]

def longestWeyl : Model F := (weylR * weylS)^3

def quarterTurn : SL(2,F) := ⟨!![0,1;-1,0], by simp [Matrix.det_fin_two]⟩

theorem longestWeyl_eq_product : (longestWeyl : Model F) = productHom (quarterTurn,quarterTurn) := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp [longestWeyl,pow_succ,weylR,weylS,weylREquiv,weylSEquiv,
    weylRLinear,weylSLinear,weylRApply,weylSApply,productHom,octonionEquiv,
    coordinates,pairEquiv,pairLinear,bar,quarterTurn]


private theorem fieldEmbedding_productHom {K : Type*} [Field K] (f : F →+* K)
    (A B : SL(2,F)) :
    fieldEmbedding f (productHom (A,B)) =
      productHom (SpecialLinearGroup.map f A, SpecialLinearGroup.map f B) := by
  have hc (x : Carrier F) : coeffMap f ((productHom (A,B)).val x) =
      (productHom (SpecialLinearGroup.map f A, SpecialLinearGroup.map f B)).val (coeffMap f x) := by
    ext i
    fin_cases i <;> simp [productHom,octonionEquiv,coordinates,pairEquiv,pairLinear,bar,
      coeffMap,SpecialLinearGroup.map_apply_coe,Matrix.mul_apply,Fin.sum_univ_two]
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  apply (Pi.basisFun K (Fin 8)).ext
  intro j
  simp only [Pi.basisFun_apply]
  change (fieldEmbedding f (productHom (A,B))).val (basisVector j) = _
  rw [fieldEmbedding_basis]
  have hj := hc (basisVector j)
  rw [coeffMap_basisVector] at hj
  simpa only [basisVector,LinearEquiv.coe_coe] using hj

variable [Finite F] {p : ℕ} [CharP F p]

omit [Finite F] in
private theorem exists_quarterTurn_lang [Fintype F] (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ A : SL(2,AlgebraicClosure F),
      SpecialLinearGroup.map
        (FiniteField.frobeniusAlgHom F (AlgebraicClosure F)).toRingHom A = A * quarterTurn := by
  let K := AlgebraicClosure F
  let σ : K →+* K := (FiniteField.frobeniusAlgHom F K).toRingHom
  have hσ (x : K) : σ x = x^p := by
    simp only [σ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, FiniteField.frobeniusAlgHom_apply]
    rw [← Nat.card_eq_fintype_card, hF]
  have hn : ((p+1 : ℕ) : K) ≠ 0 := by simp
  let : NeZero ((p+1 : ℕ) : K) := ⟨hn⟩
  obtain ⟨l, hl⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K (p+1)
  have hl0 : l ≠ 0 := hl.ne_zero (by omega)
  have hlσ : σ l = l⁻¹ := by
    rw [hσ]
    apply eq_inv_of_mul_eq_one_left
    rw [← pow_succ]
    exact hl.pow_eq_one
  have hlσσ : σ (σ l) = l := by rw [hlσ,map_inv₀,hlσ,inv_inv]
  have hlne : l - σ l ≠ 0 := by
    intro he
    have heq : l = σ l := sub_eq_zero.mp he
    have hs : l^2 = 1 := by
      calc
        l^2 = σ l * l := by rw [pow_two]; exact congrArg (fun x => x*l) heq
        _ = 1 := by rw [hlσ]; exact inv_mul_cancel₀ hl0
    have hd := hl.dvd_of_pow_eq_one 2 hs
    have := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have hpp : 1 < p*p := by nlinarith
  obtain ⟨a,ha⟩ := IsAlgClosed.exists_pow_nat_eq (-1 : K)
    (Nat.sub_pos_of_lt hpp)
  have ha0 : a ≠ 0 := by
    intro he
    rw [he, zero_pow (Nat.ne_of_gt (Nat.sub_pos_of_lt hpp))] at ha
    exact one_ne_zero (neg_eq_zero.mp ha.symm)
  have haσσ : σ (σ a) = -a := by
    rw [hσ,hσ,← pow_mul]
    have he : p*p = (p*p-1)+1 := by omega
    rw [he,pow_succ,ha,neg_one_mul]
  let b := l*a
  have hbσσ : σ (σ b) = -b := by
    simp only [b,map_mul,hlσσ,haσσ]
    ring
  let δ := a * (-σ b) - (-σ a) * b
  have hδeq : δ = a * σ a * (l-σ l) := by dsimp [δ,b]; rw [map_mul]; ring
  have hδ0 : δ ≠ 0 := by
    rw [hδeq]
    exact mul_ne_zero (mul_ne_zero ha0 (by simpa using σ.injective.ne ha0)) hlne
  have hδσ : σ δ = δ := by
    dsimp only [δ]
    simp only [map_sub,map_mul,map_neg,haσσ,hbσσ]
    ring
  let A : SL(2,K) := ⟨!![a,-σ a; b/δ,-σ b/δ], by
    rw [Matrix.det_fin_two]
    change a * (-σ b/δ) - (-σ a)*(b/δ) = 1
    calc
      _ = δ/δ := by dsimp only [δ]; ring
      _ = 1 := div_self hδ0⟩
  refine ⟨A, ?_⟩
  apply Subtype.ext
  change (!![a,-σ a; b/δ,-σ b/δ].map σ) =
    !![a,-σ a; b/δ,-σ b/δ] * !![0,1;-1,0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply,Fin.sum_univ_two,haσσ,hbσσ,hδσ] <;> ring
/-- An explicit solution of the longest-Weyl Frobenius equation in the actual
G₂ model. The construction passes through the genuine quaternion action. -/
theorem exists_longestWeyl_lang (hF : Nat.card F = p) (hp : 3 < p) :
    ∃ u : Model (AlgebraicClosure F), frobenius F u = u * longestWeyl := by
  let := Fintype.ofFinite F
  obtain ⟨A,hA⟩ := exists_quarterTurn_lang hF hp
  refine ⟨productHom (A,A), ?_⟩
  change fieldEmbedding (FiniteField.frobeniusAlgHom F (AlgebraicClosure F)).toRingHom
    (productHom (A,A)) = _
  rw [fieldEmbedding_productHom,hA,longestWeyl_eq_product,← map_mul]
  rfl

end
end Atlas.G2.MultiplierOrdinary.OddThreePrimary.Nonsplit
end
