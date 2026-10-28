module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.GTwoSource.CentralPair
public import Theory.SpecificGroups.G2.RootPresentationRecognition.Relations

/-!
# Completion of the two undetermined positive G₂ coefficients

Fong–Seitz II (1974), (9.16)–(9.21), printed pp.216–217, leaves an
unknown central coefficient in EB and an unknown highest-root coefficient
in FE after the lower-module calculation. This module extracts those
coefficients from the actual root maps, derives their additive laws using
collection, and derives their scaling laws using the actual torus action.
It then proves the two missing equations in the presentation's literal
A–F order, including the field of order four.

The earlier DC, FC, FD equations, ten commutations, lower coefficients
of FE, torus weights and one unit commutator are explicit intermediate
inputs. They must still be constructed from (6E)(a) and the coupled
rank-one modules. This is the coefficient step, not the source recognition
theorem. The FE normalization needs a scalar outside `{0,1}`; the binary
case and the Weyl/rank-one equations remain with source reconstruction.
-/

@[expose] public noncomputable section
open scoped commutatorElement
open Atlas.G2.RootPresentationRecognition
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
variable {K Y : Type*} [Field K] [CharP K 2] [Group Y]

/-- Every additive root element is an involution in characteristic two. -/
theorem root_inv (L : PositiveRoots K Y) (i : Fin 6) (a : K) :
    (L.x i a)⁻¹ = L.x i a := by
  apply inv_eq_of_mul_eq_one_right
  rw [← L.x_add, CharTwo.add_self_eq_zero, L.x_zero]

/-- For additive roots in characteristic two, the source right commutator
`x⁻¹ y⁻¹ x y` equals the library left commutator `x y x⁻¹ y⁻¹`. -/
theorem right_commutator_eq (L : PositiveRoots K Y) (i j : Fin 6) (a b : K) :
    (L.x i a)⁻¹ * (L.x j b)⁻¹ * L.x i a * L.x j b = ⁅L.x i a, L.x j b⁆ := by
  simp only [commutatorElement_def, root_inv]

/-- Reverse the source (9.16)(ii) commutator, including its D,C,B,A factor
order, to obtain the presentation's F,E ordered exchange. -/
theorem fe_exchange_of_right_commutator (L : PositiveRoots K Y) (z e a : K)
    (hc : (L.x 4 e)⁻¹ * (L.x 5 z)⁻¹ * L.x 4 e * L.x 5 z =
      L.x 3 (e*z) * L.x 2 (e*z^2) * L.x 1 (e*z^3) * L.x 0 a) :
    L.x 5 z * L.x 4 e =
      L.x 0 a * L.x 1 (e*z^3) * L.x 2 (e*z^2) * L.x 3 (e*z) * L.x 4 e * L.x 5 z := by
  have hi := congrArg (fun t : Y => t⁻¹) hc
  simp only [mul_inv_rev, root_inv] at hi
  have h := congrArg (fun t : Y => t * (L.x 4 e * L.x 5 z)) hi
  have hE : L.x 4 e * L.x 4 e = 1 := by
    rw [← L.x_add, CharTwo.add_self_eq_zero, L.x_zero]
  have hF : L.x 5 z * L.x 5 z = 1 := by
    rw [← L.x_add, CharTwo.add_self_eq_zero, L.x_zero]
  have he : L.x 4 e * (L.x 4 e * L.x 5 z) = L.x 5 z := by rw [← mul_assoc, hE, one_mul]
  have hf : L.x 5 z * L.x 5 z = 1 := hF
  simpa only [mul_assoc, he, hf, mul_one] using h

variable [Finite K]

/-- Intermediate root data before determining EB and the highest FE coefficient.
`fe_mem` specifies only the already known lower coordinates. -/
structure PartialPositiveData (L : PositiveRoots K Y) : Type _ where
  A_injective : Function.Injective (L.root 0)
  commuting : L.CommutingRelations
  dc : ∀ d c, L.x 3 d * L.x 2 c = L.x 0 (c*d) * L.x 2 c * L.x 3 d
  fc : ∀ z c, L.x 5 z * L.x 2 c = L.x 1 (c*z) * L.x 2 c * L.x 5 z
  fd : ∀ z d, L.x 5 z * L.x 3 d =
    L.x 0 (d^2*z) * L.x 1 (d*z^2) * L.x 3 d * L.x 5 z
  eb_mem : ∀ b e, ⁅L.x 4 e, L.x 1 b⁆ ∈ (L.root 0).range
  eb_one : ⁅L.x 4 1, L.x 1 1⁆ = L.x 0 1
  fe_mem : ∀ z e, ∃ a, L.x 5 z * L.x 4 e =
    L.x 0 a * L.x 1 (e*z^3) * L.x 2 (e*z^2) * L.x 3 (e*z) * L.x 4 e * L.x 5 z
  torus : Kˣ × Kˣ → Y
  torus_root : ∀ l m i a,
    torus (l,m) * L.x i a * (torus (l,m))⁻¹ =
      L.x i (BorelWeylData.weight l m i * a)

namespace PartialPositiveData
variable {L : PositiveRoots K Y} (d : PartialPositiveData L)

/-- The source torus slice with weights `(t⁻¹,t,t⁻²)` on A,B,E. -/
def centralPair : CentralPairData K Y where
  A := L.root 0
  B := L.root 1
  E := L.root 4
  A_injective := d.A_injective
  ba := d.commuting.ba
  ea := d.commuting.ea
  commutator_mem := d.eb_mem
  torus t := d.torus (1,t⁻¹)
  torus_A t a := by simpa [BorelWeylData.weight] using d.torus_root 1 t⁻¹ 0 a
  torus_B t b := by simpa [BorelWeylData.weight] using d.torus_root 1 t⁻¹ 1 b
  torus_E t e := by simpa [BorelWeylData.weight] using d.torus_root 1 t⁻¹ 4 e
  unit_commutator := d.eb_one

include d in
/-- The EB equation follows from containment and the normalized unit commutator. -/
theorem eb (e b : K) : L.x 4 e * L.x 1 b = L.x 0 (b*e) * L.x 1 b * L.x 4 e :=
  d.centralPair.exchange b e

private theorem append_relation {a b c : Y} (h : a * b = c) (z : Y) :
    a * (b * z) = c * z := by rw [← mul_assoc, h]

omit [CharP K 2] [Finite K] in
private theorem collect_same (i : Fin 6) (s t : K) (z : Y) :
    L.x i s * (L.x i t * z) = L.x i (s + t) * z := by
  rw [← mul_assoc, ← L.x_add]

variable (g : K → K → K)
  (hg : ∀ z e, L.x 5 z * L.x 4 e =
    L.x 0 (g z e) * L.x 1 (e*z^3) * L.x 2 (e*z^2) * L.x 3 (e*z) * L.x 4 e * L.x 5 z)

include d hg in
omit [Finite K] in
/-- Associativity and the lower exchanges force the additive defect (9.17)(ii). -/
theorem coefficient_add (z w e : K) :
    g (z+w) e = g z e + g w e + z*w^2*e^2 + w*z^2*e^2 := by
  have h := congrArg (fun y : Y => L.x 5 z * y) (hg w e)
  rw [← mul_assoc, ← L.x_add, hg] at h
  simp only [mul_assoc, append_relation (d.commuting.fa _ _),
    append_relation (d.commuting.fb _ _), append_relation (d.fc _ _),
    append_relation (d.fd _ _), append_relation (hg _ _),
    append_relation (d.commuting.ca _ _), append_relation (d.commuting.ba _ _),
    append_relation (d.commuting.da _ _), append_relation (d.commuting.db _ _),
    append_relation (d.commuting.cb _ _), append_relation (d.dc _ _),
    collect_same, ← L.x_add] at h
  have hcB : e*w^3 + (e*(w^2*z) + (e*(w*z^2) + e*z^3)) = e*(z+w)^3 := by
    ring_nf
    simp [CharTwo.ofNat_eq_mod]
  have hcC : e*w^2 + e*z^2 = e*(z+w)^2 := by rw [CharTwo.add_sq]; ring
  have hcD : e*w + e*z = e*(z+w) := by ring
  have hcA : g w e + ((e*w)^2*z + (g z e + e*(z^2*(e*w)))) =
      g z e + g w e + z*w^2*e^2 + w*z^2*e^2 := by ring
  rw [hcB, hcC, hcD, hcA] at h
  simp only [← mul_assoc, mul_right_cancel_iff] at h
  exact Multiplicative.ofAdd.injective (d.A_injective h)

include d hg in
omit [CharP K 2] [Finite K] in
/-- A zero long-root parameter makes the highest coefficient vanish. -/
theorem coefficient_zero_right (z : K) : g z 0 = 0 := by
  have h := hg z 0
  simp only [zero_mul, L.x_zero, mul_one] at h
  have he : L.x 0 (g z 0) = L.x 0 0 := by
    rw [L.x_zero]
    exact mul_right_cancel (h.symm.trans (one_mul _).symm)
  exact Multiplicative.ofAdd.injective (d.A_injective he)

include d hg in
omit [CharP K 2] [Finite K] in
/-- Conjugate the actual FE product by the full two-parameter torus. -/
theorem coefficient_torus (l m : Kˣ) (z e : K) :
    g ((l : K) / m * z) ((m : K)^2 / l * e) = (l : K) * m * g z e := by
  let c := MulAut.conj (d.torus (l,m))
  have hc (i : Fin 6) (a : K) : c (L.x i a) = L.x i (BorelWeylData.weight l m i * a) :=
    d.torus_root l m i a
  have h := congrArg c (hg z e)
  simp only [map_mul, hc] at h
  dsimp [BorelWeylData.weight] at h
  rw [hg] at h
  have hb : (m:K)^2 / l * e * ((l:K) / m * z)^3 =
      (l:K)^2 / m * (e*z^3) := by field_simp
  have hcc : (m:K)^2 / l * e * ((l:K) / m * z)^2 = (l:K) * (e*z^2) := by
    field_simp
  have hd : (m:K)^2 / l * e * ((l:K) / m * z) = (m:K) * (e*z) := by
    field_simp
  rw [hb,hcc,hd] at h
  simp only [mul_right_cancel_iff] at h
  exact Multiplicative.ofAdd.injective (d.A_injective h)

include d hg in
omit [CharP K 2] [Finite K] in
/-- Express the same scaling in the paper's h₁,h₂ parameters. -/
theorem coefficient_scale (l m : Kˣ) (z e : K) :
    g ((l:K)⁻¹^2 * m * z) ((l:K)^3 * (m:K)⁻¹^2 * e) = (m:K)⁻¹ * g z e := by
  have h := d.coefficient_torus g hg l⁻¹ (l/m) z e
  simp only [Units.val_inv_eq_inv_val, Units.val_div_eq_div_val] at h
  have hf : (l:K)⁻¹ / ((l:K)/(m:K)) * z = (l:K)⁻¹^2 * m * z := by
    field_simp
  have he : ((l:K)/(m:K))^2 / (l:K)⁻¹ * e = (l:K)^3 * (m:K)⁻¹^2 * e := by
    field_simp
  have ha : (l:K)⁻¹ * ((l:K)/(m:K)) = (m:K)⁻¹ := by field_simp
  rwa [hf,he,ha] at h

include d in
/-- The two reconstructed coefficients complete the literal positive presentation. -/
theorem relations (hw : ∃ w : K, w ≠ 0 ∧ w ≠ 1) : L.CharTwoRelations := by
  classical
  choose g hg using d.fe_mem
  have heq := g_normalization g (d.coefficient_zero_right g hg)
    (d.coefficient_scale g hg) (d.coefficient_add g hg) hw
  refine ⟨d.commuting, d.dc, d.eb, d.fc, d.fd, ?_⟩
  intro z e
  simpa only [heq z e, mul_comm (z^3) (e^2)] using hg z e
end PartialPositiveData
end Theory.AlgebraicGroup.TitsSystem.SourceBinary.GTwoSource
