module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FixedCodimensions.FullAutomizer
public import Theory.Representation.G2.RestrictedModules.NaturalCoordinates
public import Theory.SpecificGroups.G2.PRegularClasses.GeometricTorus
public import Theory.SpecificGroups.G2.PRegularClasses.FieldExtension
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Theory.Representation.BinaryOffender.QuadraticQuotient

/-!
# Odd-order displacement in the actual natural G₂ module

Six coordinates identify the trace-zero octonion quotient. Its characteristic
polynomial commutes with field extension. Over an algebraic closure, an odd-order
actor is conjugate to the explicit rank-two torus; a nonidentity torus actor has
at most two unit weights. Thus every nonidentity odd-order actor moves at least
four field dimensions. Binary scalar restriction and the literal original
coordinate projection give the 4n bound, retaining nonsplit central attachments.

Source: Aschbacher--Smith I.2.3 and 11.2.2(2), printed pp.413,768.
The torus conjugacy input is the proved octonion model of GLS III 1.4.2(e).
The imported octonion coordinates are attributed in LICENSES/ATLAS.txt.
G2Full applies this calculation to all odd-prime actors of the actual automizer.
-/

open Polynomial Subgroup Representation Representation.BinaryOffender
public noncomputable section
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.G2Odd
open Atlas.G2
open Restricted.NaturalCoordinates
variable {F K : Type*} [Field F] [CharP F 2] [Field K] [CharP K 2]

private theorem extension_action (f : F →+* K) (g : Model F) (v : Fin 6 → F) :
    action K (PRegularClasses.FieldExtension.fieldEmbedding f g) (fun i => f (v i)) =
      fun i => f (action F g v i) := by
  have hr : ((representative K (fun i => f (v i))).val) =
      PRegularClasses.FieldExtension.coeffMap f (representative F v).val := by
    ext i
    fin_cases i <;> simp [representative, PRegularClasses.FieldExtension.coeffMap]
  have hh := PRegularClasses.FieldExtension.fieldEmbedding_action f g (representative F v).val
  ext i
  fin_cases i <;>
    simp [action_apply, Restricted.NaturalCoordinates.projection,
      Natural.traceZeroAction_val, hr,
      PRegularClasses.FieldExtension.fieldEmbedding_action,
      PRegularClasses.FieldExtension.coeffMap]


private theorem extension_charpoly (f : F →+* K) (g : Model F) :
    (action K (PRegularClasses.FieldExtension.fieldEmbedding f g)).charpoly =
      (action F g).charpoly.map f := by
  rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun K (Fin 6)),
    ← LinearMap.charpoly_toMatrix _ (Pi.basisFun F (Fin 6)), ← Matrix.charpoly_map]
  congr 1
  ext i j
  simp only [LinearMap.toMatrix_apply, Pi.basisFun_repr, Pi.basisFun_apply,
    Matrix.map_apply]
  have hv : (fun k => f ((Pi.single j (1 : F) : Fin 6 → F) k)) = (Pi.single j (1 : K) : Fin 6 → K) := by
    ext k
    simp [Pi.single_apply]
  have hh := extension_action f g (Pi.single j 1)
  rw [hv] at hh
  exact congrFun hh i

private theorem conjugate_charpoly (g h : Model F) (hc : IsConj g h) :
    (action F g).charpoly = (action F h).charpoly := by
  obtain ⟨c,rfl⟩ := isConj_iff.mp hc
  let e := (action F).asGroupHom c
  have he : action F (c * g * c⁻¹) = e.val * action F g * e.inv := by
    simp only [map_mul]
    rfl
  rw [he]
  exact ((LinearEquiv.ofLinearMap e.val e.inv e.val_inv e.inv_val).charpoly_conj
    (action F g)).symm

private theorem torus_charpoly (l m : Fˣ) :
    (action F (torus l m)).charpoly =
      (X-C (l:F)) * (X-C (m:F)) * (X-C (↑(l*m⁻¹):F)) *
      (X-C (↑(l⁻¹*m):F)) * (X-C (↑m⁻¹:F)) * (X-C (↑l⁻¹:F)) := by
  rw [← LinearMap.charpoly_toMatrix _ (Pi.basisFun F (Fin 6))]
  have hm : LinearMap.toMatrix (Pi.basisFun F (Fin 6)) (Pi.basisFun F (Fin 6))
      (action F (torus l m)) =
      Matrix.diagonal ![(l:F),(m:F),(↑(l*m⁻¹):F),(↑(l⁻¹*m):F),(↑m⁻¹:F),(↑l⁻¹:F)] := by
    ext i j
    fin_cases i <;>
      simp [action_apply, Restricted.NaturalCoordinates.projection,
        representative, Natural.traceZeroAction_val, torus, torusEquiv, torusLinear,
        torusWeights, Matrix.diagonal, Pi.single_apply, eq_comm]
  rw [hm, Matrix.charpoly_diagonal]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Matrix.cons_val_fin_one, Fin.prod_univ_zero, mul_one]
  ring

private theorem torus_multiplicity (l m : Fˣ) (hne : torus l m ≠ 1) :
    ((action F (torus l m)).charpoly).rootMultiplicity 1 ≤ 2 := by
  classical
  have hpair : ¬ (l = 1 ∧ m = 1) := by
    rintro ⟨rfl,rfl⟩
    exact hne torusHom.map_one
  rw [torus_charpoly]
  repeat' rw [Polynomial.rootMultiplicity_mul]
  all_goals try {simp only [ne_eq, mul_eq_zero, X_sub_C_ne_zero, or_self, not_false_eq_true]}
  simp only [Polynomial.rootMultiplicity_X_sub_C]
  have hli : (1 : F) = ↑l⁻¹ ↔ l = 1 := by
    rw [← Units.val_one, Units.val_inj, eq_inv_iff_mul_eq_one]
    simp
  have hmi : (1 : F) = ↑m⁻¹ ↔ m = 1 := by
    rw [← Units.val_one, Units.val_inj, eq_inv_iff_mul_eq_one]
    simp
  have hlm : (1 : F) = ↑(l*m⁻¹) ↔ l = m := by
    rw [← Units.val_one, Units.val_inj, eq_comm, mul_inv_eq_one]
  have hml : (1 : F) = ↑(l⁻¹*m) ↔ l = m := by
    rw [← Units.val_one, Units.val_inj, eq_comm, inv_mul_eq_one]
  have hl1 : (1 : F) = ↑l ↔ l = 1 := by
    rw [← Units.val_one, Units.val_inj, eq_comm]
  have hm1 : (1 : F) = ↑m ↔ m = 1 := by
    rw [← Units.val_one, Units.val_inj, eq_comm]
  simp only [hli,hmi,hlm,hml,hl1,hm1]
  by_cases hl : l = 1 <;> by_cases hm : m = 1 <;> by_cases he : l = m <;>
    simp_all

/-- A nonidentity odd-order G₂ actor fixes at most two field dimensions
on the actual natural quotient. -/
theorem natural_odd_fixed (g : Model F) (hne : g ≠ 1) (ho : Odd (orderOf g)) :
    Module.finrank F ((Natural.action F g - LinearMap.id).ker) ≤ 2 := by
  let K := AlgebraicClosure F
  let f : F →+* K := algebraMap F K
  let h := PRegularClasses.FieldExtension.fieldEmbedding f g
  have hne' : h ≠ 1 := by
    intro hh
    exact hne (PRegularClasses.FieldExtension.fieldEmbedding_injective f
      (hh.trans (map_one _).symm))
  have ho' : ¬ 2 ∣ orderOf h := by
    rw [PRegularClasses.FieldExtension.fieldEmbedding_orderOf]
    exact ho.not_two_dvd_nat
  obtain ⟨l,m,hc⟩ := PRegularClasses.isConj_torus_of_odd_order h ho'
  have ht : torus l m ≠ 1 := by
    intro ht
    apply hne'
    exact (isConj_one_right.mp (ht ▸ hc.symm))
  have hpoly : ((action F g).charpoly).rootMultiplicity 1 ≤ 2 := by
    rw [Polynomial.eq_rootMultiplicity_map f.injective 1, map_one,
      ← extension_charpoly, conjugate_charpoly h _ hc]
    exact torus_multiplicity l m ht
  have hnat : (Natural.action F g).charpoly = (action F g).charpoly :=
    ((equiv F).charpoly_conj (Natural.action F g)).symm
  have hbound := LinearMap.finrank_eigenspace_le (Natural.action F g) 1
  rw [hnat] at hbound
  have heig : Module.End.eigenspace (Natural.action F g) 1 = (Natural.action F g - LinearMap.id).ker := by
    ext v
    rw [Module.End.mem_eigenspace_iff]
    change Natural.action F g v = (1 : F) • v ↔ Natural.action F g v - v = 0
    rw [one_smul,sub_eq_zero]
  rw [heig] at hbound
  exact hbound.trans hpoly

/-- Every nonidentity odd-order inner G₂ actor moves at least four
coefficient-field dimensions after binary scalar restriction. -/
theorem natural_odd_lower [Finite F] [Algebra (ZMod 2) F]
    (g : Model F) (hne : g ≠ 1) (ho : Odd (orderOf g)) :
    4 * Module.finrank (ZMod 2) F ≤
      fixedCodim (restrictScalars (k := ZMod 2) (Natural.action F)) (zpowers g) := by
  let Q := (Natural.action F g - LinearMap.id).ker
  have hdim := natural_odd_fixed g hne ho
  change Module.finrank F Q ≤ 2 at hdim
  have hsum := Q.finrank_quotient_add_finrank
  rw [Natural.finrank_space] at hsum
  have hfour : 4 ≤ Module.finrank F (Natural.Space F ⧸ Q) := by omega
  have hfix : fixedSpace (restrictScalars (k := ZMod 2) (Natural.action F)) (zpowers g) =
      Q.restrictScalars (ZMod 2) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff]
    change Natural.action F g v = v ↔ Natural.action F g v - v = 0
    exact sub_eq_zero.symm
  unfold fixedCodim
  rw [hfix, (Submodule.Quotient.restrictScalarsEquiv (ZMod 2) Q).finrank_eq,
    ← Module.finrank_mul_finrank (ZMod 2) F (Natural.Space F ⧸ Q)]
  simpa only [Nat.mul_comm] using Nat.mul_le_mul_left (Module.finrank (ZMod 2) F) hfour
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.G2Odd

open scoped IsMulCommutative
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
open CFSG.Quasithin.ChapterB.QuasisimpleSource Atlas.G2
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)

/-- Inner odd-prime actors in the literal original G₂ automizer move at
least 4n dimensions; the original central attachment need not split. -/
theorem g2_inner_odd_prime_lower
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier))) :
    letI := D.elementary
    ∀ p : ℕ, p.Prime → Odd p → ∀ a : Automizer V, orderOf a = p →
      a ∈ inducedAutomizer V L →
      4 * S.field.degree ≤ fixedCodim (automizerRepresentation V) (zpowers a) := by
  let := D.elementary
  intro p hp ho a ha haL
  let c := Coordinates.g2 m
  let : Finite c.Space := Finite.of_surjective c.projection c.projection_surjective
  obtain ⟨ρ,hρ,he,hres⟩ := exists_faithful_quotient_action D S c
  let : Algebra (ZMod 2) S.field.Carrier := ZMod.algebra S.field.Carrier 2
  let : Nontrivial (Natural.Space S.field.Carrier) := Module.nontrivial_of_finrank_pos
    (by rw [Natural.finrank_space]; decide :
      0 < Module.finrank S.field.Carrier (Natural.Space S.field.Carrier))
  let f : c.Space →+ Natural.Space S.field.Carrier := {
    toFun := id
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  let E : c.Space ≃ₗ[ZMod 2] Natural.Space S.field.Carrier :=
    LinearEquiv.ofBijective (f.toZModLinearMap 2) Function.bijective_id
  let τ : Representation (ZMod 2) (Automizer V) (Natural.Space S.field.Carrier) :=
    E.conjRingEquiv.toMonoidHom.comp ρ
  have hτ (a : Automizer V) (v : c.Space) : E (ρ a v) = τ a (E v) := by
    change E (ρ a v) = E (ρ a (E.symm (E v)))
    rw [E.symm_apply_apply]
  let eL : inducedAutomizer V L ≃* Model S.field.Carrier := layerEquiv D S c
  have hres' (b : inducedAutomizer V L) (v : Natural.Space S.field.Carrier) :
      τ b v = Natural.action S.field.Carrier (eL b) v := by
    change E (ρ b (E.symm v)) = _
    rw [hres]
    change Natural.action S.field.Carrier (eL b) (E (E.symm v)) = _
    rw [E.apply_symm_apply]
  let g := eL ⟨a,haL⟩
  have hg : orderOf g = p := by
    rw [eL.orderOf_eq, ← Subgroup.orderOf_coe]
    exact ha
  have hg1 : g ≠ 1 := by intro h; simp only [h,orderOf_one] at hg; exact hp.ne_one hg.symm
  have hgo : Odd (orderOf g) := hg.symm ▸ ho
  have hd := G2Odd.natural_odd_lower g hg1 hgo
  have hfix : fixedSpace τ (zpowers a) =
      fixedSpace (restrictScalars (k := ZMod 2) (Natural.action S.field.Carrier)) (zpowers g) := by
    ext v
    rw [mem_fixedSpace_zpowers_iff,mem_fixedSpace_zpowers_iff]
    exact (congrArg (· = v) (hres' ⟨a,haL⟩ v)).to_iff
  have hcod : fixedCodim τ (zpowers a) =
      fixedCodim (restrictScalars (k := ZMod 2) (Natural.action S.field.Carrier)) (zpowers g) := by
    unfold fixedCodim
    rw [hfix]
  rw [← hcod, Representation.OneCohomology.coefficient_finrank_of_card 2 _ S.field.card_eq] at hd
  exact hd.trans (fixedCodim_le_of_equivariant_surjection
    (automizerRepresentation V) τ (E.toLinearMap.comp (projectionLinear D S c))
    (E.surjective.comp (projectionLinear_surjective D S c))
    (fun b v => (congrArg E (he b v)).trans (hτ b _)) (zpowers a))
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.Parameters.FullAutomizer
