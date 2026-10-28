module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Setup
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.Model
public import Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalTransport
public import Theory.Representation.BinaryOffender.EquivariantOffender
public import Theory.Representation.NormalElementaryQuotient

/-!
# Relabeling the actual natural S6 point action

An even permutation carries the nonzero marked vector to the duad {4,5}.
Conjugating the quotient map by that permutation and applying the same
permutation to the module coordinates preserves the action. The original
vector centralizer becomes the canonical point parabolic, and its embedded
two-core becomes the exceptional subgroup used in the finite model.

Source: Aschbacher--Smith C.1.37, printed pp.141--143, and the natural S6
application of B.2.19 on p.143.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterC.NaturalSixControl
open Subgroup Stellmacher
open ChapterB.BaumannArgument
open scoped IsMulCommutative
open Theory.SpecificGroups.SymmetricSix
open Theory.SpecificGroups.SymmetricSix.BinaryFlags
open Theory.SpecificGroups.SymmetricSix.BinaryFlags.NaturalGeometry
open Representation.BinaryOffender
universe u
variable {K : Type u} [Group K] (V : Subgroup K) [V.Normal]

/-- Coordinates for the literal conjugation action on the binary natural module. -/
structure NaturalAction where
  q : K →* Model.S
  onto : Function.Surjective q
  kernel : q.ker = pCore 2 K
  coordinates : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6))
  action : ∀ g v, (coordinates (MulAut.conjNormal g v)).toAdd =
    Model.rho (q g) (coordinates v).toAdd

namespace NaturalAction
variable {V} (d : NaturalAction V)

theorem kernel_centralizer : d.q.ker = centralizer (V : Set K) :=
  RankOne.SymmetricSix.natural_six_kernel_eq_centralizer V d.q d.coordinates d.action

def addCoordinates : Additive V ≃+ BinaryPermutation.natural (Fin 6) where
  toFun v := (d.coordinates v.toMul).toAdd
  invFun v := Additive.ofMul (d.coordinates.symm (Multiplicative.ofAdd v))
  left_inv v := d.coordinates.symm_apply_apply v
  right_inv v := d.coordinates.apply_symm_apply (Multiplicative.ofAdd v)
  map_add' v w := d.coordinates.map_mul v.toMul w.toMul

variable [IsElementaryAbelian 2 V]

noncomputable def linearCoordinates : Additive V ≃ₗ[ZMod 2] BinaryPermutation.natural (Fin 6) :=
  { d.addCoordinates with map_smul' := ZMod.map_smul d.addCoordinates }

noncomputable def ρ : Representation (ZMod 2) Model.S (Additive V) :=
  Representation.NormalElementaryQuotient.representation V d.q d.onto d.kernel_centralizer

theorem equivariant (g : Model.S) (v : Additive V) :
    d.linearCoordinates (d.ρ g v) = Model.rho g (d.linearCoordinates v) := by
  obtain ⟨a,rfl⟩ := d.onto g
  have he := Representation.NormalElementaryQuotient.representation_apply
    V d.q d.onto d.kernel_centralizer a v
  have hc : (d.ρ (d.q a) v).toMul = MulAut.conjNormal a v.toMul := Subtype.ext he
  change (d.coordinates _).toAdd = _
  rw [hc]
  exact d.action a v.toMul

theorem fixed_finrank (A : Subgroup Model.S) :
    Module.finrank (ZMod 2) (fixedSpace d.ρ A) =
      Module.finrank (ZMod 2) (fixedSpace Model.rho A) := by
  have he := fixedSpace_map_equivariant d.ρ Model.rho
    (MonoidHom.id Model.S) d.linearCoordinates d.equivariant A
  rw [map_id] at he
  exact ((Submodule.equivMapOfInjective d.linearCoordinates.toLinearMap
    d.linearCoordinates.injective _).trans (LinearEquiv.ofEq _ _ he)).finrank_eq

theorem model_fixedCodim (A : Subgroup Model.S) :
    fixedCodim d.ρ A = fixedCodim Model.rho A := by
  simpa only [map_id] using fixedCodim_map_equivariant d.ρ Model.rho
    (MonoidHom.id Model.S) d.linearCoordinates d.equivariant A

theorem bestOffender_iff (A : Subgroup Model.S) :
    IsBestOffender d.ρ A ↔ IsBestOffender Model.rho A := by
  simp only [IsBestOffender, weight, d.fixed_finrank]

include d in
omit [IsElementaryAbelian 2 V] in
theorem module_card : Nat.card V = 16 := by
  rw [Nat.card_congr d.coordinates.toEquiv]
  change Nat.card (BinaryPermutation.natural (Fin 6)) = 16
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    BinaryPermutation.finrank_natural_even (Fin 6) (by decide)]
  rfl

omit [IsElementaryAbelian 2 V] in
noncomputable def actionEquiv : (K ⧸ centralizer (V : Set K)) ≃* Model.S :=
  (QuotientGroup.quotientMulEquivOfEq d.kernel_centralizer.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.q d.onto)

omit [IsElementaryAbelian 2 V] in
theorem actionEquiv_apply (g : K) : d.actionEquiv (actionMap V g) = d.q g := rfl

omit [IsElementaryAbelian 2 V] in
theorem image_eq (A : Subgroup K) :
    (A.map (actionMap V)).map d.actionEquiv.toMonoidHom = A.map d.q := by
  rw [map_map]
  rfl

variable [Finite K]

theorem fixed_card (A : Subgroup K) :
    Nat.card (V ⊓ centralizer (A : Set K) : Subgroup K) =
      2 ^ Module.finrank (ZMod 2) (fixedSpace Model.rho (A.map d.q)) := by
  have h := Nat.card_congr (Representation.NormalElementaryQuotient.fixedSpaceEquiv
    V d.q d.onto d.kernel_centralizer A)
  rw [← h]
  change Nat.card (fixedSpace d.ρ (A.map d.q)) = _
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, d.fixed_finrank]

theorem fixedCodim_eq_model (A : Subgroup K) :
    ChapterB.BaumannArgument.fixedCodim V A = Representation.BinaryOffender.fixedCodim Model.rho (A.map d.q) := by
  have hd := fixedCodim_add_finrank Model.rho (A.map d.q)
  rw [BinaryPermutation.finrank_natural_even (Fin 6) (by decide)] at hd
  norm_num at hd
  rw [ChapterB.BaumannArgument.fixedCodim, d.module_card, d.fixed_card, Nat.log_pow Nat.one_lt_two]
  norm_num
  omega

omit [IsElementaryAbelian 2 V] in
theorem residual_image : (pResidual 2 K).map d.q = alternatingGroup (Fin 6) := by
  rw [map_pResidual_of_surjective 2 d.q d.onto, Equiv.Perm.twoResidual_eq_alternating]

omit [IsElementaryAbelian 2 V] in
theorem residual_lift (g : alternatingGroup (Fin 6)) :
    ∃ a ∈ pResidual 2 K, d.q a = g := by
  apply mem_map.mp
  rw [d.residual_image]
  exact g.property

omit [IsElementaryAbelian 2 V] in
def residualHom : pResidual 2 K →* alternatingGroup (Fin 6) :=
  (d.q.comp (pResidual 2 K).subtype).codRestrict _ fun a => by
    rw [← d.residual_image]
    exact mem_map_of_mem d.q a.property

omit [IsElementaryAbelian 2 V] in
theorem residual_surjective : Function.Surjective d.residualHom := by
  intro g
  obtain ⟨a,ha,he⟩ := d.residual_lift g
  exact ⟨⟨a,ha⟩, Subtype.ext he⟩

end NaturalAction

namespace SourceData
variable {L V : Subgroup K} [L.Normal] [V.Normal] {T : Sylow 2 K}
  (d : SourceData L V T)

theorem marked_nonzero : (d.eV d.v).toAdd ≠ 0 := by
  intro h
  apply d.v_ne
  apply d.eV.injective
  apply Multiplicative.toAdd.injective
  rw [map_one]
  exact h

/-- An even relabeling of the literal nonzero marked vector. -/
noncomputable def relabeler : alternatingGroup (Fin 6) :=
  Classical.choose (NaturalTransport.transitive_nonzero (d.eV d.v).toAdd
    (pairVector 4 5) d.marked_nonzero pairVector45_ne_zero)

theorem relabeler_spec : Model.rho d.relabeler.val (d.eV d.v).toAdd = pairVector 4 5 :=
  Classical.choose_spec (NaturalTransport.transitive_nonzero (d.eV d.v).toAdd
    (pairVector 4 5) d.marked_nonzero pairVector45_ne_zero)

/-- The quotient map after the same even relabeling of the actor and module. -/
noncomputable def q0 : K →* Model.S :=
  (MulAut.conj d.relabeler.val).toMonoidHom.comp d.q

noncomputable def e0 : V ≃* Multiplicative (BinaryPermutation.natural (Fin 6)) :=
  d.eV.trans (LinearMap.GeneralLinearGroup.toLinearEquiv
    (Model.rho.asGroupHom d.relabeler.val)).toAddEquiv.toMultiplicative

theorem e0_apply (v : V) : (d.e0 v).toAdd = Model.rho d.relabeler.val (d.eV v).toAdd := rfl

theorem e0_point : (d.e0 d.v).toAdd = pairVector 4 5 := d.relabeler_spec

theorem q0_onto : Function.Surjective d.q0 :=
  (MulAut.conj d.relabeler.val).surjective.comp d.onto

theorem q0_kernel : d.q0.ker = pCore 2 K := by
  rw [q0, MonoidHom.ker_comp_of_injective _ _ (MulAut.conj d.relabeler.val).injective]
  exact d.ker_eq

theorem q0_image_component : L.map d.q0 = alternatingGroup (Fin 6) := by
  rw [q0, ← map_map, d.image_component]
  exact conjugate_alternating d.relabeler.val

theorem e0_action (g : K) (v : V) :
    (d.e0 (MulAut.conjNormal g v)).toAdd = Model.rho (d.q0 g) (d.e0 v).toAdd := by
  rw [d.e0_apply, d.action, d.e0_apply]
  change Model.rho d.relabeler.val (Model.rho (d.q g) (d.eV v).toAdd) =
    Model.rho (d.relabeler.val * d.q g * d.relabeler.val⁻¹)
      (Model.rho d.relabeler.val (d.eV v).toAdd)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel_right]

noncomputable def canonicalAction : NaturalAction V where
  q := d.q0
  onto := d.q0_onto
  kernel := d.q0_kernel
  coordinates := d.e0
  action := d.e0_action

private theorem marked_fixed_iff (g : K) :
    g ∈ d.P ↔ Model.rho (d.q0 g) (pairVector 4 5) = pairVector 4 5 := by
  have h : g ∈ d.P ↔ MulAut.conjNormal g d.v = d.v := by
    change g ∈ centralizer ({(d.v : K)} : Set K) ↔ _
    rw [mem_centralizer_singleton_iff]
    constructor
    · intro hc
      apply Subtype.ext
      change g * (d.v : K) * g⁻¹ = d.v
      rw [hc, mul_inv_cancel_right]
    · intro hc
      have he := congrArg Subtype.val hc
      change g * (d.v : K) * g⁻¹ = (d.v : K) at he
      exact mul_inv_eq_iff_eq_mul.mp he
  rw [h]
  constructor
  · intro h
    have he := d.e0_action g d.v
    rw [h, d.e0_point] at he
    exact he.symm
  · intro h
    apply d.e0.injective
    apply Multiplicative.toAdd.injective
    rw [d.e0_action, d.e0_point, h]

theorem P_eq_comap : d.P = H1.comap d.q0 := by
  ext g
  rw [d.marked_fixed_iff]
  change Model.rho (d.q0 g) (pairVector 4 5) = pairVector 4 5 ↔ d.q0 g ∈ H1
  rw [pairVector_map, pairVector_eq_iff ((d.q0 g).injective.ne (by decide)) (by decide)]
  change pair (d.q0 g 4) (d.q0 g 5) = pair 4 5 ↔ (pair 4 5).image (d.q0 g) = pair 4 5
  simp [pair]

variable [Finite K]

theorem R_eq_comap : d.R = Model.E.comap d.q0 := by
  have hp : IsPGroup 2 d.q0.ker := d.q0_kernel.symm ▸ pCore_isPGroup
  have hk : d.q0.ker ≤ d.P := by
    rw [d.P_eq_comap]
    exact MonoidHom.ker_le_comap d.q0 H1
  have hkcore : d.q0.ker ≤ d.R :=
    le_pCoreIn_of_normalizes hp hk le_normalizer_of_normal
  have hm := map_pCoreIn_of_ker_isPGroup d.q0 hp d.P
  have himage : d.P.map d.q0 = H1 := by
    rw [d.P_eq_comap, map_comap_eq_self_of_surjective d.q0_onto]
  rw [himage, H1_core_eq_pointCore, Model.pointCore_eq_exceptional] at hm
  rw [← hm, comap_map_eq, sup_eq_left.mpr hkcore]

end SourceData
end CFSG.Quasithin.ChapterC.NaturalSixControl
