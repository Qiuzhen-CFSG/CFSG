module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.AxisCases
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Transvection.Reciprocal.AxisCases.Shears

/-!
# The full reciprocal shear image in the doubled natural case

The original conjugate is faithfully marked using its central quotient and
the selected g. Under the literal reciprocal action, the forward natural
coordinates identify the action kernel with C_W(A), of order q². Since W
has order q⁴, its action image has order q². The common axis has dimension
two, and the shear bound therefore makes this image the entire shear group.
The original SL₃ action supplies field-linearity; no model actor is assumed.

Source: Aschbacher--Smith 11.3.7(4), case (ii), refs/quasithin.pdf,
printed p.773. The actual R₂ comparison consumes this calculation in
`AxisCases.SL3`.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

open Subgroup Representation
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {G : Type*} [Group G] {T : Sylow 2 G} {H A : Subgroup G}
    {F : BinaryField}

def commonAxis {E : Type*} [AddCommGroup E] [Module F.Carrier E]
    (α : omegaClosure T H →* (E ≃ₗ[F.Carrier] E)) : Submodule F.Carrier E where
  carrier := {v | ∀ w, α w v = v}
  zero_mem' := by simp
  add_mem' := by intro u v hu hv w; simp [hu w,hv w]
  smul_mem' := by intro r v hv w; simp [hv w]

section
variable {E : Type*} [AddCommGroup E] [Module F.Carrier E]
    (e : A ≃* Multiplicative E)
    (hN : omegaClosure T H ≤ normalizer (A : Set G))
    (α : omegaClosure T H →* (E ≃ₗ[F.Carrier] E))
    (hact : ∀ w v, (e (A.normalizerMonoidHom (inclusion hN w) v)).toAdd =
      α w (e v).toAdd)
include hact

theorem mem_axis_iff (v : A) : (e v).toAdd ∈ commonAxis α ↔
    (v : G) ∈ centralizer (omegaClosure T H : Set G) := by
  change (∀ w, α w (e v).toAdd = (e v).toAdd) ↔ _
  simp only [←hact, Multiplicative.toAdd.injective.eq_iff, e.injective.eq_iff]
  constructor
  · intro h w hw
    have he := congrArg Subtype.val (h ⟨w,hw⟩)
    change w * (v : G) * w⁻¹ = (v : G) at he
    exact (mul_inv_eq_iff_eq_mul.mp he)
  · intro h w
    apply Subtype.ext
    change (w : G) * (v : G) * (w : G)⁻¹ = (v : G)
    exact mul_inv_eq_iff_eq_mul.mpr (h w w.property)

def axisEquiv : ↥(A ⊓ centralizer (omegaClosure T H : Set G)) ≃ commonAxis α where
  toFun v := ⟨(e ⟨v,v.property.1⟩).toAdd,(mem_axis_iff e hN α hact _).mpr v.property.2⟩
  invFun v := ⟨(e.symm (Multiplicative.ofAdd v.val) : G),
    (e.symm _).property, (mem_axis_iff e hN α hact _).mp (by
      rw [e.apply_symm_apply]
      exact v.property)⟩
  left_inv v := by apply Subtype.ext; simp
  right_inv v := by apply Subtype.ext; simp

theorem action_ker : α.ker = (centralizer (A : Set G)).comap (omegaClosure T H).subtype := by
  ext w
  change α w = 1 ↔ _
  constructor
  · intro hw v hv
    have he := hact w ⟨v,hv⟩
    rw [hw] at he
    have hh : A.normalizerMonoidHom (inclusion hN w) ⟨v,hv⟩ = ⟨v,hv⟩ :=
      e.injective (Multiplicative.toAdd.injective he)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hh)).symm
  · intro hw
    ext x
    obtain ⟨v,hv⟩ := e.surjective (Multiplicative.ofAdd x)
    have hx : (e v).toAdd = x := congrArg Multiplicative.toAdd hv
    change α w x = x
    rw [←hx,←hact]
    congr 2
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mpr (hw v v.property).symm

theorem action_le_shears (n : NaturalSylowCoordinates T H A F 2) :
    α.range ≤ Shear.group (commonAxis α) := by
  rintro _ ⟨w,rfl⟩
  refine ⟨fun v hv => hv w, fun x => ?_⟩
  obtain ⟨v,hv⟩ := e.surjective (Multiplicative.ofAdd x)
  have hx : (e v).toAdd = x := congrArg Multiplicative.toAdd hv
  rw [←hx,←hact]
  let z : A := A.normalizerMonoidHom (inclusion hN w) v * v⁻¹
  have hz : (e z).toAdd =
      (e (A.normalizerMonoidHom (inclusion hN w) v)).toAdd - (e v).toAdd := by
    simp only [z,map_mul,map_inv,toAdd_mul,toAdd_inv,sub_eq_add_neg]
  rw [←hz,mem_axis_iff e hN α hact]
  apply (n.commutator_le_common_axis hN).trans inf_le_right
  change ⁅(w : G),(v : G)⁆ ∈ ⁅A,omegaClosure T H⁆
  rw [commutator_comm]
  exact commutator_mem_commutator w.property v.property
end

/-- The doubled forward coordinates force the full shear group on the actual axis. -/
theorem full_shears [Finite G] (n : NaturalSylowCoordinates T H A F 2)
    (e : A ≃* Multiplicative (Fin 3 → F.Carrier))
    (hN : omegaClosure T H ≤ normalizer (A : Set G))
    (α : omegaClosure T H →* ((Fin 3 → F.Carrier) ≃ₗ[F.Carrier] (Fin 3 → F.Carrier)))
    (hact : ∀ w v, (e (A.normalizerMonoidHom (inclusion hN w) v)).toAdd =
      α w (e v).toAdd) :
    Module.finrank F.Carrier (commonAxis α) = 2 ∧
      α.range = Shear.group (commonAxis α) := by
  let : Finite ((Fin 3 → F.Carrier) ≃ₗ[F.Carrier] (Fin 3 → F.Carrier)) :=
    Finite.of_injective (fun e : (Fin 3 → F.Carrier) ≃ₗ[F.Carrier] (Fin 3 → F.Carrier) => (e : _ → _)) DFunLike.coe_injective
  have hA : Nat.card A = Nat.card F.Carrier ^ 3 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card (Fin 3 → F.Carrier) = _
    rw [Nat.card_fun,Nat.card_fin]
  have hc := n.commutator_eq_common_axis_of_card (by decide) hN hA
  have hcard : Nat.card (commonAxis α) = Nat.card F.Carrier ^ 2 := by
    rw [←Nat.card_congr (axisEquiv e hN α hact),←hc,n.commutator_eq_fixed,n.card_fixed]
  have hd : Module.finrank F.Carrier (commonAxis α) = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := F.Carrier)] at hcard
    exact (Nat.pow_right_injective (Finite.one_lt_card (α := F.Carrier))) hcard
  have hk : Nat.card α.ker = Nat.card F.Carrier ^ 2 := by
    rw [action_ker e hN α hact]
    change Nat.card ((centralizer (A : Set G)).subgroupOf (omegaClosure T H)) = _
    rw [←inf_subgroupOf_left (centralizer (A : Set G)) (omegaClosure T H)]
    rw [Nat.card_congr (subgroupOfEquivOfLe (show
      omegaClosure T H ⊓ centralizer (A : Set G) ≤ omegaClosure T H from inf_le_left)).toEquiv]
    exact n.card_fixed
  have hW : Nat.card (omegaClosure T H) = (Nat.card F.Carrier ^ 2) * (Nat.card F.Carrier ^ 2) := by
    rw [Nat.card_congr n.coordinates.toEquiv]
    change Nat.card (Fin 2 → Fin 2 → F.Carrier) = _
    simp only [Nat.card_fun,Nat.card_fin,pow_two]
  have hr : Nat.card α.range = Nat.card F.Carrier ^ 2 := by
    have h := α.ker.card_mul_index
    rw [index_ker,hk,hW] at h
    exact Nat.mul_left_cancel (pow_pos Nat.card_pos _) h
  refine ⟨hd, eq_of_le_of_card_ge (action_le_shears e hN α hact n) ?_⟩
  rw [hr,←hcard]
  apply Shear.card_le
  have hdim := (commonAxis α).finrank_quotient_add_finrank
  rw [hd,Module.finrank_fin_fun] at hdim
  omega

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal

open Subgroup Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V H : Subgroup G}
  {D : ChosenModule T L V} {S : D.NonbinaryNaturalInput}

private theorem original_projection_injective (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) : Function.Injective c.projection := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro v hv
  apply mem_bot.mpr
  apply Subtype.ext
  apply mem_bot.mp
  rw [←hfixed]
  exact ⟨v.property,(c.projection_eq_one_iff v).mp hv⟩

def conjugateCoordinates (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G) :
    (V.map (MulAut.conj g).toMonoidHom) ≃* Multiplicative c.Space :=
  (V.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm.trans
    (MulEquiv.ofBijective c.projection
      ⟨by exact original_projection_injective c hfixed,c.projection_surjective⟩)

theorem conjugateCoordinates_intertwines (c : Coordinates D S.field)
    (hfixed : V ⊓ centralizer (L : Set G) = ⊥) (g : G)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G))
    (w : omegaClosure T H) (v : V.map (MulAut.conj g).toMonoidHom) :
    ((conjugateCoordinates c hfixed g)
      ((V.map (MulAut.conj g).toMonoidHom).normalizerMonoidHom (inclusion hN w) v)).toAdd =
      reciprocalAction c g hN w ((conjugateCoordinates c hfixed g) v).toAdd := by
  let A := V.map (MulAut.conj g).toMonoidHom
  let e : V ≃* A := V.equivMapOfInjective (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  change (c.projection (e.symm (A.normalizerMonoidHom (inclusion hN w) v))).toAdd =
    reciprocalAction c g hN w (c.projection (e.symm v)).toAdd
  rw [reciprocalAction_projection]
  congr 2
  apply e.injective
  rw [e.apply_symm_apply]
  apply Subtype.ext
  change (w : G) * (v : G) * (w : G)⁻¹ = _
  rw [coe_equivMapOfInjective_apply]
  have hz : ((reciprocalNormalizerHom g hN w : normalizer (V : Set G)) : G) =
      g⁻¹ * (w : G) * g := by
    change g⁻¹ * (w : G) * (g⁻¹)⁻¹ = _
    rw [inv_inv]
  simp only [MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
    normalizerMonoidHom_apply_apply_coe,hz]
  have hv : g * (e.symm v : G) * g⁻¹ = (v : G) :=
    congrArg Subtype.val (e.apply_symm_apply v)
  calc
    _ = (w : G) * (g * (e.symm v : G) * g⁻¹) * (w : G)⁻¹ := by rw [hv]
    _ = _ := by group

def sl3LinearReciprocal
    (a : ActionEquiv D.centralQuotientAction (linearNatural S.field 3))
    (f : InvariantFlag (.sl3 a)) (g : G) {m : ℕ}
    (n : NaturalSylowCoordinates T H (V.map (MulAut.conj g).toMonoidHom) S.field m)
    (hN : omegaClosure T H ≤ normalizer (V.map (MulAut.conj g).toMonoidHom : Set G)) :
    omegaClosure T H →* ((Fin 3 → S.field.Carrier) ≃ₗ[S.field.Carrier] (Fin 3 → S.field.Carrier)) where
  toFun w := LinearEquiv.ofBijective
    { toFun := reciprocalAction (.sl3 a) g hN w
      map_add' := (reciprocalAction (.sl3 a) g hN w).map_add
      map_smul' := sl3_reciprocal_action_linear a f g n hN w }
    ((reciprocalAction (.sl3 a) g hN).apply_bijective w)
  map_one' := by
    ext v
    change reciprocalAction (.sl3 a) g hN 1 v = v
    rw [map_one]; rfl
  map_mul' u v := by
    ext x
    change reciprocalAction (.sl3 a) g hN (u*v) x =
      reciprocalAction (.sl3 a) g hN u (reciprocalAction (.sl3 a) g hN v x)
    rw [map_mul]; rfl
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Reciprocal
