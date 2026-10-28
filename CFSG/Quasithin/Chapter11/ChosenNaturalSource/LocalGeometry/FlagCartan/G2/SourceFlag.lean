module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.G2.ModelFlag
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.FlagCartan.CartanGeometry.Normalization
public import Theory.AtlasPort.LinearGroups.G2.Perfectness

/-!
# The marked nonbinary G₂ flag in the original chosen module

Perfectness identifies the full nonbinary octonion group with its derived
group through the actual subtype map. The image of T intersect L is Sylow.
The intrinsic three-step flag pulls back through the original binary marking.
Its fixed and displacement descriptions prove invariance under the entire T,
including its outer action, without an assumed field-linear action of T.

Source: Aschbacher--Smith 11.0.2 and opening §11.1, pp.759--761.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation
open CFSG.Quasithin.Chapter12.Section02
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2

private theorem fixed_stable {k H W F : Type*} [Field k] [Field F] [Group H]
    [AddCommGroup W] [Module k W] [Module F W]
    (ρ : Representation k H W) (P : Subgroup H) [P.Normal]
    (U : Submodule F W) (hU : ∀ x, x ∈ U ↔ ∀ p : P, ρ p.val x = x)
    (t : H) (x : W) (hx : x ∈ U) : ρ t x ∈ U := by
  apply (hU _).mpr
  intro p
  let r : P := ⟨t⁻¹ * p.val * t, by
    simpa only [inv_inv] using (inferInstance : P.Normal).conj_mem p.val p.property t⁻¹⟩
  have he : ρ p.val (ρ t x) = ρ t (ρ r.val x) := by
    simp only [← Module.End.mul_apply, ← map_mul, r]
    congr 2
    group
  rw [he, (hU x).mp hx r]

private theorem step_stable {k H W F : Type*} [Field k] [Field F] [Group H]
    [AddCommGroup W] [Module k W] [Module F W]
    (ρ : Representation k H W) (P : Subgroup H) [P.Normal]
    (U V : Submodule F W)
    (hV : ∀ x, x ∈ V ↔ ∀ p : P, ρ p.val x - x ∈ U)
    (hU : ∀ t x, x ∈ U → ρ t x ∈ U)
    (t : H) (x : W) (hx : x ∈ V) : ρ t x ∈ V := by
  apply (hV _).mpr
  intro p
  let r : P := ⟨t⁻¹ * p.val * t, by
    simpa only [inv_inv] using (inferInstance : P.Normal).conj_mem p.val p.property t⁻¹⟩
  have he : ρ p.val (ρ t x) = ρ t (ρ r.val x) := by
    simp only [← Module.End.mul_apply, ← map_mul, r]
    congr 2
    group
  rw [he, ← map_sub]
  exact hU t _ ((hV x).mp hx r)

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))

/-- The original full G₂ marking, with no replacement by a group-family tag. -/
abbrev coordinates := Coordinates.g2 m

/-- The unchanged binary T-action, with its native octonion-quotient carrier explicit. -/
def ambientAction : Representation (ZMod 2) T (Atlas.G2.Natural.Space S.field.Carrier) :=
  (coordinates S m).sylowAction S

theorem field_card_gt_two : 2 < Nat.card S.field.Carrier := by
  rw [S.field.card_eq]
  exact (by simpa using Nat.pow_lt_pow_right (by decide : 1 < 2) S.nonbinary)

/-- The derived comparison is literally the inverse of subgroup inclusion. -/
def derivedEquiv : Atlas.G2.Model S.field.Carrier ≃* Atlas.G2.Natural.OrthogonalCover.SylowFlag.D S.field.Carrier := by
  let : Group.IsPerfect (Atlas.G2.Model S.field.Carrier) :=
    Atlas.G2.isPerfect (field_card_gt_two S)
  exact (MulEquiv.subgroupCongr Group.IsPerfect.commutator_eq_top |>.trans topEquiv).symm

@[simp] theorem derivedEquiv_coe (g : Atlas.G2.Model S.field.Carrier) :
    (derivedEquiv S g).val = g := rfl

/-- The unchanged component projection followed by the justified derived comparison. -/
def derivedMap : L →* Atlas.G2.Natural.OrthogonalCover.SylowFlag.D S.field.Carrier :=
  (derivedEquiv S).toMonoidHom.comp (coordinates S m).quotientMap

theorem derivedMap_surjective : Function.Surjective (derivedMap S m) :=
  (derivedEquiv S).surjective.comp (coordinates S m).quotientMap_surjective

/-- The actual Sylow intersection in L. -/
def innerSylow : Sylow 2 L :=
  (NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component).choose

theorem innerSylow_coe : (innerSylow (D := D) : Subgroup L) = (T : Subgroup G).subgroupOf L :=
  (NormalSylowQuotientAction.intersection_sylow T L D.sylow_normalizes_component).choose_spec

/-- The original inner Sylow, mapped through the actual marking. -/
def modelSylow : Sylow 2 (Atlas.G2.Natural.OrthogonalCover.SylowFlag.D S.field.Carrier) :=
  (innerSylow (D := D)).mapSurjective (derivedMap_surjective S m)

/-- The intrinsic flag for precisely this mapped Sylow. -/
def modelFlag : Atlas.G2.Natural.OrthogonalCover.SylowFlag.IntrinsicFlag S.field.Carrier (modelSylow S m) :=
  (Atlas.G2.Natural.OrthogonalCover.SylowFlag.exists_intrinsicFlag S.field.Carrier (modelSylow S m)).some

private theorem inner_action (r : L.subgroupOf (T : Subgroup G))
    (x : Atlas.G2.Natural.Space S.field.Carrier) :
    (ambientAction S m) r.val x =
      Atlas.G2.Natural.derivedAction S.field.Carrier
        (derivedMap S m ⟨r.val.val, r.property⟩) x := by
  obtain ⟨v,hv⟩ := (coordinates S m).projection_surjective (Multiplicative.ofAdd x)
  have hx : ((coordinates S m).projection v).toAdd = x := congrArg Multiplicative.toAdd hv
  rw [← hx]
  exact ((coordinates S m).conjugationAction_projection
    D.sylow_normalizes_component S.sylow_normalizes r.val v).trans
      ((coordinates S m).projection_component_conjugation ⟨r.val.val,r.property⟩ v)

private theorem forall_modelSylow_iff (p : Atlas.G2.Natural.OrthogonalCover.SylowFlag.D S.field.Carrier → Prop) :
    (∀ q : (modelSylow S m : Subgroup (Atlas.G2.Natural.OrthogonalCover.SylowFlag.D S.field.Carrier)), p q.val) ↔
      ∀ r : L.subgroupOf (T : Subgroup G), p (derivedMap S m ⟨r.val.val,r.property⟩) := by
  constructor
  · intro h r
    apply h ⟨derivedMap S m ⟨r.val.val,r.property⟩,?_⟩
    change _ ∈ (innerSylow (D := D) : Subgroup L).map (derivedMap S m)
    apply mem_map_of_mem
    rw [innerSylow_coe]
    exact r.val.property
  · intro h ⟨q,hq⟩
    change q ∈ (innerSylow (D := D) : Subgroup L).map (derivedMap S m) at hq
    obtain ⟨l,hl,rfl⟩ := hq
    rw [innerSylow_coe] at hl
    exact h ⟨⟨l.val,hl⟩,l.property⟩

private theorem modelFlag_first (x : Atlas.G2.Natural.Space S.field.Carrier) :
    x ∈ (modelFlag S m).space 0 ↔
      ∀ r : L.subgroupOf (T : Subgroup G), (ambientAction S m) r.val x = x := by
  exact ((modelFlag S m).first x).trans
    ((forall_modelSylow_iff S m (fun a =>
      Atlas.G2.Natural.derivedAction S.field.Carrier a x = x)).trans (forall_congr' fun r =>
      Iff.of_eq (congrArg (fun y => y = x) (inner_action S m r x).symm)))

private theorem modelFlag_next (i : Fin 2) (x : Atlas.G2.Natural.Space S.field.Carrier) :
    x ∈ (modelFlag S m).space i.succ ↔
      ∀ r : L.subgroupOf (T : Subgroup G),
        (ambientAction S m) r.val x - x ∈ (modelFlag S m).space i.castSucc := by
  exact ((modelFlag S m).next i x).trans
    ((forall_modelSylow_iff S m (fun a =>
      Atlas.G2.Natural.derivedAction S.field.Carrier a x - x ∈
        (modelFlag S m).space i.castSucc)).trans (forall_congr' fun r =>
      Iff.of_eq (congrArg (fun y => y - x ∈ (modelFlag S m).space i.castSucc)
        (inner_action S m r x).symm)))

/-- The entire ambient Sylow preserves each space, including its outer binary action. -/
theorem sylow_invariant (i : Fin 3) :
    ∀ t : T, ∀ x ∈ (modelFlag S m).space i,
      (ambientAction S m) t x ∈ (modelFlag S m).space i := by
  let R := L.subgroupOf (T : Subgroup G)
  let : R.Normal := ⟨by
    intro r hr t
    exact (D.sylow_normalizes_component t.property r.val).mp hr⟩
  have h0 := fixed_stable (ambientAction S m) R _ (modelFlag_first S m)
  have h1 := step_stable (ambientAction S m) R ((modelFlag S m).space 0)
    ((modelFlag S m).space 1) (modelFlag_next S m 0) h0
  have h2 := step_stable (ambientAction S m) R ((modelFlag S m).space 1)
    ((modelFlag S m).space 2) (modelFlag_next S m 1) h1
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The source flag on the original quotient and its original subgroup preimages. -/
def flag : InvariantFlag (coordinates S m) where
  space := (modelFlag S m).space
  dimension := (modelFlag S m).dimension
  nested := (modelFlag S m).nested
  invariant i := ((coordinates S m).sylow_normalizes_preimage_iff S _).mpr (sylow_invariant S m i)

/-- Inner-Sylow uniqueness, as required by the independent Cartan consumer. -/
theorem flag_inner_unique : (flag S m).IsInnerUnique := by
  intro i U hdim hn
  apply (modelFlag S m).unique i U hdim
  intro q x hx
  have hforall : ∀ q : (modelSylow S m : Subgroup (Atlas.G2.Natural.OrthogonalCover.SylowFlag.D S.field.Carrier)),
      Atlas.G2.Natural.derivedAction S.field.Carrier q.val x ∈ U := by
    refine (forall_modelSylow_iff S m (fun a =>
      Atlas.G2.Natural.derivedAction S.field.Carrier a x ∈ U)).mpr ?_
    intro r
    have hm := ((coordinates S m).mem_normalizer_preimage_iff U
      ⟨r.val.val,r.property⟩).mp (hn ⟨r.val.property,r.property⟩)
    exact (hm x).mpr hx
  exact hforall q

/-- Uniqueness for the full original T follows from the stronger inner version. -/
theorem flag_unique : (flag S m).IsUnique := by
  intro i U hd hn
  exact flag_inner_unique S m i U hd (inf_le_left.trans hn)

/-- Existence and both uniqueness statements for the original supplied marking. -/
theorem exists_unique_marked_flag :
    ∃ f : InvariantFlag (Coordinates.g2 m), f.IsUnique ∧ f.IsInnerUnique :=
  ⟨flag S m, flag_unique S m, flag_inner_unique S m⟩

/-- The constructed marked G₂ flag removes the uniqueness premise in Cartan existence. -/
theorem exists_flag_normalizing_cartan :
    ∃ X : Subgroup G, IsCartan T L X ∧
      ∀ i, X ≤ normalizer ((flag S m).Vi i : Set G) :=
  (flag S m).exists_normalizing_cartan (flag_inner_unique S m)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.G2
