module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility.Actions

/-!
# Irreducible constituents on the original source point and quotient

The aligned coordinates identify the literal subgroup V₁ ≤ V and the quotient
V/V₁ with the scalar line and the natural plane. Their actions are proved to
be the ones induced by ambient conjugation. Surjectivity of the original L₁
projection then proves irreducibility among all subgroups and noncentrality.

The generic kernel-coordinate construction generalizes the binary construction
in `Theory.Representation.PSL3Two.AffineConstituents` to the defining field.
Source: Aschbacher–Smith, G.2.1 and G.2.5(6–8), printed pp.332,335–336.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility
open Matrix.PSL3.LinearThree

/-- Irreducibility on a multiplicatively written elementary abelian group. -/
def SubgroupIrreducible {A M : Type*} [Group M] (act : A → M → M) : Prop :=
  ∀ K : Subgroup M, (∀ x v, v ∈ K → act x v ∈ K) → K = ⊥ ∨ K = ⊤

private theorem subgroup_irreducible {A M V : Type*} [Group M] [AddGroup V]
    (e : M ≃* Multiplicative V) (act : A → M → M) (ρ : A → V → V)
    (he : ∀ x v, (e (act x v)).toAdd = ρ x (e v).toAdd)
    (ht : ∀ v w, v ≠ 0 → w ≠ 0 → ∃ x, ρ x v = w) :
    SubgroupIrreducible act := by
  intro K hK
  rcases K.bot_or_exists_ne_one with h | ⟨v,hv,hv1⟩
  · exact Or.inl h
  · right
    apply top_unique
    intro w _
    by_cases hw : w = 1
    · exact hw ▸ K.one_mem
    have hv0 : (e v).toAdd ≠ 0 := by
      intro h; apply hv1; apply e.injective
      exact (Multiplicative.toAdd.injective h).trans e.map_one.symm
    have hw0 : (e w).toAdd ≠ 0 := by
      intro h; apply hw; apply e.injective
      exact (Multiplicative.toAdd.injective h).trans e.map_one.symm
    obtain ⟨x,hx⟩ := ht _ _ hv0 hw0
    have heq : act x v = w := e.injective (Multiplicative.toAdd.injective ((he x v).trans hx))
    exact heq ▸ hK x v hv

private theorem subgroup_noncentral {A M V : Type*} [Group M] [AddGroup V]
    (e : M ≃* Multiplicative V) (act : A → M → M) (ρ : A → V → V)
    (he : ∀ x v, (e (act x v)).toAdd = ρ x (e v).toAdd)
    (ht : Noncentral ρ) : Noncentral act := by
  obtain ⟨x,v,hv⟩ := ht
  refine ⟨x,e.symm (Multiplicative.ofAdd v), ?_⟩
  intro h
  have hh := he x (e.symm (Multiplicative.ofAdd v))
  rw [h, e.apply_symm_apply] at hh
  exact hv hh.symm

def markedKernelCoordinates {F M V W : Type*} [Field F] [Group M]
    [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
    (e : M ≃* Multiplicative V) (f : V →ₗ[F] W) :
    (f.toAddMonoidHom.toMultiplicative.comp e.toMonoidHom).ker ≃* Multiplicative f.ker where
  toFun x := Multiplicative.ofAdd ⟨(e x.val).toAdd, x.property⟩
  invFun x := ⟨e.symm (Multiplicative.ofAdd x.toAdd.val), by
    change f (e (e.symm (Multiplicative.ofAdd x.toAdd.val))).toAdd = 0
    rw [e.apply_symm_apply]
    exact x.toAdd.property⟩
  left_inv x := by apply Subtype.ext; exact e.symm_apply_apply x.val
  right_inv x := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (e.apply_symm_apply _)
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (e.map_mul x.val y.val)

variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  {d : Hypothesis D F n g h} (a : PointAlignment d)

/-- The literal source quotient map after the prescribed alignment. -/
def sourceProjection : D.V →* Multiplicative (Fin 2 → F) :=
  (tail F).toAddMonoidHom.toMultiplicative.comp (alignedCoordinates a).toMonoidHom

theorem sourceProjection_surjective : Function.Surjective (sourceProjection a) :=
  (tail_surjective F).comp (alignedCoordinates a).surjective

theorem sourceProjection_kernel : (sourceProjection a).ker = D.V₁.subgroupOf D.V := by
  ext v
  exact aligned_point a v

include a in
theorem sourcePoint_normal : (D.V₁.subgroupOf D.V).Normal := by
  rw [← sourceProjection_kernel a]
  infer_instance

/-- Coordinates on V₁ itself, with its actual inclusion into V. -/
def sourcePointEquiv : D.V₁.subgroupOf D.V ≃* Multiplicative F :=
  (MulEquiv.subgroupCongr (sourceProjection_kernel a).symm).trans
    ((markedKernelCoordinates (alignedCoordinates a) (tail F)).trans
      (naturalLineEquiv F).toAddEquiv.toMultiplicative)

@[simp] theorem sourcePointEquiv_apply (v : D.V₁.subgroupOf D.V) :
    (sourcePointEquiv a v).toAdd = (alignedCoordinates a v.val).toAdd 0 := rfl

/-- The quotient denominator is the original V₁, not a newly chosen kernel. -/
noncomputable def sourceQuotientEquiv [(D.V₁.subgroupOf D.V).Normal] :
    (D.V ⧸ D.V₁.subgroupOf D.V) ≃* Multiplicative (Fin 2 → F) :=
  (QuotientGroup.quotientMulEquivOfEq (sourceProjection_kernel a).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (sourceProjection_surjective a))

@[simp] theorem sourceQuotientEquiv_mk [(D.V₁.subgroupOf D.V).Normal] (v : D.V) :
    sourceQuotientEquiv a (QuotientGroup.mk' (D.V₁.subgroupOf D.V) v) = sourceProjection a v := rfl

def sourceConjugate (l : D.L₁) (v : D.V) : D.V :=
  ⟨(l : G) * v * (l : G)⁻¹,
    (mem_normalizer_iff.mp (normalizes_of_span D d.span_eq
      (((map_subtype_le _).trans inf_le_left) l.property)) v).mp v.property⟩

theorem sourceConjugate_coordinates (hn : 1 < n) (l : D.L₁) (v : D.V) :
    (alignedCoordinates a (sourceConjugate (d := d) l v)).toAdd =
      (localProjection a hn l).val.val *ᵥ (alignedCoordinates a v).toAdd :=
  aligned_natural_action a hn l v

def sourcePointAction (hn : 1 < n) (l : D.L₁) (v : D.V₁.subgroupOf D.V) :
    D.V₁.subgroupOf D.V :=
  ⟨sourceConjugate (d := d) l v.val, by
    change (sourceConjugate (d := d) l v.val : G) ∈ D.V₁
    rw [← aligned_point a, sourceConjugate_coordinates a hn]
    exact naturalLine_invariant F _ ((aligned_point a v.val).mpr v.property)⟩

theorem sourcePointEquiv_action (hn : 1 < n) (l : D.L₁) (v : D.V₁.subgroupOf D.V) :
    (sourcePointEquiv a (sourcePointAction a hn l v)).toAdd =
      scalarAction F (localProjection a hn l) (sourcePointEquiv a v).toAdd := by
  change (alignedCoordinates a (sourceConjugate (d := d) l v.val)).toAdd 0 = _
  rw [sourceConjugate_coordinates a hn]
  have hv := (mem_naturalLine F _).mp ((aligned_point a v.val).mpr v.property)
  simp only [scalarAction, mulVec, dotProduct, Fin.sum_univ_three, hv.1, hv.2,
    sourcePointEquiv_apply, mul_zero, add_zero]
  rfl

noncomputable def sourceQuotientAction [(D.V₁.subgroupOf D.V).Normal]
    (hn : 1 < n) (l : D.L₁) (v : D.V ⧸ D.V₁.subgroupOf D.V) :
    D.V ⧸ D.V₁.subgroupOf D.V :=
  (sourceQuotientEquiv a).symm (Multiplicative.ofAdd
    (blockAction F (localProjection a hn l) (sourceQuotientEquiv a v).toAdd))

theorem sourceQuotientEquiv_action [(D.V₁.subgroupOf D.V).Normal]
    (hn : 1 < n) (l : D.L₁) (v : D.V ⧸ D.V₁.subgroupOf D.V) :
    (sourceQuotientEquiv a (sourceQuotientAction a hn l v)).toAdd =
      blockAction F (localProjection a hn l) (sourceQuotientEquiv a v).toAdd :=
  congrArg Multiplicative.toAdd ((sourceQuotientEquiv a).apply_symm_apply _)

/-- The identified quotient action is the one induced by original ambient conjugation. -/
theorem sourceQuotientAction_mk [(D.V₁.subgroupOf D.V).Normal]
    (hn : 1 < n) (l : D.L₁) (v : D.V) :
    sourceQuotientAction a hn l (QuotientGroup.mk' (D.V₁.subgroupOf D.V) v) =
      QuotientGroup.mk' (D.V₁.subgroupOf D.V) (sourceConjugate (d := d) l v) := by
  apply (sourceQuotientEquiv a).injective
  apply Multiplicative.toAdd.injective
  rw [sourceQuotientEquiv_action, sourceQuotientEquiv_mk, sourceQuotientEquiv_mk]
  change blockAction F _ (tail F _) = tail F (alignedCoordinates a (sourceConjugate (d := d) l v)).toAdd
  rw [sourceConjugate_coordinates a hn, natural_quotient_action]
  rfl

/-- The source point and its literal quotient are irreducible among all subgroups. -/
theorem source_constituents_irreducible [(D.V₁.subgroupOf D.V).Normal] (hn : 1 < n) :
    SubgroupIrreducible (sourcePointAction a hn) ∧
      SubgroupIrreducible (sourceQuotientAction a hn) := by
  constructor
  · apply subgroup_irreducible (sourcePointEquiv a) _ _ (sourcePointEquiv_action a hn)
    intro v w hv hw
    obtain ⟨x,hx⟩ := scalar_transitive F v w hv hw
    obtain ⟨l,rfl⟩ := localProjection_surjective a hn x
    exact ⟨l,hx⟩
  · apply subgroup_irreducible (sourceQuotientEquiv a) _ _ (sourceQuotientEquiv_action a hn)
    intro v w hv hw
    obtain ⟨x,hx⟩ := block_transitive F v w hv hw
    obtain ⟨l,rfl⟩ := localProjection_surjective a hn x
    exact ⟨l,hx⟩

include d in
private theorem field_card_gt_two (hn : 1 < n) : 2 < Nat.card F := by
  rw [d.field_card]
  have hh : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (by omega)
  omega

theorem source_constituents_noncentral [(D.V₁.subgroupOf D.V).Normal] (hn : 1 < n) :
    Noncentral (sourcePointAction a hn) ∧ Noncentral (sourceQuotientAction a hn) :=
  ⟨subgroup_noncentral (sourcePointEquiv a) _ _ (sourcePointEquiv_action a hn)
    (scalar_noncentral F _ (localProjection_surjective a hn) (field_card_gt_two (d := d) hn)).1,
   subgroup_noncentral (sourceQuotientEquiv a) _ _ (sourceQuotientEquiv_action a hn)
    (plane_actions_noncentral F _ (localProjection_surjective a hn)).1⟩

include a in
theorem source_constituents_card [(D.V₁.subgroupOf D.V).Normal] :
    Nat.card (D.V₁.subgroupOf D.V) = 2 ^ n ∧
      Nat.card (D.V ⧸ D.V₁.subgroupOf D.V) = 2 ^ (2*n) := by
  constructor
  · exact (Nat.card_congr (sourcePointEquiv a).toEquiv).trans d.field_card
  · rw [Nat.card_congr (sourceQuotientEquiv a).toEquiv]
    change Nat.card (Fin 2 → F) = _
    rw [Nat.card_fun, Nat.card_fin, d.field_card, ← pow_mul, Nat.mul_comm n 2]

/-- All four model factors with the actual original L₁ action. -/
theorem source_flag_irreducible (hn : 1 < n) :
    AdditivelyIrreducible (fun l => naturalLineAction F (localProjection a hn l)) ∧
    AdditivelyIrreducible (fun l => naturalQuotientAction F (localProjection a hn l)) ∧
    AdditivelyIrreducible (fun l => dualPlaneAction F (localProjection a hn l)) ∧
    AdditivelyIrreducible (fun l => dualQuotientAction F (localProjection a hn l)) :=
  flag_irreducible F _ (localProjection_surjective a hn)

theorem source_flag_noncentral (hn : 1 < n) :
    Noncentral (fun l => naturalLineAction F (localProjection a hn l)) ∧
    Noncentral (fun l => naturalQuotientAction F (localProjection a hn l)) ∧
    Noncentral (fun l => dualPlaneAction F (localProjection a hn l)) ∧
    Noncentral (fun l => dualQuotientAction F (localProjection a hn l)) :=
  flag_noncentral F _ (localProjection_surjective a hn) (field_card_gt_two (d := d) hn)

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.ScalarConstituents.Irreducibility
