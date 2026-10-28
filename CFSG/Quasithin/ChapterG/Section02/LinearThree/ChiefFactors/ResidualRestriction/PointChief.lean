module
public import CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.IntersectionAssembly

/-!
# The scalar point is an actual larger-field chief subgroup

The intersection calculation proves V≤L₁. Consequently V₁ is a nontrivial
normal subgroup of L₁ whose scalar action is irreducible and noncentral.
It is a genuine chief subgroup of order 2^n and cannot be a natural
SL₂(2^n)-plane, whose order is 2^(2n).

This is an obstruction under the full source Hypothesis and the explicit
earlier U≤T and I=LU conclusions. It neither constructs an instance of
all ambient hypotheses nor claims a counterexample to the complete source
theorem. The source chief-factor owner must resolve the larger-field
statement; replacing O² by a derived or solvable residual is invalid.

Source: Aschbacher–Smith, G.2.1 and G.2.5(8), printed pp.332,335–336.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.PointChief
open ScalarConstituents ScalarConstituents.Irreducibility
variable {G : Type*} [Group G] [Finite G] {D : Setup G}
  {F : Type*} [Field F] [Finite F] {n : ℕ} {g h : G}
  {d : Hypothesis D F n g h} (a : PointAlignment d)

omit [Finite G] in
/-- Relative normality holds for the actual intersection with the marked point. -/
theorem point_normal : (D.V₁.subgroupOf D.L₁).Normal :=
  normal_subgroupOf_of_le_normalizer ((map_subtype_le _).trans inf_le_right)

/-- Once V≤L₁ is proved, the point intersection is exactly the original point. -/
def carrierEquiv (hpoint : D.V₁ ≤ D.L₁) :
    D.V₁.subgroupOf D.L₁ ≃* D.V₁.subgroupOf D.V :=
  (subgroupOfEquivOfLe hpoint).trans (subgroupOfEquivOfLe d.setup.point_le).symm

include a in
private theorem point_irreducible (hn : 1 < n) (hpoint : D.V₁ ≤ D.L₁)
    [ (D.V₁.subgroupOf D.L₁).Normal] :
    SubgroupIrreducible (fun l v => MulAut.conjNormal l v : D.L₁ →
      D.V₁.subgroupOf D.L₁ → D.V₁.subgroupOf D.L₁) := by
  let := sourcePoint_normal a
  let e := carrierEquiv (d := d) hpoint
  intro N hN
  have hInv : ∀ l z, z ∈ N.map e.toMonoidHom → sourcePointAction a hn l z ∈ N.map e.toMonoidHom := by
    rintro l z ⟨x,hx,rfl⟩
    exact ⟨MulAut.conjNormal l x,hN l x hx,rfl⟩
  rcases (source_constituents_irreducible a hn).1 _ hInv with hz | ht
  · left
    exact (map_eq_bot_iff_of_injective _ e.injective).mp hz
  · right
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [map_top_of_surjective _ e.surjective]
    exact ht

private theorem chief_bot_of_irreducible {K : Type*} [Group K]
    (X : Subgroup K) [X.Normal] (hX : X ≠ ⊥)
    (hi : SubgroupIrreducible (fun k x => MulAut.conjNormal k x : K → X → X)) :
    ChiefFactor.IsChief X ⊥ := by
  refine ⟨inferInstance,inferInstance,bot_lt_iff_ne_bot.mpr hX,?_⟩
  intro N hN _ hNX
  have hInv : ∀ k x, x ∈ N.subgroupOf X → MulAut.conjNormal k x ∈ N.subgroupOf X :=
    fun k x hx => hN.conj_mem x hx k
  rcases hi (N.subgroupOf X) hInv with hz | ht
  · left
    have hh := congrArg (fun Q : Subgroup X => Q.map X.subtype) hz
    simpa only [map_subgroupOf_eq_of_le hNX,Subgroup.map_bot] using hh
  · right
    have hh := congrArg (fun Q : Subgroup X => Q.map X.subtype) ht
    simpa only [map_subgroupOf_eq_of_le hNX,← MonoidHom.range_eq_map,Subgroup.range_subtype] using hh

include a in
/-- The extra scalar constituent is an actual chief interval of the literal L₁. -/
theorem point_chief (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) : ChiefFactor.IsChief (D.V₁.subgroupOf D.L₁) ⊥ := by
  have hpoint := d.setup.point_le.trans (IntersectionAssembly.Larger.V_le_residual a hn hUT hILU)
  let := point_normal (D := D)
  apply chief_bot_of_irreducible _ _ (point_irreducible a hn hpoint)
  intro hh
  have hm := congrArg (fun Q : Subgroup D.L₁ => Q.map D.L₁.subtype) hh
  rw [map_subgroupOf_eq_of_le hpoint,Subgroup.map_bot] at hm
  exact d.setup.point_ne_bot hm

include a in
/-- The chief subgroup's literal conjugation action is nontrivial. -/
theorem point_noncentral (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) [(D.V₁.subgroupOf D.L₁).Normal] :
    ∃ l : D.L₁, ∃ v : D.V₁.subgroupOf D.L₁, MulAut.conjNormal l v ≠ v := by
  have hpoint := d.setup.point_le.trans (IntersectionAssembly.Larger.V_le_residual a hn hUT hILU)
  let := sourcePoint_normal a
  let e := carrierEquiv (d := d) hpoint
  obtain ⟨l,v,hv⟩ := (source_constituents_noncentral a hn).1
  refine ⟨l,e.symm v,?_⟩
  intro hh
  have he : e (MulAut.conjNormal l (e.symm v)) = sourcePointAction a hn l (e (e.symm v)) := rfl
  rw [hh,e.apply_symm_apply] at he
  exact hv he.symm

include a in
/-- The actual scalar chief subgroup has order q, whereas a natural SL₂(q)-plane has order q². -/
theorem point_card (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) : Nat.card (D.V₁.subgroupOf D.L₁) = 2 ^ n := by
  have hpoint := d.setup.point_le.trans (IntersectionAssembly.Larger.V_le_residual a hn hUT hILU)
  let e := (carrierEquiv (d := d) hpoint).trans (sourcePointEquiv a)
  exact (Nat.card_congr e.toEquiv).trans d.field_card

include a in
/-- A precise obstruction to the larger-field all-natural-plane description.
This does not assert that the complete ambient source data have an instance. -/
theorem point_not_natural_plane (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) :
    ¬ Nonempty (D.V₁.subgroupOf D.L₁ ≃* Multiplicative (Fin 2 → F)) := by
  rintro ⟨e⟩
  have hc := Nat.card_congr e.toEquiv
  rw [point_card a hn hUT hILU] at hc
  change 2 ^ n = Nat.card (Fin 2 → F) at hc
  rw [Nat.card_fun,Nat.card_fin,d.field_card,← pow_mul] at hc
  exact (pow_lt_pow_right₀ (by decide : 1 < 2) (by omega : n < n * 2)).ne hc
open NoncentralChiefRefinement

/-- The original point intersection, normal in the actual local residual. -/
def pointNode : NormalNode D.L₁ := ⟨D.V₁.subgroupOf D.L₁,point_normal⟩

/-- The chief section has the literal denominator 1. -/
noncomputable def pointSectionEquiv : Section (⊥ : NormalNode D.L₁) (pointNode (D := D)) ≃*
    D.V₁.subgroupOf D.L₁ :=
  (QuotientGroup.quotientMulEquivOfEq (bot_subgroupOf (D.V₁.subgroupOf D.L₁))).trans
    QuotientGroup.quotientBot

include a in
/-- Order of the literal scalar chief section. -/
theorem point_section_card (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) :
    Nat.card (Section (⊥ : NormalNode D.L₁) (pointNode (D := D))) = 2 ^ n :=
  (Nat.card_congr (pointSectionEquiv (D := D)).toEquiv).trans (point_card a hn hUT hILU)

include a in
/-- The scalar chief interval satisfies the exact noncentral-two convention used in refinement. -/
theorem point_noncentral_two (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) :
    IsNoncentralTwo (⊥ : NormalNode D.L₁) (pointNode (D := D)) := by
  refine ⟨IsPGroup.of_card (point_section_card a hn hUT hILU),?_⟩
  intro hc
  let := point_normal (D := D)
  obtain ⟨l,v,hv⟩ := point_noncentral a hn hUT hILU
  rw [isCentral_iff_commutator_le,Subgroup.commutator_le] at hc
  have hh := hc l (mem_top _) v.val v.property
  change ⁅l,v.val⁆ ∈ (⊥ : Subgroup D.L₁) at hh
  have he : l * v.val * l⁻¹ = v.val := by
    have hh' := mem_bot.mp hh
    simpa only [commutatorElement_def,mul_inv_eq_one] using hh'
  exact hv (Subtype.ext he)

include a in
/-- The obstruction concerns the actual chief quotient, not a family label. -/
theorem point_section_not_natural_plane (hn : 1 < n) (hUT : D.U ≤ D.T)
    (hILU : I D g h = D.L ⊔ D.U) :
    ¬ Nonempty (Section (⊥ : NormalNode D.L₁) (pointNode (D := D)) ≃*
      Multiplicative (Fin 2 → F)) := by
  rintro ⟨e⟩
  exact point_not_natural_plane a hn hUT hILU
    ⟨(pointSectionEquiv (D := D)).symm.trans e⟩

end CFSG.Quasithin.ChapterG.Section02.LinearThree.ChiefFactors.ResidualRestriction.PointChief
