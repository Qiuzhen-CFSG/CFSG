module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.ComponentRank.Radical
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.Representation.TwoCoreScalarSaturation

/-!
# The G₂ component kernel from linear two-core saturation

A highest-root group acts on the octonions by `1 + t D`. Scalar closure of
linear two-core displacements therefore makes its intersection with a
subgroup's two-core either trivial or total. For an arbitrary ambient conjugate,
restrict the representation to H intersect L and undo that conjugation inside
the normal model carrier. Relative normality identifies the two-core of this
intersection with its intersection with O₂(H). This covers every ambient outer
extension using only normality of L.

The source E₂ clauses exclude the total-kernel case. The resulting trivial
kernel supplies the fixed-component confinement implication and, more strongly,
the exact rank in the literal quotient H/O∞(H) for either component alternative.
The conditional interfaces are retained, and the final four theorems discharge
scalar closure using the faithful finite-dimensional representation theorem
`Representation.mem_twoCore_of_displacement_eq_smul`. Thus this component
branch needs only normality of L, with no extra geometric premise, Sylow
alignment, simplicity or restriction on the ambient outer extension.

Source: Aschbacher--Smith E.1.1--6, printed pp.209--210, and E.1.14(1),
printed p.214, citing Asc82a Lemma 4.7. Root coordinates come from the licensed
ATLAS port; see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Theory.GroupTheory Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction.ComponentRank
universe u v
variable {G : Type u} {F : Type v} [Group G] [Finite G]
  [Field F]

/-- Scalar saturation makes a nontrivial kernel on any full ambient root
conjugate total. The representation is on H intersect L, so elements outside L
are never assumed to act linearly over F. -/
theorem family_le_core_of_inf_ne_bot_of_scalar_saturation
    (hs : ∀ (X : Type u) [Group X] [Finite X]
      (ρ : X →* Module.End F (Carrier F)), Function.Injective ρ →
      ∀ (x y : X) (c : F), y ∈ pCore 2 X →
        ρ x - 1 = c • (ρ y - 1) → x ∈ pCore 2 X)
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e) (hAH : A ≤ H)
    (hker : A.subgroupOf H ⊓ pCore 2 H ≠ ⊥) :
    A.subgroupOf H ≤ pCore 2 H := by
  obtain ⟨g, rfl⟩ := hA
  let rG : Multiplicative F →* G :=
    (MulAut.conj g).toMonoidHom.comp ((modelEmbedding L e).comp highestRootHom)
  have hrange : rG.range = (root L e).map (MulAut.conj g).toMonoidHom := by
    simp only [rG, MonoidHom.range_comp, root, highestRoot]
  have hrH (a) : rG a ∈ H := by
    apply hAH
    change rG a ∈ (root L e).map (MulAut.conj g).toMonoidHom
    rw [← hrange]
    exact ⟨a, rfl⟩
  have hrL (a) : rG a ∈ L :=
    (inferInstance : L.Normal).conj_mem _ (e.symm (highestRootHom a)).property g
  let N : Subgroup H := L.subgroupOf H
  let rH : Multiplicative F →* H := rG.codRestrict H hrH
  let rN : Multiplicative F →* N := rH.codRestrict N hrL
  let inclusion : N →* L :=
    (H.subtype.comp N.subtype).codRestrict L (fun x => x.property)
  let c : L ≃* Model F := (MulAut.conjNormal g⁻¹).trans e
  let j : N →* Model F := c.toMonoidHom.comp inclusion
  have hj : Function.Injective j := by
    intro x y h
    have h1 := c.injective h
    exact Subtype.ext (Subtype.ext (congrArg (fun z : L => (z : G)) h1))
  have hjr (a) : j (rN a) = rootA a.toAdd := by
    change e (MulAut.conjNormal g⁻¹
      ⟨g * (e.symm (highestRootHom a) : G) * g⁻¹, _⟩) = _
    have hc : (MulAut.conjNormal g⁻¹
      ⟨g * (e.symm (highestRootHom a) : G) * g⁻¹, hrL a⟩ : L) =
        e.symm (highestRootHom a) := by
      apply Subtype.ext
      simp [mul_assoc]
    rw [hc, e.apply_symm_apply]
    rfl
  let ρ : N →* Module.End F (Carrier F) :=
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp ((representation F).comp j)
  have hρ : Function.Injective ρ := by
    intro x y h
    apply hj
    apply representation_injective
    apply LinearEquiv.toLinearMap_injective
    exact h
  let D : Module.End F (Carrier F) := (rootA (1 : F)).val.toLinearMap - 1
  have hlin (a) : ρ (rN a) - 1 = a.toAdd • D := by
    change (j (rN a)).val.toLinearMap - 1 = _
    rw [hjr]
    apply LinearMap.ext
    intro v
    funext i
    fin_cases i <;>
      simp [D, rootA, Explicit.rootAEquiv, Explicit.rootALinear, Explicit.rootAApply,
        Matrix.vecHead, Matrix.vecTail]
  have hrr : rH.range = ((root L e).map (MulAut.conj g).toMonoidHom).subgroupOf H := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      change rG a ∈ (root L e).map (MulAut.conj g).toMonoidHom
      rw [← hrange]
      exact ⟨a, rfl⟩
    · intro hx
      have hx' : (x : G) ∈ rG.range := hrange.symm ▸ hx
      obtain ⟨a, ha⟩ := hx'
      exact ⟨a, Subtype.ext ha⟩
  have hcore : (pCore 2 H).subgroupOf N = pCore 2 N :=
    (inferInstance : N.Normal).isSubnormal.pCore_subgroupOf 2
  obtain ⟨x, hx, hx1⟩ :=
    ((((root L e).map (MulAut.conj g).toMonoidHom).subgroupOf H ⊓ pCore 2 H).bot_or_exists_ne_one).resolve_left hker
  obtain ⟨b, hb⟩ := (show x ∈ rH.range from hrr.symm ▸ hx.1)
  have hb0 : b.toAdd ≠ 0 := by
    intro hz
    have hb1 : b = 1 := Multiplicative.toAdd.injective hz
    exact hx1 (hb.symm.trans (hb1 ▸ map_one rH))
  have hbcore : rN b ∈ pCore 2 N := by
    rw [← hcore]
    change rH b ∈ pCore 2 H
    rw [hb]
    exact hx.2
  intro z hz
  obtain ⟨a, rfl⟩ := (show z ∈ rH.range from hrr.symm ▸ hz)
  have ha := hs N ρ hρ (rN a) (rN b) (a.toAdd / b.toAdd) hbcore (by
    rw [hlin, hlin, smul_smul, div_mul_cancel₀ _ hb0])
  rw [← hcore] at ha
  exact ha

/-- The nonzero proper kernel required by the fixed-component branch cannot
occur, conditional on scalar closure of linear two-core displacements. -/
theorem component_inf_core_eq_bot_of_scalar_saturation
    (hs : ∀ (X : Type u) [Group X] [Finite X]
      (ρ : X →* Module.End F (Carrier F)), Function.Injective ρ →
      ∀ (x y : X) (c : F), y ∈ pCore 2 X →
        ρ x - 1 = c • (ρ y - 1) → x ∈ pCore 2 X)
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H) :
    A.subgroupOf H ⊓ pCore 2 H = ⊥ := by
  by_contra hker
  exact component_not_le_core hm hc
    (family_le_core_of_inf_ne_bot_of_scalar_saturation hs L e hA hm.2.2.1 hker)

/-- Application to the literal first geometric premise of
`rank_lower_bound_of_component_geometry`. The orbit actor is local tau in H;
its defining quotient and the fixed-component alternative are retained.
The scalar-closure premise remains to be supplied by its independent producer. -/
theorem fixed_component_geometry_of_scalar_saturation
    (hs : ∀ (X : Type u) [Group X] [Finite X]
      (ρ : X →* Module.End F (Carrier F)), Function.Injective ρ →
      ∀ (x y : X) (c : F), y ∈ pCore 2 X →
        ρ x - 1 = c • (ρ y - 1) → x ∈ pCore 2 X)
    (L T : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H) :
    ∀ D : Subgroup (H ⧸ solvableRadical H),
      IsComponent (H ⧸ solvableRadical H) D →
      componentLayer (H ⧸ solvableRadical H) = conjugateJoin
        ((tau (T.subgroupOf H) (A.subgroupOf H)).map
          (QuotientGroup.mk' (solvableRadical H))) D →
      D = ⁅D, (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H))⁆ →
      A.subgroupOf H ⊓ pCore 2 H ≠ ⊥ → H ≤ shortOvergroup L T e := by
  intro _ _ _ _ hker
  exact (hker (component_inf_core_eq_bot_of_scalar_saturation hs L e hA hm hc)).elim

/-- In fact scalar saturation fixes the exact rank in the intrinsic radical
quotient for both component alternatives. This remains conditional until the
same scalar-closure premise is discharged. -/
theorem component_rank_eq_field_degree_of_scalar_saturation [CharP F 2]
    (hs : ∀ (X : Type u) [Group X] [Finite X]
      (ρ : X →* Module.End F (Carrier F)), Function.Injective ρ →
      ∀ (x y : X) (c : F), y ∈ pCore 2 X →
        ρ x - 1 = c • (ρ y - 1) → x ∈ pCore 2 X)
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) = f := by
  apply rank_radical_eq_of_inf_eq_bot L e hA hm.2.2.1 hF
  exact (component_inf_radical_eq_core hm hc).trans
    (component_inf_core_eq_bot_of_scalar_saturation hs L e hA hm hc)

variable [CharP F 2]

/-- In characteristic two every nontrivial two-core intersection with a member
of the full ambient highest-root family contains that whole member. Scalar
saturation is supplied by the faithful eight-dimensional representation. -/
theorem family_le_core_of_inf_ne_bot
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e) (hAH : A ≤ H)
    (hker : A.subgroupOf H ⊓ pCore 2 H ≠ ⊥) :
    A.subgroupOf H ≤ pCore 2 H := by
  apply family_le_core_of_inf_ne_bot_of_scalar_saturation (F := F) _ L e hA hAH hker
  intro X _ _ ρ hρ x y c hy hxy
  exact Representation.mem_twoCore_of_displacement_eq_smul ρ hρ x y c hy hxy

/-- Both source E₂ alternatives have trivial two-core kernel on the full
ambient highest-root family. Two-closedness of the radical and the literal
component alternative are retained through `ECaseComponent`. -/
theorem component_inf_core_eq_bot
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H) :
    A.subgroupOf H ⊓ pCore 2 H = ⊥ := by
  by_contra hker
  exact component_not_le_core hm hc
    (family_le_core_of_inf_ne_bot L e hA hm.2.2.1 hker)

/-- The first geometric premise of `rank_lower_bound_of_component_geometry`,
with no remaining scalar-saturation or geometry assumption. Its nontrivial
kernel contradicts `component_inf_core_eq_bot`. The quotient, local tau actor
and fixed-component witness are exactly those of the source E₂ case. -/
theorem fixed_component_geometry
    (L T : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H) :
    ∀ D : Subgroup (H ⧸ solvableRadical H),
      IsComponent (H ⧸ solvableRadical H) D →
      componentLayer (H ⧸ solvableRadical H) = conjugateJoin
        ((tau (T.subgroupOf H) (A.subgroupOf H)).map
          (QuotientGroup.mk' (solvableRadical H))) D →
      D = ⁅D, (A.subgroupOf H).map (QuotientGroup.mk' (solvableRadical H))⁆ →
      A.subgroupOf H ⊓ pCore 2 H ≠ ⊥ → H ≤ shortOvergroup L T e := by
  intro _ _ _ _ hker
  exact (hker (component_inf_core_eq_bot L e hA hm hc)).elim

/-- The literal image in H/O∞(H) has the full field degree as its rank,
in either source component alternative and every ambient outer extension.
No quotient-model identification or independent geometric premise is needed. -/
theorem component_rank_eq_field_degree
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {T A H : Subgroup G} (hA : A ∈ family L e)
    (hm : IsEMember T A H) (hc : ECaseComponent T A H)
    {f : ℕ} (hF : Nat.card F = 2 ^ f) :
    Group.rank ((A.subgroupOf H).map
      (QuotientGroup.mk' (solvableRadical H))) = f := by
  apply rank_radical_eq_of_inf_eq_bot L e hA hm.2.2.1 hF
  exact (component_inf_radical_eq_core hm hc).trans
    (component_inf_core_eq_bot L e hA hm hc)

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction.ComponentRank
