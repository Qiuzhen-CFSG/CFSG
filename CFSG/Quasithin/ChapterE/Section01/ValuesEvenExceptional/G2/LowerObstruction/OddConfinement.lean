module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.G2.LowerObstruction.Family
public import CFSG.Quasithin.ChapterE.Section01.Basic
public import Theory.GroupTheory.PGroup.NormalDirectPowerSection
public import Theory.Representation.AffineRootQuotient
public import Theory.Representation.TwoCoreScalarSaturation

/-!
# The odd G₂ confinement branch

The highest-root operators on the octonions are `1 + t D`. Scalar closure
of displacements in the intrinsic two-core forces the kernel on a full root
group to be either trivial or total. Thus its intrinsic quotient image cannot
have rank one when the field has more than two elements, excluding E.1.2(E1).

This module proves the exclusion, including the actual octonion calculation
and the transfer for every ambient conjugate. For `N = H ∩ L`, the map
`N → H/O₂(H)` has kernel `O₂(N)` by normality. This handles outer extensions
without requiring their action to be F-linear. The scalar-closure theorem in
`Theory.Representation.TwoCoreScalarSaturation` discharges the linear premise.
The resulting confinement theorem needs only a normal copy of the full model;
the stronger source assumptions of simplicity, G = LT, Sylow alignment and
SQTK are unnecessary for this branch. No weak-closure identity is assumed.

Source: Aschbacher--Smith E.1.1--6 and E.1.14(1), printed pp.209--210 and 214,
the latter citing Asc82a, *GF(2)-representations of finite groups*, Lemma 4.7.
The actual root operators come from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

public section
open Subgroup Atlas.G2 Atlas.G2.LieParabolicSetup Atlas.SplitOctonion

namespace CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction
universe u v
variable {G : Type u} {F : Type v} [Group G] [Finite G]
  [Field F] [Finite F] [CharP F 2]

/-- Conditional exclusion of the genuine odd source case for every ambient
conjugate of the full highest-root group. The general linear scalar-closure
theorem remains explicit here and is discharged in `not_odd` below. -/
theorem not_odd_of_scalar_core_saturation
    (hs : ∀ (X : Type u) [Group X] [Finite X]
      (ρ : X →* Module.End F (Carrier F)), Function.Injective ρ →
      ∀ (x y : X) (c : F), y ∈ pCore 2 X →
        ρ x - 1 = c • (ρ y - 1) → x ∈ pCore 2 X)
    (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e) (hAH : A ≤ H)
    (hF : 2 < Nat.card F) : ¬ ECaseOdd A H := by
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
  let q : N →* H ⧸ pCore 2 H := (QuotientGroup.mk' (pCore 2 H)).comp N.subtype
  have hq : q.ker = pCore 2 N := by
    change ((QuotientGroup.mk' (pCore 2 H)).comp N.subtype).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact (inferInstance : N.Normal).isSubnormal.pCore_subgroupOf 2
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
  have he : (q.comp rN).range =
      (((root L e).map (MulAut.conj g).toMonoidHom).subgroupOf H).map
        (QuotientGroup.mk' (pCore 2 H)) := by
    change ((QuotientGroup.mk' (pCore 2 H)).comp rH).range = _
    rw [MonoidHom.range_comp, hrr]
  intro ho
  obtain ⟨p, hp, hodd, hpq, hne, hcomm, hrank⟩ := ho
  apply Representation.affine_root_quotient_rank_ne_one ρ (hs N ρ hρ) rN D hlin q hq hF
  exact (Group.rank_congr (MulEquiv.subgroupCongr he)).trans hrank

/-- Application to the literal E-member interface and trapping subgroup.
The scalar two-core premise is discharged in `odd_member_le_shortOvergroup`
below. Normality handles all ambient conjugations, so the result also applies
to the source outer two-extensions. -/
theorem odd_member_le_shortOvergroup_of_scalar_core_saturation
    (hs : ∀ (X : Type u) [Group X] [Finite X]
      (ρ : X →* Module.End F (Carrier F)), Function.Injective ρ →
      ∀ (x y : X) (c : F), y ∈ pCore 2 X →
        ρ x - 1 = c • (ρ y - 1) → x ∈ pCore 2 X)
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (e : L ≃* Model F)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    {A H : Subgroup G} (hA : A ∈ family L e)
    (hH : IsEMember (T : Subgroup G) A H) (ho : ECaseOdd A H) :
    H ≤ shortOvergroup L (T : Subgroup G) e := by
  have hF2 : 2 < Nat.card F := by
    rw [hF]
    simpa only [pow_one] using
      (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mpr hf
  exact (not_odd_of_scalar_core_saturation hs L e hA hH.2.2.1 hF2 ho).elim

/-- A full highest-root group over a field of size greater than two, or any
ambient conjugate, cannot satisfy E.1.2(E1) in an overgroup. Scalar saturation
is proved for the faithful finite-dimensional octonion action. -/
theorem not_odd (L : Subgroup G) [L.Normal] (e : L ≃* Model F)
    {A H : Subgroup G} (hA : A ∈ family L e) (hAH : A ≤ H)
    (hF : 2 < Nat.card F) : ¬ ECaseOdd A H :=
  not_odd_of_scalar_core_saturation
    (fun _ _ _ ρ hρ => Representation.mem_twoCore_of_displacement_eq_smul ρ hρ)
    L e hA hAH hF

/-- The odd E-member confinement required by the G₂ lower obstruction in
E.1.14(1). All scalar-closure premises are discharged. The literal E-member
interface retains its ambient tau and Sylow clauses, and supplies `A ≤ H`.
Normality of `L` suffices, including when the source ambient group is an outer
two-extension of its generalized Fitting subgroup. -/
theorem odd_member_le_shortOvergroup
    (L : Subgroup G) [L.Normal] (T : Sylow 2 G) (e : L ≃* Model F)
    {f : ℕ} (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    {A H : Subgroup G} (hA : A ∈ family L e)
    (hH : IsEMember (T : Subgroup G) A H) (ho : ECaseOdd A H) :
    H ≤ shortOvergroup L (T : Subgroup G) e :=
  odd_member_le_shortOvergroup_of_scalar_core_saturation
    (fun _ _ _ ρ hρ => Representation.mem_twoCore_of_displacement_eq_smul ρ hρ)
    L T e hf hF hA hH ho

end CFSG.Quasithin.ChapterE.ExceptionalValues.G2.LowerObstruction
