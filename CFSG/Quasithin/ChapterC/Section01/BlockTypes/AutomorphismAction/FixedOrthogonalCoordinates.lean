module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.OrthogonalInvolutionCoordinates
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.FieldInvolution
public import Theory.Representation.SL2OrthogonalCover.FixedField.Extraction
public import Theory.GroupAction.ElementaryFixedQuotient
public import Theory.FieldTheory.ScalarTwistedFixedPoints

/-!
# The original fixed group and its orthogonal core

An outer involution of a full-cover even block has a square-root fixed subgroup
on its elementary two-core. Thus the literal fixed-group projection onto the
fixed original quotient is surjective. Transport through the coherent field
alignment identifies this quotient with SL₂ over the coefficient fixed field,
and identifies the original fixed core with its full orthogonal cover.

The packet retains the literal fixed quotient projection, its precise kernel,
and the conjugation action. Its center-detection statement follows through the
same natural projection: a vector fixed by every fixed actor is in the smaller
cover's radical, whose inverse image is the original radical. This detects
centrality in the original group, including when the fixed field has order two.

Source: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532, and its fixed-block
applications in Lemma 2.4.23, printed p.537.
-/

public section
noncomputable section
open Subgroup Representation
open SL2NaturalOffenders.FixedField
namespace CFSG.Quasithin.ChapterC
variable (L : Type*) [Group L]

/-- The original fixed subgroup acts on its original fixed two-core as the full
orthogonal cover over the coefficient fixed field. -/
structure FixedOrthogonalCoordinates (n : ℕ) (a : MulAut L) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  [charTwo : CharP F 2]
  card : Nat.card F = 2 ^ n
  coefficient : F ≃+* F
  coefficient_ne : coefficient ≠ RingEquiv.refl F
  coefficient_involutive : Function.Involutive coefficient
  quotient : (quotientAut (pCore 2 L) a).fixedSubgroup ≃*
    SL2OrthogonalCover.SL (FixedBy.subfield F coefficient)
  actor : a.fixedSubgroup →* SL2OrthogonalCover.SL (FixedBy.subfield F coefficient)
  actor_projection : ∀ l, actor l = quotient (MulAut.fixedQuotientProjection (pCore 2 L) a l)
  actor_surjective : Function.Surjective actor
  actor_kernel : actor.ker = (pCore 2 L).subgroupOf a.fixedSubgroup
  core : (pCore 2 L).subgroupOf a.fixedSubgroup ≃*
    Multiplicative (SL2OrthogonalCover.Space (FixedBy.subfield F coefficient))
  conjugation_equivariant : ∀ (l : a.fixedSubgroup)
      (u : (pCore 2 L).subgroupOf a.fixedSubgroup),
    (core (MulAut.conjNormal l u)).toAdd = SL2OrthogonalCover.action (actor l) (core u).toAdd
  center_detection : ∀ u : (pCore 2 L).subgroupOf a.fixedSubgroup,
    (∀ l : a.fixedSubgroup, MulAut.conjNormal l u = u) → u.val.val ∈ center L

attribute [instance] FixedOrthogonalCoordinates.field FixedOrthogonalCoordinates.finite
  FixedOrthogonalCoordinates.charTwo
variable {L}

/-- The coefficient fixed field has precisely half the original binary degree. -/
theorem FixedOrthogonalCoordinates.fixed_field_parameters {n : ℕ} {a : MulAut L}
    (c : FixedOrthogonalCoordinates L n a) :
    ∃ m : ℕ, 0 < m ∧ n = 2 * m ∧
      Nat.card (FixedBy.subfield c.F c.coefficient) = 2 ^ m := by
  let K := FixedBy.subfield c.F c.coefficient
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨m, _, hm⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (m : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hm
  have hs := FiniteField.card_involution_fixed_sq c.coefficient
    c.coefficient_involutive c.coefficient_ne
  have hpow : 2 ^ ((m : ℕ) * 2) = 2 ^ n := by
    rw [pow_mul, ← hK]
    exact hs.trans c.card
  refine ⟨m, m.pos, ?_, hK⟩
  have he := Nat.pow_right_injective (by decide : 1 < 2) hpow
  omega

private theorem core_fixed_iff {n : ℕ} {a : MulAut L}
    (c : OrthogonalInvolutionCoordinates L n a) (u : pCore 2 L) :
    u.val ∈ a.fixedSubgroup ↔ (c.core u).toAdd ∈ fixedVectors c.actor := by
  rw [MulAut.mem_fixedSubgroup]
  change a u.val = u.val ↔ c.actor (c.core u).toAdd = (c.core u).toAdd
  rw [← c.core_equivariant]
  constructor
  · intro h
    exact congrArg (fun x : pCore 2 L => (c.core x).toAdd) (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (c.core.injective (Multiplicative.toAdd.injective h))

private def coreFixedEquiv {n : ℕ} {a : MulAut L}
    (c : OrthogonalInvolutionCoordinates L n a) :
    (pCore 2 L).subgroupOf a.fixedSubgroup ≃* Multiplicative (fixedVectors c.actor) where
  toFun u := Multiplicative.ofAdd
    ⟨(c.core ⟨u.val.val, u.property⟩).toAdd, (core_fixed_iff c _).mp u.val.property⟩
  invFun v :=
    let u := c.core.symm (Multiplicative.ofAdd (v.toAdd : SL2OrthogonalCover.Space c.F))
    ⟨⟨u.val, (core_fixed_iff c u).mpr (by
      change (c.core (c.core.symm _)).toAdd ∈ fixedVectors c.actor
      rw [c.core.apply_symm_apply]
      exact v.toAdd.property)⟩, u.property⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change (c.core.symm (c.core ⟨u.val.val, u.property⟩)).val = u.val.val
    exact congrArg Subtype.val (c.core.symm_apply_apply ⟨u.val.val, u.property⟩)
  right_inv v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (c.core.apply_symm_apply
      (Multiplicative.ofAdd (v.toAdd : SL2OrthogonalCover.Space c.F)))
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (c.core.map_mul
      ⟨u.val.val, u.property⟩ ⟨v.val.val, v.property⟩)

private theorem core_mem_center_of_radical {n : ℕ} {a : MulAut L}
    (c : OrthogonalInvolutionCoordinates L n a) (u : pCore 2 L)
    (hu : (c.core u).toAdd ∈ (SL2OrthogonalCover.form (F := c.F)).polarBilin.ker) :
    u.val ∈ center L := by
  rw [← SL2OrthogonalCover.fixed_radical] at hu
  rw [Subgroup.mem_center_iff]
  intro l
  have he : MulAut.conjNormal l u = u := by
    apply c.core.injective
    apply Multiplicative.toAdd.injective
    rw [c.conjugation_equivariant]
    exact hu _
  have hh := congrArg (fun v : pCore 2 L => v.val * l) he
  simpa only [MulAut.conjNormal_apply, MulEquiv.coe_mk, Subgroup.coe_mk,
    mul_assoc, inv_mul_cancel, mul_one] using hh

/-- The actual fixed group and fixed core inherit the marked cover; surjectivity
uses the square-root fixed count on the original elementary two-core. -/
theorem IsL2EvenBlock.fixed_orthogonal_coordinates {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : Nat.card (center L) = 2 ^ n)
    (a : MulAut L) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, quotientAut (pCore 2 L) a = MulAut.conj g) :
    Nonempty (FixedOrthogonalCoordinates L n a) := by
  let := hL.2.1.finite
  let : IsElementaryAbelian 2 (pCore 2 L) := hcore ▸ hL.2.1.elementary
  obtain ⟨c⟩ := hL.orthogonal_involution_coordinates hcore hz a ha houter
  let α := MulAut.congr c.quotient (quotientAut (pCore 2 L) a)
  have hα : α ^ 2 = 1 := by
    dsimp only [α]
    rw [← map_pow, ← map_pow, ha, map_one, map_one]
  have hαouter : ¬ ∃ g, α = MulAut.conj g :=
    fun h => houter ((MulAut.congr_inner_iff c.quotient _).mp h)
  obtain ⟨σ, hσne, hσ, β, A, e, B, hA, hβ, hAE, _, _, _, _, hAp⟩ :=
    SL2OrthogonalCover.FixedField.outer_involution_full_alignment n hL.1 c.card α
      c.actor c.actor_involutive c.normalizer_equivariant hα hαouter
  let eActor := fixedActorEquiv α σ β hβ
  let eV := fixedVectorEquiv σ c.actor A hAE
  have heV (g : α.fixedSubgroup) (v : fixedVectors c.actor) :
      eV ⟨SL2OrthogonalCover.action (g : SL2OrthogonalCover.SL c.F) v,
        SL2OrthogonalCover.FixedField.fixed_action_mem_of_intertwines α c.actor
          c.normalizer_equivariant g v⟩ = SL2OrthogonalCover.action (eActor g) (eV v) :=
    SL2OrthogonalCover.FixedField.fixed_cover_equivariance α σ β c.actor A hβ hAE hA g v _ rfl
  let eQuot := MulAut.fixedSubgroupEquivOfCompatible c.quotient
    (quotientAut (pCore 2 L) a) α (fun g => by
      change c.quotient (quotientAut (pCore 2 L) a g) =
        c.quotient (quotientAut (pCore 2 L) a (c.quotient.symm (c.quotient g)))
      rw [c.quotient.symm_apply_apply])
  let q := eQuot.trans eActor
  let p := MulAut.fixedQuotientProjection (pCore 2 L) a
  let ρ := q.toMonoidHom.comp p
  let ec := (coreFixedEquiv c).trans (AddEquiv.toMultiplicative eV)
  have hc : Nat.card (MulAut.characteristic (pCore 2 L) a).fixedSubgroup ^ 2 =
      Nat.card (pCore 2 L) := by
    have hh : (MulAut.characteristic (pCore 2 L) a).fixedSubgroup =
        (MulAut.characteristic (pCore 2 L) a).toMonoidHom.eqLocus (MonoidHom.id _) := by
      ext u
      exact MulAut.mem_fixedSubgroup _ _
    rw [hh]
    exact hL.full_cover_core_fixed_card hcore hz a ha houter
  have hp : Function.Surjective p :=
    MulAut.fixedQuotientProjection_surjective (pCore 2 L) a ha hc
  have hker : ρ.ker = (pCore 2 L).subgroupOf a.fixedSubgroup := by
    exact (MonoidHom.ker_comp_of_injective p q.toMonoidHom q.injective).trans
      (MulAut.fixedQuotientProjection_kernel (pCore 2 L) a)
  have hconj (l : a.fixedSubgroup) (u : (pCore 2 L).subgroupOf a.fixedSubgroup) :
      (ec (MulAut.conjNormal l u)).toAdd = SL2OrthogonalCover.action (ρ l) (ec u).toAdd := by
    have heq : (coreFixedEquiv c (MulAut.conjNormal l u)).toAdd =
        ⟨SL2OrthogonalCover.action (eQuot (p l)).val (coreFixedEquiv c u).toAdd,
          SL2OrthogonalCover.FixedField.fixed_action_mem_of_intertwines α c.actor
            c.normalizer_equivariant (eQuot (p l)) (coreFixedEquiv c u).toAdd⟩ := by
      apply Subtype.ext
      change (c.core (MulAut.conjNormal (l : L) ⟨u.val.val, u.property⟩)).toAdd = _
      rw [c.conjugation_equivariant]
      congr 1
      apply congrArg SL2OrthogonalCover.action
      exact (MulAut.fixedSubgroupEquivOfCompatible_apply c.quotient
        (quotientAut (pCore 2 L) a) α _ (p l)).symm
    change eV (coreFixedEquiv c (MulAut.conjNormal l u)).toAdd =
      SL2OrthogonalCover.action (eActor (eQuot (p l))) (eV (coreFixedEquiv c u).toAdd)
    rw [heq]
    exact heV (eQuot (p l)) (coreFixedEquiv c u).toAdd
  have hcenter (u : (pCore 2 L).subgroupOf a.fixedSubgroup)
      (hu : ∀ l : a.fixedSubgroup, MulAut.conjNormal l u = u) : u.val.val ∈ center L := by
    have hfix : (ec u).toAdd ∈ Representation.OneCohomology.fixed
        (SL2OrthogonalCover.action (F := FixedBy.subfield c.F σ)) := by
      intro g
      obtain ⟨l, rfl⟩ := q.surjective.comp hp g
      change SL2OrthogonalCover.action (ρ l) (ec u).toAdd = (ec u).toAdd
      rw [← hconj, hu]
    rw [SL2OrthogonalCover.fixed_radical] at hfix
    have hcoords := (SL2OrthogonalCover.mem_polar_ker _).mp hfix
    have hAz : A (c.core ⟨u.val.val, u.property⟩).toAdd ∈
        (SL2OrthogonalCover.form (F := c.F)).polarBilin.ker := by
      rw [SL2OrthogonalCover.mem_polar_ker]
      constructor
      · have hh := congrArg (fun x : FixedBy.subfield c.F σ => (x : c.F)) hcoords.1
        exact hh
      · have hh := congrArg (fun x : FixedBy.subfield c.F σ => (x : c.F)) hcoords.2
        exact hh
    have hpz : SL2OrthogonalCover.projection (A (c.core ⟨u.val.val, u.property⟩).toAdd) = 0 := by
      rw [← SL2OrthogonalCover.projection_kernel] at hAz
      exact hAz
    rw [hAp] at hpz
    have hu0 : SL2OrthogonalCover.projection (c.core ⟨u.val.val, u.property⟩).toAdd = 0 :=
      B.injective (hpz.trans B.map_zero.symm)
    apply core_mem_center_of_radical c ⟨u.val.val, u.property⟩
    rw [← SL2OrthogonalCover.projection_kernel]
    exact hu0
  refine ⟨{ F := c.F
            card := c.card
            coefficient := σ
            coefficient_ne := hσne
            coefficient_involutive := hσ
            quotient := q
            actor := ρ
            actor_projection := fun _ => rfl
            actor_surjective := q.surjective.comp hp
            actor_kernel := hker
            core := ec
            conjugation_equivariant := hconj
            center_detection := hcenter }⟩
end CFSG.Quasithin.ChapterC
