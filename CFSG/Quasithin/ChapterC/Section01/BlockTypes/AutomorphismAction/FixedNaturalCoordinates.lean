module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction.FieldInvolution
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import Theory.Representation.SL2NaturalOffenders.FixedField.Natural
public import Theory.GroupAction.ElementaryFixedQuotient
public import Theory.FieldTheory.ScalarTwistedFixedPoints
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.NaturalExtensionRecognition
public import Theory.ElementaryAbelian.Injective

/-!
# The original fixed group of a centerless even block

When the original center is trivial, the elementary two-core is its marked
natural module. Simultaneous field descent identifies the fixed actor and
fixed core with SL₂ and its natural plane over the same coefficient fixed
field. The square-root fixed count makes the literal fixed quotient
projection surjective; its kernel is the original two-core intersected with
the fixed group.

For original binary degree at least four, the fixed field has degree at least
two. The marked natural extension then recognizes a centerless even block at
half the degree. Its two-core is precisely the original fixed two-core.

The private import is an intentional proof extension of AutomorphismAction:
it compares its defined actor with the prescribed quotient isomorphism. No
private implementation occurs in a public statement.

Source: Aschbacher–Smith, Lemma 2.4.12(2), printed p.532, and the fixed-block
application in Lemma 2.4.23(1), printed p.537.
-/

public section
noncomputable section
open Subgroup Representation
open SL2NaturalOffenders.FixedField
open Theory.SpecificGroups.SymplecticFour
namespace CFSG.Quasithin.ChapterC
variable (L : Type*) [Group L]

/-- The literal fixed quotient and fixed core carry the natural action over
the same coefficient fixed field. -/
structure FixedNaturalCoordinates (n : ℕ) (a : MulAut L) where
  F : Type
  [field : Field F]
  [finite : Finite F]
  [charTwo : CharP F 2]
  card : Nat.card F = 2 ^ n
  coefficient : F ≃+* F
  coefficient_ne : coefficient ≠ RingEquiv.refl F
  coefficient_involutive : Function.Involutive coefficient
  quotient : (quotientAut (pCore 2 L) a).fixedSubgroup ≃*
    Matrix.SpecialLinearGroup (Fin 2) (FixedBy.subfield F coefficient)
  actor : a.fixedSubgroup →* Matrix.SpecialLinearGroup (Fin 2) (FixedBy.subfield F coefficient)
  actor_projection : ∀ l, actor l = quotient (MulAut.fixedQuotientProjection (pCore 2 L) a l)
  actor_surjective : Function.Surjective actor
  actor_kernel : actor.ker = (pCore 2 L).subgroupOf a.fixedSubgroup
  core : (pCore 2 L).subgroupOf a.fixedSubgroup ≃*
    Multiplicative (Fin 2 → FixedBy.subfield F coefficient)
  conjugation_equivariant : ∀ (l : a.fixedSubgroup)
      (u : (pCore 2 L).subgroupOf a.fixedSubgroup),
    (core (MulAut.conjNormal l u)).toAdd = (actor l).val.mulVec (core u).toAdd

attribute [instance] FixedNaturalCoordinates.field FixedNaturalCoordinates.finite
  FixedNaturalCoordinates.charTwo
variable {L}

/-- The coefficient fixed field has half the original binary degree. -/
theorem FixedNaturalCoordinates.fixed_field_parameters {n : ℕ} {a : MulAut L}
    (c : FixedNaturalCoordinates L n a) :
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

section FixedCore
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {a : MulAut L}
variable (e : pCore 2 L ≃* Multiplicative (Fin 2 → F))
  (E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F))
  (he : ∀ u, (e (MulAut.characteristic (pCore 2 L) a u)).toAdd = E (e u).toAdd)

include he

private theorem natural_core_fixed_iff (u : pCore 2 L) :
    u.val ∈ a.fixedSubgroup ↔ (e u).toAdd ∈ fixedVectors E := by
  rw [MulAut.mem_fixedSubgroup]
  change a u.val = u.val ↔ E (e u).toAdd = (e u).toAdd
  rw [← he]
  constructor
  · intro h
    exact congrArg (fun x : pCore 2 L => (e x).toAdd) (Subtype.ext h)
  · intro h
    exact congrArg Subtype.val (e.injective (Multiplicative.toAdd.injective h))

private def naturalCoreFixedEquiv :
    (pCore 2 L).subgroupOf a.fixedSubgroup ≃* Multiplicative (fixedVectors E) where
  toFun u := Multiplicative.ofAdd
    ⟨(e ⟨u.val.val, u.property⟩).toAdd, (natural_core_fixed_iff e E he _).mp u.val.property⟩
  invFun v :=
    let u := e.symm (Multiplicative.ofAdd (v.toAdd : Fin 2 → F))
    ⟨⟨u.val, (natural_core_fixed_iff e E he u).mpr (by
      change (e (e.symm _)).toAdd ∈ fixedVectors E
      rw [e.apply_symm_apply]
      exact v.toAdd.property)⟩, u.property⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    change (e.symm (e ⟨u.val.val, u.property⟩)).val = u.val.val
    exact congrArg Subtype.val (e.symm_apply_apply ⟨u.val.val, u.property⟩)
  right_inv v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (e.apply_symm_apply
      (Multiplicative.ofAdd (v.toAdd : Fin 2 → F)))
  map_mul' u v := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact congrArg Multiplicative.toAdd (e.map_mul
      ⟨u.val.val, u.property⟩ ⟨v.val.val, v.property⟩)
end FixedCore

/-- An actual outer involution of a centerless block supplies the marked
fixed-natural coordinates, with no residual compatibility assumption. -/
theorem IsL2EvenBlock.fixed_natural_coordinates {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : center L = ⊥)
    (a : MulAut L) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, quotientAut (pCore 2 L) a = MulAut.conj g) :
    Nonempty (FixedNaturalCoordinates L n a) := by
  let := hL.2.1.finite
  let : IsElementaryAbelian 2 (pCore 2 L) := hcore ▸ hL.2.1.elementary
  obtain ⟨F, _, _, hF, _, ρ, ⟨m⟩, hm⟩ := hL.2.2
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  have hz' : blockFixed L = ⊥ := by
    change (center L).subgroupOf (blockU L) = ⊥
    rw [hz, bot_subgroupOf]
  let q₀ := QuotientGroup.mk' (blockFixed L)
  have hq₀ : Function.Bijective q₀ := ⟨by
    apply q₀.ker_eq_bot_iff.mp
    rw [QuotientGroup.ker_mk', hz'], QuotientGroup.mk'_surjective _⟩
  let e : pCore 2 L ≃* Multiplicative (Fin 2 → F) :=
    ((MulEquiv.subgroupCongr hcore).trans (MulEquiv.ofBijective q₀ hq₀)).trans m.moduleIso
  let A := m.moduleAction a
  let E₀ : (Fin 2 → F) ≃+ (Fin 2 → F) :=
    { toFun v := (A (Multiplicative.ofAdd v)).toAdd
      invFun v := (A.symm (Multiplicative.ofAdd v)).toAdd
      left_inv v := A.symm_apply_apply v
      right_inv v := A.apply_symm_apply v
      map_add' v w := A.map_mul v w }
  let E : (Fin 2 → F) ≃ₗ[ZMod 2] (Fin 2 → F) :=
    { E₀ with map_smul' := fun c v => ZMod.map_smul E₀ c v }
  have hE : Function.Involutive E := by
    intro v
    have hA : A ^ 2 = 1 := by dsimp only [A]; rw [← map_pow, ha, map_one]
    exact congrArg Multiplicative.toAdd (DFunLike.congr_fun hA (Multiplicative.ofAdd v))
  have he (g : Matrix.SpecialLinearGroup (Fin 2) F) (v : Fin 2 → F) :
      E (g.val.mulVec v) = (m.quotientAction a g).val.mulVec (E v) := by
    have hh := m.actions_compatible a g (Multiplicative.ofAdd v)
    have hv : Multiplicative.ofAdd (g.val.mulVec v) = ρ g (Multiplicative.ofAdd v) :=
      Multiplicative.toAdd.injective (hm g (Multiplicative.ofAdd v)).symm
    change (A (Multiplicative.ofAdd (g.val.mulVec v))).toAdd = _
    rw [hv]
    exact (congrArg Multiplicative.toAdd hh).trans (hm _ _)
  have heκ (u : pCore 2 L) :
      (e (MulAut.characteristic (pCore 2 L) a u)).toAdd = E (e u).toAdd := by
    change (m.moduleIso (QuotientGroup.mk' (blockFixed L)
      (MulEquiv.subgroupCongr hcore (MulAut.characteristic (pCore 2 L) a u)))).toAdd =
      (m.moduleAction a (m.moduleIso (QuotientGroup.mk' (blockFixed L)
        (MulEquiv.subgroupCongr hcore u)))).toAdd
    rw [m.moduleAction_mk]
    congr 2
  have hel (l : L) (u : pCore 2 L) :
      (e (MulAut.conjNormal l u)).toAdd = (m.actor l).val.mulVec (e u).toAdd := by
    change (m.moduleIso (QuotientGroup.mk' (blockFixed L)
      (MulEquiv.subgroupCongr hcore (MulAut.conjNormal l u)))).toAdd = _
    have hconj : MulEquiv.subgroupCongr hcore (MulAut.conjNormal l u) =
        blockConjugate L l (MulEquiv.subgroupCongr hcore u) := by
      apply Subtype.ext
      rfl
    rw [hconj, m.intertwining]
    exact hm _ _
  let α := m.quotientAction a
  have hα : α ^ 2 = 1 := by dsimp only [α]; rw [← map_pow, ha, map_one]
  have hαouter : ¬ ∃ g, α = MulAut.conj g :=
    fun h => houter ((MulAut.congr_inner_iff m.quotientIso _).mp h)
  obtain ⟨σ, hσne, hσ, eActor, eV, heV⟩ :=
    outer_involution_fixed_natural α E hE he hα hαouter
  let eQuot := MulAut.fixedSubgroupEquivOfCompatible m.quotientIso
    (quotientAut (pCore 2 L) a) α (fun g => by
      change m.quotientIso (quotientAut (pCore 2 L) a g) =
        m.quotientIso (quotientAut (pCore 2 L) a (m.quotientIso.symm (m.quotientIso g)))
      rw [m.quotientIso.symm_apply_apply])
  let q := eQuot.trans eActor
  let p := MulAut.fixedQuotientProjection (pCore 2 L) a
  let actor := q.toMonoidHom.comp p
  let ef := naturalCoreFixedEquiv e E heκ
  let ec := ef.trans (AddEquiv.toMultiplicative eV)
  have hc : Nat.card (MulAut.characteristic (pCore 2 L) a).fixedSubgroup ^ 2 =
      Nat.card (pCore 2 L) := by
    have hh : (MulAut.characteristic (pCore 2 L) a).fixedSubgroup =
        (MulAut.characteristic (pCore 2 L) a).toMonoidHom.eqLocus (MonoidHom.id _) := by
      ext u
      exact MulAut.mem_fixedSubgroup _ _
    rw [hh]
    exact hL.centerless_core_fixed_card hcore hz a ha houter
  have hp : Function.Surjective p :=
    MulAut.fixedQuotientProjection_surjective (pCore 2 L) a ha hc
  have hker : actor.ker = (pCore 2 L).subgroupOf a.fixedSubgroup :=
    (MonoidHom.ker_comp_of_injective p q.toMonoidHom q.injective).trans
      (MulAut.fixedQuotientProjection_kernel (pCore 2 L) a)
  have hconj (l : a.fixedSubgroup) (u : (pCore 2 L).subgroupOf a.fixedSubgroup) :
      (ec (MulAut.conjNormal l u)).toAdd = (actor l).val.mulVec (ec u).toAdd := by
    have heq : (ef (MulAut.conjNormal l u)).toAdd =
        ⟨(eQuot (p l)).val.val.mulVec (ef u).toAdd,
          fixed_action_mem_of_intertwines α E he (eQuot (p l)) (ef u).toAdd⟩ := by
      apply Subtype.ext
      change (e (MulAut.conjNormal (l : L) ⟨u.val.val, u.property⟩)).toAdd = _
      rw [hel]
      congr 1
      exact congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F => g.val)
        (MulAut.fixedSubgroupEquivOfCompatible_apply m.quotientIso
          (quotientAut (pCore 2 L) a) α _ (p l)).symm
    change eV (ef (MulAut.conjNormal l u)).toAdd =
      (eActor (eQuot (p l))).val.mulVec (eV (ef u).toAdd)
    rw [heq]
    exact heV (eQuot (p l)) (ef u).toAdd
  refine ⟨{ F := F
            card := hF
            coefficient := σ
            coefficient_ne := hσne
            coefficient_involutive := hσ
            quotient := q
            actor := actor
            actor_projection := fun _ => rfl
            actor_surjective := q.surjective.comp hp
            actor_kernel := hker
            core := ec
            conjugation_equivariant := hconj }⟩

/-- The fixed-natural packet supplies the elementary natural extension used
by block recognition. -/
def FixedNaturalCoordinates.naturalExtension [Finite L] {n : ℕ} {a : MulAut L}
    (c : FixedNaturalCoordinates L n a)
    (hQ : IsElementaryAbelian 2 ((pCore 2 L).subgroupOf a.fixedSubgroup))
    (hF : 2 < Nat.card (FixedBy.subfield c.F c.coefficient)) :
    NaturalExtension (F := FixedBy.subfield c.F c.coefficient)
      ((pCore 2 L).subgroupOf a.fixedSubgroup) := by
  let K := FixedBy.subfield c.F c.coefficient
  let : Algebra (ZMod 2) K := ZMod.algebra K 2
  exact naturalExtensionOfNatural hQ c.actor c.actor_surjective c.actor_kernel
    hF c.core c.conjugation_equivariant

/-- The marked fixed group is a centerless even block at half the degree. -/
theorem FixedNaturalCoordinates.fixed_block [Finite L] {n : ℕ} {a : MulAut L}
    (c : FixedNaturalCoordinates L n a)
    (hQ : IsElementaryAbelian 2 ((pCore 2 L).subgroupOf a.fixedSubgroup))
    (hn : 4 ≤ n) :
    ∃ m : ℕ, 1 < m ∧ n = 2 * m ∧ IsL2EvenBlock a.fixedSubgroup m ∧
      pCore 2 a.fixedSubgroup = (pCore 2 L).subgroupOf a.fixedSubgroup ∧
      center a.fixedSubgroup = ⊥ := by
  obtain ⟨m, hm, hnm, hcard⟩ := c.fixed_field_parameters
  have hm' : 1 < m := by omega
  let K := FixedBy.subfield c.F c.coefficient
  have hc : 2 < Nat.card K := by
    rw [hcard]
    exact lt_of_lt_of_le (by decide : 2 < 2 ^ 2)
      (Nat.pow_le_pow_right (by decide : 0 < 2) hm')
  let d := c.naturalExtension hQ hc
  have hcenter : center a.fixedSubgroup = ⊥ := by
    apply bot_unique
    intro z hz
    have hzQ : z ∈ (pCore 2 L).subgroupOf a.fixedSubgroup := by
      rw [← d.centralizer_eq]
      exact center_le_centralizer _ hz
    let u : (pCore 2 L).subgroupOf a.fixedSubgroup := ⟨z, hzQ⟩
    let : Algebra (ZMod 2) K := ZMod.algebra K 2
    have hv : (c.core u).toAdd ∈ OneCohomology.fixed (SL2OrthogonalCover.binaryNatural (F := K)) := by
      intro g
      obtain ⟨l, rfl⟩ := c.actor_surjective g
      change (c.actor l).val.mulVec (c.core u).toAdd = (c.core u).toAdd
      rw [← c.conjugation_equivariant]
      have hu : MulAut.conjNormal l u = u := by
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (mem_center_iff.mp hz l)
      rw [hu]
    rw [SL2OrthogonalCover.natural_fixed] at hv
    have hu : u = 1 := c.core.injective (by
      apply Multiplicative.toAdd.injective
      rw [map_one]
      exact hv)
    exact congrArg Subtype.val hu
  exact ⟨m, hm', hnm, isL2EvenBlock_of_naturalExtension d hm' hcard, d.core_eq hc, hcenter⟩

/-- The actual centerless source block recognizes its outer fixed group and
identifies the fixed group's literal two-core. -/
theorem IsL2EvenBlock.fixed_natural_block {n : ℕ} (hL : IsL2EvenBlock L n)
    (hcore : pCore 2 L = blockU L) (hz : center L = ⊥)
    (a : MulAut L) (ha : a ^ 2 = 1)
    (houter : ¬ ∃ g, quotientAut (pCore 2 L) a = MulAut.conj g) (hn : 4 ≤ n) :
    ∃ m : ℕ, 1 < m ∧ n = 2 * m ∧ IsL2EvenBlock a.fixedSubgroup m ∧
      pCore 2 a.fixedSubgroup = (pCore 2 L).subgroupOf a.fixedSubgroup ∧
      center a.fixedSubgroup = ⊥ := by
  let := hL.2.1.finite
  let : IsElementaryAbelian 2 (pCore 2 L) := hcore ▸ hL.2.1.elementary
  let f : ((pCore 2 L).subgroupOf a.fixedSubgroup) →* pCore 2 L :=
    { toFun u := ⟨u.val.val, u.property⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : pCore 2 L => x.val) huv
  have hQ : IsElementaryAbelian 2 ((pCore 2 L).subgroupOf a.fixedSubgroup) :=
    IsElementaryAbelian.of_injective f hf
  obtain ⟨c⟩ := hL.fixed_natural_coordinates hcore hz a ha houter
  exact c.fixed_block hQ hn
end CFSG.Quasithin.ChapterC
