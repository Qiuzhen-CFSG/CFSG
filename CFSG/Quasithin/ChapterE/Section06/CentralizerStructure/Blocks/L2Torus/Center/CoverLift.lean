module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Blocks.L2Torus.Center.Natural
public import Theory.ElementaryAbelian.VectorSpace
public import Theory.Representation.FirstCohomologyDuality
public import Theory.Representation.SpecialLinearNatural
public import Mathlib.Algebra.Algebra.ZMod
public import Mathlib.LinearAlgebra.QuadraticForm.Radical

/-!
# Lifting the root-fixed line through the genuine natural cover

For a marked short group L with quotient SL₂(F), |F| = 2ⁿ and n > 1,
two-perfectness implies perfectness: its abelianization is an image of O₂(L).
The Three-Subgroup Lemma then gives [U(L),L] = U(L). Conjugation on the
elementary abelian U(L) is therefore a full binary representation, factoring
through SL₂(F) because O₂(L) centralizes U(L). The marked natural quotient
is its literal surjective covering projection, with fixed kernel C_U(L).

The explicit earlier-source input `RankOneCoverTheorem` retains the
three-dimensional orthogonal realization of the universal cover from
I.2.3(1) and all of I.2.3(3). Applying it to this constructed cover fixes the
preimage of the first coordinate line under the root group. Since S is the
full preimage of that root group, this proves `a.rootLine ≤ C_L(S)`.
The result is conditional only on the indicated earlier-source theorem;
it does not assert a proof of I.2.3 or use C.1.13.

The covering construction adapts the independently proved construction in
Chapter15's `LinearTwo.Centralizer.CoveringLayer.Module`, with perfectness
proved here and no import from Chapter15.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.1.7 and
C.1.12, printed pp.123–124; I.1.5 and I.2.3, pp.408 and 413;
the application in E.6.7, p.246.
-/

@[expose] public section

open Subgroup Representation
open scoped IsMulCommutative commutatorElement MatrixGroups
namespace CFSG.Quasithin.ChapterE.Section06.L2Torus.CoverLift
universe u v
variable {L : Type u} {F : Type v} [Group L] [Field F] {B : Subgroup L}

section Perfectness
variable [Finite F] [CharP F 2]

/-- Perfectness follows from two-perfectness and the marked rank-one quotient. -/
theorem marked_isPerfect (hshort : ChapterC.IsShort L) (a : MarkedBlockModel L B F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) : Group.IsPerfect L := by
  have hpow : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hcard : 1 < Nat.card Fˣ := by rw [Nat.card_units, hF]; omega
  let : Nontrivial Fˣ := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨t, ht⟩ := exists_ne (1 : Fˣ)
  have htF : (t : F) ≠ 1 := fun h => ht (Units.ext h)
  have ht2 : (t : F) ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h | h
    · exact htF h
    · exact htF (h.trans (CharTwo.neg_eq 1))
  let : Group.IsPerfect SL(2, F) := ⟨Matrix.SL2.commutator_eq_top t.ne_zero ht2⟩
  have hmap : (commutator L).map a.linearMap = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr a.linearMap_surjective,
      ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  let q := QuotientGroup.mk' (commutator L)
  have hq : Function.Surjective (q.comp (pCore 2 L).subtype) := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (commutator L) y
    have hl : a.linearMap l ∈ (commutator L).map a.linearMap := by rw [hmap]; trivial
    obtain ⟨d, hd, he⟩ := hl
    have hk : l * d⁻¹ ∈ pCore 2 L := by
      rw [← a.linearMap_ker]
      change a.linearMap (l * d⁻¹) = 1
      rw [map_mul, map_inv, he, mul_inv_cancel]
    refine ⟨⟨l * d⁻¹, hk⟩, ?_⟩
    change q (l * d⁻¹) = q l
    have hdq : q d = 1 := (QuotientGroup.eq_one_iff d).mpr hd
    rw [map_mul, map_inv, hdq, inv_one, mul_one]
  exact ⟨hshort.twoPerfect (commutator L) inferInstance
    (pCore_isPGroup.of_surjective _ hq)⟩
end Perfectness

theorem blockU_full_commutator [Group.IsPerfect L] :
    ⁅ChapterC.blockU L, (⊤ : Subgroup L)⁆ = ChapterC.blockU L := by
  let D := ⁅ChapterC.blockU L, (⊤ : Subgroup L)⁆
  let q := QuotientGroup.mk' D
  have ht : (⊤ : Subgroup L).map q = ⊤ := map_top_of_surjective q (QuotientGroup.mk'_surjective D)
  have hd : D.map q = ⊥ := by rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hdouble : ⁅⁅(pCore 2 L).map q, (⊤ : Subgroup (L ⧸ D))⁆, (⊤ : Subgroup (L ⧸ D))⁆ = ⊥ := by
    rw [← ht, ← map_commutator, ← map_commutator]
    exact hd
  have hp : ⁅(⊤ : Subgroup (L ⧸ D)), (⊤ : Subgroup (L ⧸ D))⁆ = ⊤ := by
    rw [← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  have hz : ⁅⁅(⊤ : Subgroup (L ⧸ D)), (⊤ : Subgroup (L ⧸ D))⁆, (pCore 2 L).map q⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate (by simpa only [commutator_comm] using hdouble) hdouble
  rw [hp, commutator_comm] at hz
  have hu : (ChapterC.blockU L).map q = ⊥ := by
    change (⁅pCore 2 L, (⊤ : Subgroup L)⁆).map q = ⊥
    rw [map_commutator, ht]
    exact hz
  exact le_antisymm (commutator_le_left _ _) (by
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff _).mp hu)

section Construction
variable [IsElementaryAbelian 2 (ChapterC.blockU L)]

noncomputable def blockBinaryAction : Representation (ZMod 2) L (Additive (ChapterC.blockU L)) where
  toFun l := (MulAut.conjNormal (H := ChapterC.blockU L) l).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul ((MulAut.conjNormal (H := ChapterC.blockU L) 1) u.toMul) = u
    rw [map_one]
    rfl
  map_mul' a b := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul ((MulAut.conjNormal (H := ChapterC.blockU L) (a * b)) u.toMul) = _
    rw [map_mul]
    rfl

theorem blockBinaryAction_apply (l : L) (u : Additive (ChapterC.blockU L)) :
    blockBinaryAction l u = Additive.ofMul (ChapterC.blockConjugate L l u.toMul) := rfl

theorem blockBinaryAction_full [Group.IsPerfect L] :
    Coinvariants.ker (blockBinaryAction (L := L)) = ⊤ := by
  let C := Coinvariants.ker (blockBinaryAction (L := L))
  let D : Subgroup (ChapterC.blockU L) := C.toAddSubgroup.toSubgroup'
  have hUD : ChapterC.blockU L ≤ D.map (ChapterC.blockU L).subtype := by
    apply (blockU_full_commutator (L := L)).symm.le.trans
    apply commutator_le.mpr
    intro u hu l _
    let v : ChapterC.blockU L := ⟨u, hu⟩
    have hc := Coinvariants.sub_mem_ker (ρ := blockBinaryAction (L := L)) l (Additive.ofMul v⁻¹)
    let w := (blockBinaryAction l (Additive.ofMul v⁻¹) - Additive.ofMul v⁻¹).toMul
    refine ⟨w, hc, ?_⟩
    simp only [w, sub_eq_add_neg]
    change l * u⁻¹ * l⁻¹ * (u⁻¹)⁻¹ = ⁅u, l⁆
    rw [inv_inv]
    have he := congrArg Subtype.val (mul_comm (ChapterC.blockConjugate L l v⁻¹) v)
    simpa only [ChapterC.blockConjugate, v, coe_mul, coe_inv, commutatorElement_def, mul_assoc] using he
  apply top_unique
  intro u _
  obtain ⟨v, hv, he⟩ := hUD u.toMul.property
  have he' : v = u.toMul := Subtype.ext he
  change u.toMul ∈ D
  exact he' ▸ hv

omit [IsElementaryAbelian 2 (ChapterC.blockU L)] in
theorem blockLinearMap_ker_le_conjugation
    (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) :
    a.linearMap.ker ≤ (MulAut.conjNormal : L →* MulAut (ChapterC.blockU L)).ker := by
  rw [a.linearMap_ker]
  intro l hl
  apply MulEquiv.ext
  intro u
  apply Subtype.ext
  change l * (u : L) * l⁻¹ = u
  rw [← hshort.core_centralizes_blockU hl u u.property, mul_inv_cancel_right]

noncomputable def blockCoverAut (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) :
    Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (ChapterC.blockU L) :=
  a.linearMap.liftOfSurjective (a.linearMap_surjective)
    ⟨MulAut.conjNormal, blockLinearMap_ker_le_conjugation hshort a⟩

omit [IsElementaryAbelian 2 (ChapterC.blockU L)] in
theorem blockCoverAut_apply (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) (l : L)
    (u : ChapterC.blockU L) :
    blockCoverAut hshort a (a.linearMap l) u = ChapterC.blockConjugate L l u := by
  unfold blockCoverAut
  rw [MonoidHom.liftOfRightInverse_comp_apply]
  rfl

noncomputable def blockCoverAction (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) :
    Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) (Additive (ChapterC.blockU L)) where
  toFun g := (blockCoverAut hshort a g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul ((blockCoverAut hshort a 1) u.toMul) = u
    rw [map_one]
    rfl
  map_mul' g h := by
    apply LinearMap.ext
    intro u
    change Additive.ofMul ((blockCoverAut hshort a (g * h)) u.toMul) = _
    rw [map_mul]
    rfl

theorem blockCoverAction_apply (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) (l : L)
    (u : Additive (ChapterC.blockU L)) :
    blockCoverAction hshort a (a.linearMap l) u = blockBinaryAction l u :=
  congrArg Additive.ofMul (blockCoverAut_apply hshort a l u.toMul)

theorem blockCoverAction_full [Group.IsPerfect L] (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) :
    Coinvariants.ker (blockCoverAction hshort a) = ⊤ := by
  apply top_unique
  rw [← blockBinaryAction_full (L := L)]
  apply Submodule.span_le.mpr
  rintro _ ⟨⟨l,u⟩,rfl⟩
  change blockBinaryAction l u - u ∈ Coinvariants.ker (blockCoverAction hshort a)
  rw [← blockCoverAction_apply hshort a]
  exact Coinvariants.sub_mem_ker _ _

variable [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

abbrev blockNaturalBinary : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) (Fin 2 → F) :=
  Representation.restrictScalars (Representation.specialLinearNatural 2)

noncomputable def blockCoverMap
    (a : MarkedBlockModel L B F) :
    Additive (ChapterC.blockU L) →ₗ[ZMod 2] (Fin 2 → F) :=
  (a.model.moduleIso.toMonoidHom.comp (QuotientGroup.mk' (ChapterC.blockFixed L))).toAdditiveLeft.toZModLinearMap 2

theorem blockCoverMap_surjective
    (a : MarkedBlockModel L B F) :
    Function.Surjective (blockCoverMap a) := by
  intro v
  obtain ⟨q,hq⟩ := a.model.moduleIso.surjective (Multiplicative.ofAdd v)
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (ChapterC.blockFixed L) q
  exact ⟨Additive.ofMul u, congrArg Multiplicative.toAdd hq⟩

theorem blockCoverMap_intertwining (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) (u : Additive (ChapterC.blockU L)) :
    blockCoverMap a (blockCoverAction hshort a g u) =
      blockNaturalBinary g (blockCoverMap a u) := by
  obtain ⟨l,rfl⟩ := a.linearMap_surjective g
  rw [blockCoverAction_apply, blockBinaryAction_apply]
  exact congrArg Multiplicative.toAdd (a.model.intertwining l u.toMul)

noncomputable def blockCoverProjection (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) :
    (blockCoverAction hshort a).IntertwiningMap (blockNaturalBinary (F := F)) :=
  (blockCoverMap a).intertwiningMap_of_isIntertwiningMap _ _
    (blockCoverMap_intertwining hshort a)

theorem blockCoverMap_ker (a : MarkedBlockModel L B F)
    (u : Additive (ChapterC.blockU L)) :
    u ∈ (blockCoverMap a).ker ↔ u.toMul ∈ ChapterC.blockFixed L := by
  change Multiplicative.toAdd (a.model.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u.toMul)) = 0 ↔ _
  change a.model.moduleIso (QuotientGroup.mk' (ChapterC.blockFixed L) u.toMul) = 1 ↔ _
  rw [map_eq_one_iff _ a.model.moduleIso.injective]
  exact QuotientGroup.eq_one_iff u.toMul

theorem blockCoverMap_ker_le_fixed (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) :
    (blockCoverMap a).ker ≤ Representation.OneCohomology.fixed (blockCoverAction hshort a) := by
  intro u hu g
  obtain ⟨l,rfl⟩ := a.linearMap_surjective g
  rw [blockCoverAction_apply, blockBinaryAction_apply]
  apply Additive.ofMul.injective
  apply Subtype.ext
  change l * (u.toMul : L) * l⁻¹ = (u.toMul : L)
  have hz : (u.toMul : L) ∈ center L := (blockCoverMap_ker a u).mp hu
  rw [mem_center_iff.mp hz l, mul_inv_cancel_right]

theorem blockCoverProjection_isCover [Group.IsPerfect L] (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) :
    Representation.OneCohomology.IsCover (blockCoverProjection hshort a) :=
  ⟨blockCoverMap_surjective a, blockCoverMap_ker_le_fixed hshort a, blockCoverAction_full hshort a⟩

end Construction

/-! The following interface is an **explicit earlier-source hypothesis**, not
an asserted theorem of this file. It is the rank-one specialization of the
orthogonal realization in I.2.3(1) and all of I.2.3(3), with G = L = SL₂(F).
The upper unipotent group is both the Sylow group and the transvection root
group, and its invariant F-line is the first coordinate line.

In characteristic two the radical in I.2.3 is the radical of the *polar
bilinear form*. The quadratic form itself is nondegenerate: it is nonzero
on that one-dimensional radical. These two radicals must not be confused.
-/

section EarlierSource
variable (F : Type*) [Field F] [Finite F] [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2
open Representation.OneCohomology
open Matrix.SpecialLinearGroup

/-- The actual cohomological universal binary covering space of the natural plane. -/
abbrev UniversalNaturalCover :=
  Module.Dual (ZMod 2) (cocycles (blockNaturalBinary (F := F)).dual)

/-- Orthogonal realization of the universal cover, as in the first assertion
of I.2.3(1). The binary equivalence intertwines the actual universal action
and commutes with the natural projection; this is not an unconnected model tag. -/
structure OrthogonalUniversalCover where
  action : Representation F (Matrix.SpecialLinearGroup (Fin 2) F) (Fin 3 → F)
  form : QuadraticForm F (Fin 3 → F)
  nondegenerate : form.Nondegenerate
  preserves : ∀ g v, form (action g v) = form v
  fixed_radical : fixed action = form.polarBilin.ker
  radical_dimension : Module.finrank F form.polarBilin.ker = 1
  projection : action.IntertwiningMap (Representation.specialLinearNatural 2)
  projection_surjective : Function.Surjective projection
  projection_kernel : projection.toLinearMap.ker = form.polarBilin.ker
  equivalence : UniversalNaturalCover F ≃ₗ[ZMod 2] (Fin 3 → F)
  intertwining : ∀ g v,
    equivalence ((universalAction (blockNaturalBinary (F := F)).dual).dual g v) =
      action g (equivalence v)
  over_natural : ∀ v,
    projection (equivalence v) = universalCoverProjection (blockNaturalBinary (F := F)) v

variable {F}
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  {σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V}

/-- The literal preimage of the invariant F-line; the cover itself need only
be an F₂-module. -/
def firstPreimage (p : σ.IntertwiningMap (blockNaturalBinary (F := F))) :
    Submodule (ZMod 2) V :=
  (LinearMap.proj 1 ∘ₗ p.toLinearMap).ker

variable (F) in
/-- Explicit earlier-source input, restricted to the rank-one case and to the
clauses used here. The orthogonal realization is retained, as is the full
fixed-space / commutator equality / root-centrality assertion of I.2.3(3).
The source theorem owner must supply this proposition; this file does not
prove I.2.3. No group L or block-centralizer conclusion occurs in its definition. -/
def RankOneCoverTheorem (n : ℕ) : Prop :=
  1 < n → Nat.card F = 2 ^ n →
    Nonempty (OrthogonalUniversalCover F) ∧
    ∀ (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (σ : Representation (ZMod 2) (Matrix.SpecialLinearGroup (Fin 2) F) V)
      (p : σ.IntertwiningMap (blockNaturalBinary (F := F))), IsCover p →
      fixed σ ≤ firstPreimage p ∧
      firstPreimage p = Coinvariants.ker (σ.comp (upperUnipotent F).subtype) ∧
      firstPreimage p ≤ fixed (σ.comp (upperUnipotent F).subtype)
end EarlierSource

section Application
variable [CharP F 2]
local instance : Algebra (ZMod 2) F := ZMod.algebra F 2

/-- The covering map is literally the previously marked quotient map. -/
theorem blockCoverMap_eq_naturalMap (hshort : ChapterC.IsShort L)
    (a : MarkedBlockModel L B F) (v : ChapterC.blockU L) :
    let := hshort.elementary
    blockCoverMap a (Additive.ofMul v) = (a.naturalMap v).toAdd := by
  let := hshort.elementary
  rfl

/-- Every hypothesis for the binary cover is discharged from shortness and
the marked SL₂ quotient. In particular no perfectness or C.1.13 premise remains. -/
theorem marked_cover [Finite F] (hshort : ChapterC.IsShort L) (a : MarkedBlockModel L B F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n) :
    let := hshort.elementary
    Representation.OneCohomology.IsCover (blockCoverProjection hshort a) := by
  let := hshort.elementary
  let := marked_isPerfect hshort a hn hF
  exact blockCoverProjection_isCover hshort a

/-- I.2.3(3) applied to the actual binary cover of a marked short group.
The Sylow group is the whole root preimage, so its kernel O₂(L) is retained;
that kernel acts trivially by shortness. No diagonal section is required. -/
theorem rootLine_le_centralizer_of_I23 [Finite L] [Finite F]
    (hshort : ChapterC.IsShort L) (a : MarkedBlockModel L B F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hI23 : RankOneCoverTheorem.{v, u} F n)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    a.rootLine ≤ Subgroup.centralizer (S : Set L) := by
  let := hshort.elementary
  have hcover := marked_cover hshort a hn hF
  have hroot := ((hI23 hn hF).2 (Additive ↥(ChapterC.blockU L))
    (blockCoverAction hshort a) (blockCoverProjection hshort a) hcover).2.2
  intro v hv
  obtain ⟨hvU, hzero⟩ := (a.mem_rootLine v).mp hv
  let u : Additive (ChapterC.blockU L) := Additive.ofMul ⟨v, hvU⟩
  have hu : u ∈ firstPreimage (blockCoverProjection hshort a) := hzero
  apply Subgroup.mem_centralizer_iff.mpr
  intro s hs
  have hsroot : a.linearMap s ∈ Matrix.SpecialLinearGroup.upperUnipotent F := by
    change s ∈ (Matrix.SpecialLinearGroup.upperUnipotent F).comap a.linearMap
    rw [← a.sylow_eq_root_comap S hS]
    exact hs
  have hfix := hroot hu ⟨a.linearMap s, hsroot⟩
  change blockCoverAction hshort a (a.linearMap s) u = u at hfix
  rw [blockCoverAction_apply, blockBinaryAction_apply] at hfix
  have hc := congrArg (fun w : Additive (ChapterC.blockU L) => (w.toMul : L)) hfix
  change s * v * s⁻¹ = v at hc
  exact (mul_inv_eq_iff_eq_mul).mp hc

/-- Combined with the natural coordinate calculation, the cover identifies
the complete centralizer of S in U(L). The only earlier-source input is I.2.3. -/
theorem blockU_centralizer_sylow_eq_rootLine_of_I23 [Finite L] [Finite F]
    (hshort : ChapterC.IsShort L) (a : MarkedBlockModel L B F)
    {n : ℕ} (hn : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hI23 : RankOneCoverTheorem.{v, u} F n)
    (S : Sylow 2 L) (hS : (S : Subgroup L) ≤ B) :
    ChapterC.blockU L ⊓ Subgroup.centralizer (S : Set L) = a.rootLine := by
  apply le_antisymm (a.blockU_centralizer_sylow_le_rootLine S hS)
  apply le_inf _ (rootLine_le_centralizer_of_I23 hshort a hn hF hI23 S hS)
  intro v hv
  exact ((a.mem_rootLine v).mp hv).choose

end Application

end CFSG.Quasithin.ChapterE.Section06.L2Torus.CoverLift

end
