module

public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic.Splitting
public import CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Binary.Coordinates
public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.CoreExtension
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# The actual quartic radical as a marked central extension of the core

Reduce the constructed quartic complement modulo the central squares. Binary
recognition on that same complement identifies the Frattini quotient with the
six-letter augmentation core, preserving conjugation and the original natural
quotient map. Every generator of the ambient cyclic-four center maps to the
constant vector, and its square generates the exact Frattini kernel.

If the radical were abelian, squaring would give a nontrivial abelian image of
the perfect hexad extension. The invariant-subspace dichotomy for A₆ then
identifies the full radical center with the embedded ambient center. These
arguments supply the elementary marked extension inputs without assuming a
quaternion-product recognition or a comparison with the intrinsic signed action.
Those two comparisons remain separate steps.

Source: Aschbacher–Smith I.2.2(6), printed pp.410 and 412 / PDF pp.421 and 423.
Only the earlier A₆ covering identification and perfectness restriction remain
source inputs to the construction.
-/

@[expose] public section

namespace CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
open Subgroup Sporadic.Mathieu Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
universe u
variable {K : Type u} [Group K]

/-- The actual complement and marked augmentation projection, before recognition of R. -/
structure FrattiniCoordinates (e : (K ⧸ center K) ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks) where
  sectionHom : alternatingGroup (Fin 6) →* hexadPreimage e B
  section_marking : ∀ a, hexadSixMap e hB (sectionHom a) = m22HexadMarking hB a
  section_projection :
    (localProjection e (MulAction.stabilizer M22 B)).comp sectionHom = m22HexadSection hB
  commutator_eq :
    ⁅(hexadRadical e B).subgroupOf (hexadPreimage e B), sectionHom.range⁆ =
      (hexadRadical e B).subgroupOf (hexadPreimage e B)
  coreMap : hexadRadical e B →* Multiplicative (BinaryPermutation.core (Fin 6))
  surjective : Function.Surjective coreMap
  kernel : coreMap.ker = frattini (hexadRadical e B)
  equivariant : ∀ a r, (coreMap (hexadConjugation e B (sectionHom a) r)).toAdd =
    BinaryPermutation.coreRepresentation (Fin 6) a.val (coreMap r).toAdd
  natural_projection : ∀ r,
    BinaryPermutation.coreToNatural (Fin 6) (coreMap r).toAdd =
      (Binary.naturalMap e hB r).toAdd

/-- Conjugation commutes with the literal ambient quotient by central squares. -/
theorem reduction_conjugation (e : (K ⧸ center K) ≃* M22)
    (B : Finset (Fin 22)) (g : hexadPreimage e B) (r : hexadRadical e B) :
    quarticReductionLocal e (m22HexadPointwiseKernel B) (hexadConjugation e B g r) =
      hexadConjugation (quarticReductionEquiv e) B
        (quarticReductionLocal e (MulAction.stabilizer M22 B) g)
        (quarticReductionLocal e (m22HexadPointwiseKernel B) r) := by
  apply Subtype.ext
  change (QuotientGroup.mk' (centralSquares K)) (g.val * r.val * g.val⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

/-- Construct the augmentation coordinates using the reduction of the same complement. -/
theorem exists_frattiniCoordinates [Finite K] [IsCyclic (center K)]
    (e : (K ⧸ center K) ≃* M22) (hZ : Nat.card (center K) = 4)
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    [Group.IsPerfect (hexadPreimage e B)]
    (hcover : CentralExtension.TwoPrimaryInvolutionData.{u} (alternatingGroup (Fin 6))) :
    Nonempty (FrattiniCoordinates e hB) := by
  obtain ⟨s, hs, hn, _, hcomm⟩ := Splitting.exists_naturally_marked_section e hZ hB hcover
  let e₂ := quarticReductionEquiv e
  let qI : hexadPreimage e B →* hexadPreimage e₂ B :=
    quarticReductionLocal e (MulAction.stabilizer M22 B)
  let qR : hexadRadical e B →* hexadRadical e₂ B :=
    quarticReductionLocal e (m22HexadPointwiseKernel B)
  let s₂ := qI.comp s
  let : Group.IsPerfect (hexadPreimage e₂ B) :=
    Group.IsPerfect.ofSurjective (f := qI) (quarticReductionLocal_surjective e _)
  have hn₂ : (localProjection e₂ (MulAction.stabilizer M22 B)).comp s₂ =
      m22HexadSection hB := hn
  have hs₂ (a : alternatingGroup (Fin 6)) :
      hexadSixMap e₂ hB (s₂ a) = m22HexadMarking hB a := by
    apply Subtype.ext
    change m22HexadAction hB (localProjection e₂ (MulAction.stabilizer M22 B) (s₂ a)) = _
    have hna : localProjection e₂ (MulAction.stabilizer M22 B) (s₂ a) =
        m22HexadSection hB a := DFunLike.congr_fun hn₂ a
    rw [hna]
    exact congrArg Subtype.val (m22HexadSixMap_section hB a)
  obtain ⟨E, hE, hEq, _⟩ := hexadRadical_core_of_section e₂
    (quarticReduction_center_card e hZ) hB (m22HexadMarking hB) s₂ hs₂
    (Binary.naturalMap e₂ hB) (Binary.naturalMap_surjective e₂ hB)
    (Binary.naturalMap_ker e₂ hB) (Binary.naturalMap_conjugation e₂ hB s₂ hn₂)
  let f := E.toMonoidHom.comp qR
  refine ⟨⟨s, (fun a => DFunLike.congr_fun hs a), hn, hcomm, f,
    E.surjective.comp (quarticReductionLocal_surjective e _), ?_, ?_, ?_⟩⟩
  · exact (MonoidHom.ker_mulEquiv_comp qR E).trans
      ((quarticReductionLocal_ker e _).trans (radical_frattini e hZ hB).symm)
  · intro a r
    change (E (qR (hexadConjugation e B (s a) r))).toAdd = _
    have hr : qR (hexadConjugation e B (s a) r) =
        hexadConjugation e₂ B (s₂ a) (qR r) := reduction_conjugation e B (s a) r
    rw [hr]
    exact hE a (qR r)
  · intro r
    exact hEq (qR r)

namespace FrattiniCoordinates
variable {e : (K ⧸ center K) ≃* M22} {B : Finset (Fin 22)} {hB : B ∈ m22Blocks}
variable (d : FrattiniCoordinates e hB)

/-- The actual Frattini quotient in its marked six-letter coordinates. -/
noncomputable def quotientEquiv :
    (hexadRadical e B ⧸ frattini (hexadRadical e B)) ≃*
      Multiplicative (BinaryPermutation.core (Fin 6)) :=
  (QuotientGroup.quotientMulEquivOfEq d.kernel.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective d.coreMap d.surjective)

/-- The quotient equivalence retains the original core map. -/
@[simp] theorem quotientEquiv_mk (r : hexadRadical e B) :
    d.quotientEquiv (QuotientGroup.mk' (frattini (hexadRadical e B)) r) = d.coreMap r := rfl

/-- Equivariance for the canonical action on the actual Frattini quotient. -/
theorem quotientEquiv_conjugation (a : alternatingGroup (Fin 6))
    (v : hexadRadical e B ⧸ frattini (hexadRadical e B)) :
    (d.quotientEquiv (Subgroup.quotientAut (frattini (hexadRadical e B))
      (hexadConjugation e B (d.sectionHom a)) v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) a.val (d.quotientEquiv v).toAdd := by
  obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective (frattini (hexadRadical e B)) v
  rw [Subgroup.quotientAut_apply_mk, d.quotientEquiv_mk, d.quotientEquiv_mk]
  exact d.equivariant a r

/-- The ambient center is exactly the inverse image of the constant line. -/
theorem center_iff_constants (r : hexadRadical e B) :
    r.val ∈ center K ↔ (d.coreMap r).toAdd.val ∈ BinaryPermutation.constants (Fin 6) := by
  have he : r.val ∈ center K ↔
      BinaryPermutation.coreToNatural (Fin 6) (d.coreMap r).toAdd = 0 := by
    rw [d.natural_projection]
    change r ∈ (center K).subgroupOf (hexadRadical e B) ↔ Binary.naturalMap e hB r = 1
    rw [← Binary.naturalMap_ker]
    rfl
  rw [he, ← Subtype.val_inj]
  exact Submodule.Quotient.mk_eq_zero _

/-- The constructed section range complements the actual radical inside I. -/
theorem isComplement :
    ((hexadRadical e B).subgroupOf (hexadPreimage e B)).IsComplement' d.sectionHom.range :=
  hexadSection_isComplement e hB (m22HexadMarking hB) d.sectionHom d.section_marking

/-- The complement is genuinely A₆, with the specified parametrization. -/
noncomputable def complementEquiv : alternatingGroup (Fin 6) ≃* d.sectionHom.range :=
  MonoidHom.ofInjective
    (hexadSection_injective e hB (m22HexadMarking hB) d.sectionHom d.section_marking)

/-- Commutator generation after both factors are embedded in the original K. -/
theorem eq_commutator : hexadRadical e B =
    ⁅hexadRadical e B, d.sectionHom.range.map (hexadPreimage e B).subtype⁆ := by
  have h := congrArg (Subgroup.map (hexadPreimage e B).subtype) d.commutator_eq
  rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (hexadRadical_le e B)] at h
  exact h.symm

variable [Finite K] [IsCyclic (center K)] (hZ : Nat.card (center K) = 4)
include hZ d

/-- An order-four central generator survives the Frattini projection. -/
theorem coreMap_ne_one_of_center_generator (c : center K) (hc : orderOf c = 4) :
    d.coreMap ⟨c, center_le_hexadRadical e B c.property⟩ ≠ 1 := by
  intro h
  have hm : (⟨c, center_le_hexadRadical e B c.property⟩ : hexadRadical e B) ∈
      frattini (hexadRadical e B) := d.kernel ▸ h
  rw [radical_frattini e hZ hB] at hm
  have h2 : c ^ 2 = 1 := Subtype.ext (centralSquares_square hZ hm)
  have hd := orderOf_dvd_of_pow_eq_one h2
  rw [hc] at hd
  norm_num at hd

/-- Every ambient central generator has the specified constant-vector image. -/
theorem coreMap_center_generator (c : center K) (hc : orderOf c = 4) :
    d.coreMap ⟨c, center_le_hexadRadical e B c.property⟩ =
      Multiplicative.ofAdd EvenCliffordSix.volumeVector := by
  let r : hexadRadical e B := ⟨c, center_le_hexadRadical e B c.property⟩
  have hconst := (d.center_iff_constants r).mp c.property
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hconst
  have ha1 : a = 1 := by
    have hcases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases hcases a with h0 | h1
    · rw [h0, zero_smul] at ha
      have hzero : d.coreMap r = 1 := by
        apply Multiplicative.toAdd.injective
        exact Subtype.ext ha.symm
      exact (d.coreMap_ne_one_of_center_generator hZ c hc hzero).elim
    · exact h1
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  rw [ha1, one_smul] at ha
  exact ha.symm.trans (by decide)

/-- Supply every elementary extension input, retaining the ambient generator and its square. -/
theorem exists_coreExtension :
    ∃ c : center K, orderOf c = 4 ∧
      ∃ D : EvenCliffordSix.CoreExtension (hexadRadical e B),
        D.projection = d.coreMap ∧
        D.actor = (hexadConjugation e B).comp d.sectionHom ∧
        D.volume.val = c.val ∧ D.sign.val = c.val ^ 2 := by
  obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := center K)
  rw [hZ] at hc
  let v : hexadRadical e B := ⟨c, center_le_hexadRadical e B c.property⟩
  let z := v ^ 2
  have hv : orderOf v = 4 := by
    rw [← orderOf_injective (hexadRadical e B).subtype Subtype.val_injective v]
    exact (orderOf_injective (center K).subtype Subtype.val_injective c).trans hc
  have hz : orderOf z = 2 := by
    change orderOf (v ^ 2) = 2
    rw [orderOf_pow, hv]
    decide
  have hzk : z ∈ d.coreMap.ker := by
    rw [d.kernel, radical_frattini e hZ hB]
    exact mem_centralSquares.mpr ⟨c, rfl⟩
  have hk : d.coreMap.ker = zpowers z := by
    apply (Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hzk) ?_).symm
    rw [d.kernel, radical_frattini_card e hZ hB, Nat.card_zpowers, hz]
  have hcentral : z ∈ center (hexadRadical e B) := by
    apply mem_center_iff.mpr
    intro r
    apply Subtype.ext
    exact mem_center_iff.mp ((center K).pow_mem c.property 2) r.val
  refine ⟨c, hc, ⟨d.coreMap, d.surjective, z, hz, hk, hcentral,
    (hexadConjugation e B).comp d.sectionHom, d.equivariant,
    v, ?_, d.coreMap_center_generator hZ c hc, rfl⟩, rfl, rfl, rfl, rfl⟩
  apply mem_center_iff.mpr
  intro r
  exact Subtype.ext (mem_center_iff.mp c.property r.val)

open scoped IsMulCommutative in
/-- Perfectness rules out an abelian radical by applying the square homomorphism. -/
theorem not_isMulCommutative [Group.IsPerfect (hexadPreimage e B)] :
    ¬ IsMulCommutative (hexadRadical e B) := by
  intro hab
  let : IsMulCommutative (hexadRadical e B) := hab
  let φ := (hexadConjugation e B).comp d.sectionHom
  let E := MulEquiv.ofBijective (hexadSplitHom e B d.sectionHom)
    (hexadSplitHom_bijective e hB (m22HexadMarking hB) d.sectionHom d.section_marking)
  let : Group.IsPerfect (hexadRadical e B ⋊[φ] alternatingGroup (Fin 6)) :=
    Group.IsPerfect.ofSurjective (f := E.symm.toMonoidHom) E.symm.surjective
  have hfix (a : alternatingGroup (Fin 6)) (r : hexadRadical e B) :
      (φ a r) ^ 2 = r ^ 2 := by
    rw [← map_pow]
    apply Subtype.ext
    change (d.sectionHom a).val * r.val ^ 2 * (d.sectionHom a).val⁻¹ = r.val ^ 2
    rw [mem_center_iff.mp (centralSquares_le_center (radical_square_mem e hZ hB r)),
      mul_inv_cancel_right]
  let f : hexadRadical e B ⋊[φ] alternatingGroup (Fin 6) →* hexadRadical e B :=
    { toFun x := x.left ^ 2
      map_one' := one_pow 2
      map_mul' x y := by
        change (x.left * φ x.right y.left) ^ 2 = x.left ^ 2 * y.left ^ 2
        rw [mul_pow, hfix] }
  obtain ⟨_, _, D, _⟩ := d.exists_coreExtension hZ
  have h2 : D.volume ^ 2 = 1 := Abelianization.commutator_subset_ker f
    (Group.IsPerfect.mem_commutator (g := SemidirectProduct.inl D.volume))
  have hs : D.sign = 1 := D.volume_square.symm.trans h2
  have ho := D.sign_order
  rw [hs, orderOf_one] at ho
  norm_num at ho

/-- Nonabelianity and the natural-module action identify the full center of R. -/
theorem center_eq_ambient [Group.IsPerfect (hexadPreimage e B)] :
    Subgroup.center (hexadRadical e B) = (Subgroup.center K).subgroupOf (hexadRadical e B) := by
  let H := (Subgroup.center (hexadRadical e B)).map d.coreMap
  let U : Submodule (ZMod 2) (BinaryPermutation.core (Fin 6)) :=
    { carrier := {v | Multiplicative.ofAdd v ∈ H}
      zero_mem' := H.one_mem
      add_mem' := fun hx hy => H.mul_mem hx hy
      smul_mem' := by
        intro c v hv
        have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
        rcases hc c with rfl | rfl
        · rw [zero_smul]
          exact H.one_mem
        · rw [one_smul]
          exact hv }
  let W := U.map (BinaryPermutation.core (Fin 6)).subtype
  have hW : ∀ a : alternatingGroup (Fin 6), ∀ v ∈ W,
      BinaryPermutation.representation (Fin 6) a.val v ∈ W := by
    intro a v hv
    obtain ⟨u, hu, rfl⟩ := hv
    obtain ⟨r, hr, he⟩ := (show Multiplicative.ofAdd u ∈ H from hu)
    refine ⟨BinaryPermutation.coreRepresentation (Fin 6) a.val u, ?_, rfl⟩
    change Multiplicative.ofAdd (BinaryPermutation.coreRepresentation (Fin 6) a.val u) ∈ H
    refine ⟨hexadConjugation e B (d.sectionHom a) r,
      (centerCongr (hexadConjugation e B (d.sectionHom a)) ⟨r, hr⟩).property, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [d.equivariant, he]
    rfl
  have hZle : (Subgroup.center K).subgroupOf (hexadRadical e B) ≤
      Subgroup.center (hexadRadical e B) := by
    intro r hr
    apply mem_center_iff.mpr
    intro x
    exact Subtype.ext (mem_center_iff.mp hr x.val)
  rcases BinaryPermutation.invariant_le_constants_or_core_le
      (by decide : 5 ≤ Fintype.card (Fin 6)) W hW with h | h
  · apply le_antisymm ?_ hZle
    intro r hr
    apply (d.center_iff_constants r).mpr
    exact h ⟨(d.coreMap r).toAdd, (show Multiplicative.ofAdd (d.coreMap r).toAdd ∈ H from
      ⟨r, hr, rfl⟩), rfl⟩
  · have hk : d.coreMap.ker ≤ Subgroup.center (hexadRadical e B) := by
      intro r hr
      rw [d.kernel, radical_frattini e hZ hB] at hr
      exact hZle (centralSquares_le_center hr)
    have ht : Subgroup.center (hexadRadical e B) = ⊤ := by
      apply top_unique
      intro r _
      obtain ⟨v, hv, he⟩ := h (d.coreMap r).toAdd.property
      obtain ⟨z, hz, hf⟩ := (show Multiplicative.ofAdd v ∈ H from hv)
      have heq : d.coreMap z = d.coreMap r :=
        hf.trans (congrArg Multiplicative.ofAdd (Subtype.ext he))
      have hrz : r * z⁻¹ ∈ d.coreMap.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, heq, mul_inv_cancel]
      have hm := (Subgroup.center (hexadRadical e B)).mul_mem (hk hrz) hz
      simpa only [inv_mul_cancel_right] using hm
    exact (d.not_isMulCommutative hZ (Subgroup.center_eq_top_iff.mp ht)).elim

/-- The intrinsic center embeds as precisely Z(K), not an unspecified cyclic subgroup. -/
theorem center_map [Group.IsPerfect (hexadPreimage e B)] :
    (Subgroup.center (hexadRadical e B)).map (hexadRadical e B).subtype = Subgroup.center K := by
  rw [d.center_eq_ambient hZ, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr (center_le_hexadRadical e B)]

end FrattiniCoordinates
end CFSG.Quasithin.ChapterI.Section02.ExceptionalCovers.M22Local.Quartic
