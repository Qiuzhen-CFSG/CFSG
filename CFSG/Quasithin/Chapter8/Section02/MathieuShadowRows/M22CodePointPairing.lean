module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointFixed
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativePairing
public import CFSG.Quasithin.Chapter8.Section02.Centralizer.SourcePointPairing

/-!
# The full original M22 point pairing

Whole-code coordinates identify the original commutator with the native
five-space. Its central quotient gives qW; the full native transvection
characters give qX. The kernels are exactly the original central cyclic
subgroup and the full centralizer of V in the original two-core. Their
evaluation is the literal ambient commutator, with the original z retained.

The arbitrary-hexad application discharges SourcePointPairing and both
fixed-space inputs for the source full-core argument. Identifying the full
actor kernel with V remains a separate original-source conclusion.

Source: Aschbacher--Smith H.16.4 and 8.2.11--12, printed pp.403,722.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.ChiefFlag MathieuCode.Hexad.ChiefFlag.Actions
open M22ChapterH.Hexad.Action BinaryTransvectionGroups
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22PointCoordinates
open ChapterE ChapterH.Section13To16.M22Local.Hexad
variable {G : Type*} [Group G] [Finite G]
private theorem native_character_fixed_iff (k : Kernel) :
    NativePairing.characterMap k = 1 ↔ ∀ v : M22Code, m22OuterCodeRepresentation k.val v = v := by
  constructor
  · intro hk
    have hk1 : k = 1 := NativePairing.characterMap_injective
      (hk.trans NativePairing.characterMap.map_one.symm)
    subst k
    intro v
    exact congrArg (fun a => a v) m22OuterCodeRepresentation.map_one
  · intro hk
    have hfaith : Function.Injective codeKernelAction := NativeSource.code_clauses.1.faithful
    have he : codeKernelAction k = 1 := by
      apply LinearEquiv.ext
      intro v
      apply Subtype.ext
      exact hk v.val
    have hk1 : k = 1 := hfaith (he.trans codeKernelAction.map_one.symm)
    exact (congrArg NativePairing.characterMap hk1).trans NativePairing.characterMap.map_one
variable (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : G)
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* M22ChapterH.Hexad.Action.Inner)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v))

/-- Coordinates on the literal original commutator before quotienting its center. -/
def fiveMap : Centralizer.commutatorSpace L V z →* Multiplicative V5.toSubmodule where
  toFun w := Multiplicative.ofAdd
    ⟨e (Additive.ofMul (⟨w,Centralizer.commutatorSpace_le L V z hLN w.property⟩ : V)),
      (m22_point_residual_commutator_coordinates L V z hLN e f hf hk he _).mp w.property⟩
  map_one' := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    exact e.map_zero
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    simp only [toAdd_mul,toAdd_ofAdd,Submodule.coe_add]
    let va : V := ⟨a,Centralizer.commutatorSpace_le L V z hLN a.property⟩
    let vb : V := ⟨b,Centralizer.commutatorSpace_le L V z hLN b.property⟩
    change e (Additive.ofMul (va*vb)) = e (Additive.ofMul va) + e (Additive.ofMul vb)
    rw [ofMul_mul,map_add]

theorem fiveMap_surjective : Function.Surjective (fiveMap L V z hLN e f hf hk he) := by
  intro w
  let v := e.symm w.toAdd.val
  have hv : (v.toMul : G) ∈ Centralizer.commutatorSpace L V z :=
    (m22_point_residual_commutator_coordinates L V z hLN e f hf hk he v).mpr
      (by change e (e.symm w.toAdd.val) ∈ _; rw [e.apply_symm_apply]; exact w.toAdd.property)
  refine ⟨⟨v.toMul,hv⟩,?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact e.apply_symm_apply _

/-- The original five-space quotient map, with the central denominator retained. -/
def sectionMap : Centralizer.commutatorSpace L V z →* Multiplicative NativePairing.Section :=
  ((centerLine NativePairing.point).mkQ.toAddMonoidHom.toMultiplicative).comp
    (fiveMap L V z hLN e f hf hk he)

theorem sectionMap_surjective : Function.Surjective (sectionMap L V z hLN e f hf hk he) := by
  intro w
  obtain ⟨v,hv⟩ := (centerLine NativePairing.point).mkQ_surjective w.toAdd
  obtain ⟨a,ha⟩ := fiveMap_surjective L V z hLN e f hf hk he (Multiplicative.ofAdd v)
  refine ⟨a,?_⟩
  change Multiplicative.ofAdd ((centerLine NativePairing.point).mkQ
    (fiveMap L V z hLN e f hf hk he a).toAdd) = w
  exact (congrArg (fun t : Multiplicative V5.toSubmodule =>
    Multiplicative.ofAdd ((centerLine NativePairing.point).mkQ t.toAdd)) ha).trans
      (congrArg Multiplicative.ofAdd hv)

/-- Characters of the actual original two-core action. -/
def characterMap : Centralizer.localTwoCore L z →*
    Multiplicative (Module.Dual (ZMod 2) NativePairing.Section) :=
  NativePairing.characterMap.comp (coreMap L z f hf hk)

theorem characterMap_surjective : Function.Surjective (characterMap L z f hf hk) :=
  NativePairing.characterMap_surjective.comp (coreMap_surjective L z f hf hk)

include hLN e he in
/-- The entire original action kernel is retained, including any central covering kernel. -/
theorem characterMap_ker :
    (characterMap L z f hf hk).ker =
      (centralizer (V : Set G)).subgroupOf (Centralizer.localTwoCore L z) := by
  ext x
  change NativePairing.characterMap (coreMap L z f hf hk x) = 1 ↔
    (x : G) ∈ centralizer (V : Set G)
  rw [native_character_fixed_iff]
  constructor
  · intro hx v hv
    have hact := coreMap_equivariant L z f hf hk V hLN e he x ⟨v,hv⟩
    have hh := congrArg (fun a : Additive V => (a.toMul : G))
      (e.injective (hact.trans (hx _)))
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · intro hx w
    obtain ⟨v,rfl⟩ := e.surjective w
    have hcomm : (x : G)*(v.toMul : G)*(x : G)⁻¹ = v.toMul :=
      mul_inv_eq_iff_eq_mul.mpr (hx v.toMul v.toMul.property).symm
    exact (coreMap_equivariant L z f hf hk V hLN e he x v.toMul).symm.trans
      (congrArg (fun a : V => e (Additive.ofMul a)) (Subtype.ext hcomm))

variable (hzV : z ∈ V)
    (hz : e (Additive.ofMul (⟨z,hzV⟩ : V)) = m22HexadVector m22Hexad24Ten_mem)

include hz

/-- The first pairing map kills precisely the original central cyclic subgroup. -/
theorem sectionMap_ker : (sectionMap L V z hLN e f hf hk he).ker =
    (zpowers z).subgroupOf (Centralizer.commutatorSpace L V z) := by
  ext w
  change (centerLine NativePairing.point).mkQ (fiveMap L V z hLN e f hf hk he w).toAdd = 0 ↔ _
  change (Submodule.Quotient.mk (fiveMap L V z hLN e f hf hk he w).toAdd : NativePairing.Section) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero,← NativePairing.center_eq_span]
  change e (Additive.ofMul (⟨w,Centralizer.commutatorSpace_le L V z hLN w.property⟩ : V))
      ∈ V1.toSubmodule ↔ (w : G) ∈ zpowers z
  exact (m22_point_line_coordinates V ⟨z,hzV⟩ e hz _).symm

include hLN he in
private theorem pairing_of_displacement (x : Centralizer.localTwoCore L z) (v : V)
    (c : ZMod 2)
    (hdisp : c • m22HexadVector m22Hexad24Ten_mem =
      m22OuterCodeRepresentation (coreMap L z f hf hk x).val (e (Additive.ofMul v)) -
        e (Additive.ofMul v)) : ⁅(x : G),(v : G)⁆ = z ^ c.val := by
  obtain ⟨hc,hcoord⟩ := coreMap_commutator L z f hf hk V hLN e he x v
  have hp : e (Additive.ofMul (⟨z ^ c.val,pow_mem hzV c.val⟩ : V)) =
      c • m22HexadVector m22Hexad24Ten_mem := by
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) c with rfl | rfl
    · have hp0 : (⟨z ^ (0 : ZMod 2).val,pow_mem hzV (0 : ZMod 2).val⟩ : V) = 1 :=
        Subtype.ext (pow_zero z)
      rw [hp0,ofMul_one,map_zero,zero_smul]
    · simpa only [show (1 : ZMod 2).val = 1 from rfl,pow_one,one_smul] using hz
  exact congrArg (fun a : Additive V => (a.toMul : G))
    (e.injective (hcoord.trans (hdisp.symm.trans hp.symm)))

/-- The native transvections give the full original commutator pairing along z. -/
theorem pairing (x : Centralizer.localTwoCore L z) (w : Centralizer.commutatorSpace L V z) :
    ⁅(x : G),(w : G)⁆ = z ^
      ((characterMap L z f hf hk x).toAdd (sectionMap L V z hLN e f hf hk he w).toAdd).val := by
  let v : V := ⟨w,Centralizer.commutatorSpace_le L V z hLN w.property⟩
  apply pairing_of_displacement L V z hLN e f hf hk he hzV hz x v
  exact congrArg Subtype.val
    (NativePairing.characterMap_displacement (coreMap L z f hf hk x)
      (fiveMap L V z hLN e f hf hk he w).toAdd)

include hLN e hf hk he in
/-- The literal native marking discharges the complete original point-pairing input. -/
theorem source_pairing : Centralizer.SourcePointPairing L V z NativePairing.Section :=
  ⟨sectionMap L V z hLN e f hf hk he,
    sectionMap_surjective L V z hLN e f hf hk he,
    sectionMap_ker L V z hLN e f hf hk he hzV hz,
    characterMap L z f hf hk,
    characterMap_surjective L z f hf hk,
    characterMap_ker L V z hLN e f hf hk he,
    pairing L V z hLN e f hf hk he hzV hz⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22PointCoordinates

open scoped Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE ChapterH.Section13To16.M22Local.Hexad
variable {G : Type*} [Group G] [Finite G]

/-- An arbitrary original hexad supplies the full point pairing and both
fixed-space conclusions, with the original central element and full kernel. -/
theorem m22_point_hexad_pairing
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hLN : L ≤ normalizer (V : Set G))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* MulAction.stabilizer M22 B)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hz : e (Additive.ofMul z) = m22HexadVector hB)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v)) :
    Centralizer.SourcePointPairing L V z NativePairing.Section ∧
      V ⊓ centralizer (Centralizer.localTwoCore L z : Set G) = zpowers (z : G) ∧
      ∀ v : V,
        (∀ x : Centralizer.localTwoCore L z, ⁅(x : G),(v : G)⁆ ∈ zpowers (z : G)) ↔
          (v : G) ∈ Centralizer.commutatorSpace L V z := by
  let E := e.trans (WholeCodeCoordinates.codeEquiv hB)
  let F := WholeCodeCoordinates.actorMap hB f
  have hF : Function.Surjective F := WholeCodeCoordinates.actorMap_surjective hB f hf
  have hK : IsPGroup 2 F.ker := by
    change IsPGroup 2 (WholeCodeCoordinates.actorMap hB f).ker
    rw [WholeCodeCoordinates.actorMap_ker]
    exact hk
  have hZ : E (Additive.ofMul z) = m22HexadVector m22Hexad24Ten_mem :=
    (congrArg (WholeCodeCoordinates.codeEquiv hB) hz).trans
      (WholeCodeCoordinates.codeEquiv_point hB)
  have hE : ∀ r v, E (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (F r).val (E v) := fun r v =>
    (congrArg (WholeCodeCoordinates.codeEquiv hB) (he r v)).trans
      (WholeCodeCoordinates.codeEquiv_equivariant hB (f r) (e v))
  exact ⟨M22PointCoordinates.source_pairing L V z hLN E F hF hK hE z.property hZ,
    M22PointCoordinates.fixed_eq_line L z F hF hK V hLN E hE z.property hZ,
    M22PointCoordinates.fixed_modulo_line L z F hF hK V hLN E hE z.property hZ⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
