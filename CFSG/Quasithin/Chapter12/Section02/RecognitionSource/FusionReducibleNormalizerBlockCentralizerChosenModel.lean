module
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleG2Model
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizerBlockCentralizerFixedLine

/-!
# The chosen central quotient of an intrinsic block

Short-group irreducibility identifies the chosen subgroup with U(L).
The original BlockModuleModel therefore induces a linear equivalence on
its literal central quotient. The proof checks the kernel and conjugation
formulas before descending the map, retaining the original actor quotient.

This transports the intrinsic G₂ and L₃ alternatives into the fixed-space
bounds used by the reducible normalizer consumer.
Source: Aschbacher–Smith C.1.7 and 12.2.16, pp.123,800.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
open ChapterB.QuasisimpleSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable {A W : Type*} [Group A] [AddCommGroup W] [Module (ZMod 2) W]
variable {ρ : A →* MulAut (Multiplicative W)} {σ : Representation (ZMod 2) A W}

/-- Transport the intrinsic block model to the literal central quotient of the chosen module. -/
def chosenCentralEquiv_of_blockModel (D : ChosenModule T L V)
    (hb : ChapterC.IsShort L)
    (m : ChapterC.BlockModuleModel L ρ)
    (hρ : ∀ g v, (ρ g v).toAdd = σ g v.toAdd) : ActionEquiv D.centralQuotientAction σ := by
  have he := chosen_eq_blockU D hb
  let eU : ChapterC.blockU L ≃* V :=
    (equivMapOfInjective (ChapterC.blockU L) L.subtype L.subtype_injective).trans
      (MulEquiv.subgroupCongr he.symm)
  let e : Multiplicative D.space ≃* ChapterC.blockU L := D.spaceEquiv.trans eU.symm
  let f : Multiplicative D.space →* Multiplicative W :=
    m.moduleIso.toMonoidHom.comp ((QuotientGroup.mk' (ChapterC.blockFixed L)).comp e.toMonoidHom)
  let fa : D.space →+ W := MonoidHom.toAdditive f
  let fl : D.space →ₗ[ZMod 2] W := { fa with map_smul' := ZMod.map_smul fa }
  let C := G2WeylModel.Fixed D
  have heval (v : D.space) : ((e (Multiplicative.ofAdd v) : L) : G) =
      (v.val.toMul.val : G) := by
    have hh := congrArg Subtype.val (eU.apply_symm_apply (D.spaceEquiv (Multiplicative.ofAdd v)))
    exact hh.trans (D.spaceEquiv_apply v)
  have hconj (l : L) (v : D.space) :
      e (Multiplicative.ofAdd (D.chosenAction l v)) =
        ChapterC.blockConjugate L l (e (Multiplicative.ofAdd v)) := by
    apply Subtype.ext
    apply Subtype.ext
    rw [heval]
    change (l : G) * (v.val.toMul.val : G) * (l : G)⁻¹ = _
    rw [←heval v]
    rfl
  have hf (l : L) (v : D.space) :
      fl (D.chosenAction l v) = σ (m.quotientIso (QuotientGroup.mk' (pCore 2 L) l)) (fl v) := by
    change (m.moduleIso (QuotientGroup.mk' _ (e (Multiplicative.ofAdd (D.chosenAction l v))))).toAdd = _
    rw [hconj,m.intertwining,hρ]
    rfl
  have hker : fl.ker = C := by
    ext v
    change (m.moduleIso (QuotientGroup.mk' _ (e (Multiplicative.ofAdd v)))).toAdd = 0 ↔ _
    rw [show ((m.moduleIso (QuotientGroup.mk' _ (e (Multiplicative.ofAdd v)))).toAdd = 0) ↔
      QuotientGroup.mk' (ChapterC.blockFixed L) (e (Multiplicative.ofAdd v)) = 1 from
        m.moduleIso.map_eq_one_iff]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro hv l
      have hh := mem_center_iff.mp hv (subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) l)
      apply Additive.toMul.injective
      apply Subtype.ext
      apply Subtype.ext
      change (l.val.val : G) * (v.val.toMul.val : G) * (l.val.val : G)⁻¹ = (v.val.toMul.val : G)
      simp only [←heval v]
      exact mul_inv_eq_iff_eq_mul.mpr (congrArg Subtype.val hh)
    · intro hv
      apply mem_center_iff.mpr
      intro l
      have hh := hv ((subgroupOfEquivOfLe (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)).symm l)
      have hc := congrArg (fun w : Additive (ReducedModule (L ⊔ (T : Subgroup G))) =>
        (w.toMul.val : G)) hh
      apply Subtype.ext
      change (l : G) * ((e (Multiplicative.ofAdd v) : L) : G) =
        ((e (Multiplicative.ofAdd v) : L) : G) * l
      rw [heval]
      exact mul_inv_eq_iff_eq_mul.mp hc
  have hsurj : Function.Surjective fl := by
    intro w
    obtain ⟨x,hx⟩ := m.moduleIso.surjective (Multiplicative.ofAdd w)
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (ChapterC.blockFixed L) x
    refine ⟨(e.symm u).toAdd, ?_⟩
    change (m.moduleIso (QuotientGroup.mk' _ (e (e.symm u)))).toAdd = w
    rw [e.apply_symm_apply,hx]
    rfl
  let fq : D.chosenCentralQuotient →ₗ[ZMod 2] W := C.liftQ fl hker.ge
  have hbij : Function.Bijective fq := ⟨by
      apply LinearMap.ker_eq_bot.mp
      rw [Submodule.ker_liftQ,hker]
      exact Submodule.mkQ_map_self C,
    (by intro w; obtain ⟨v,rfl⟩ := hsurj w; exact ⟨Submodule.Quotient.mk v,rfl⟩)⟩
  refine { groupEquiv := m.quotientIso
           linearEquiv := LinearEquiv.ofBijective fq hbij
           intertwines := ?_ }
  intro q v
  obtain ⟨l,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
  induction v using Submodule.Quotient.induction_on with
  | _ v => exact hf l v
end CFSG.Quasithin.Chapter12.Section02.RecognitionSource.FusionReducibleNormalizer
