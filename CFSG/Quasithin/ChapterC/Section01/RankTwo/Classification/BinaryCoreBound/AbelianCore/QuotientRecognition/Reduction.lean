module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ModuleData
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.CentralModule
public import Theory.Representation.BinaryOffender.ConjugationGeneration
public import Theory.AtlasPort.ExceptionalIsomorphisms.Simplicity

/-!
# From a whole-core FF-action to an actual natural quotient

For D=[O₂(J),L], (MS3) first gives D≠1. Once D is elementary and the
intrinsic O₂(L) centralizes it, literal component conjugation descends to a
binary action of the specified SL₃(2) quotient. Any such compatible action
has [D,SL₃(2)]=D and is faithful, by simplicity. Its fixed vectors are exactly
C_D(L). A natural linear quotient therefore gives the required surjective
group homomorphism with its exact kernel and a single compatible marking.

The elementary-core, kernel-centrality, and whole-core offender assertions
are NOT established here. They form the remaining local obligation, separate
from recognizing arbitrary binary FF-modules. In particular the central omega
module is never identified with D.

Source: Aschbacher–Smith C.1.31–34, printed pp.135–137, and the binary
specialization of B.5.1, pp.99–103 (combined manuscript, 1 March 2004).
-/

public section

open scoped IsMulCommutative commutatorElement
open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}} {L R : Subgroup J}
variable (h : Input κ L R)

include h in
/-- The commutator core is nontrivial: otherwise L centralizes the central
omega module, contrary to the genuine MS characteristic condition. -/
theorem Input.commutatorCore_ne_bot : commutatorCore L ≠ ⊥ := by
  intro he
  have hc : L ≤ centralizer (pCore 2 J : Set J) := by
    apply commutator_eq_bot_iff_le_centralizer.mp
    rwa [commutator_comm]
  apply h.component_not_centralizes
  exact hc.trans (centralizer_le (fun x hx => (mem_centralModule J x).mp hx |>.1))

namespace AbelianCore.QuotientRecognition
variable [IsElementaryAbelian 2 (commutatorCore L)]
variable (hz : commutatorCore L ≤ centralizer ((pCore 2 L).map L.subtype : Set J))

private noncomputable def conjugation : SL →* MulAut (commutatorCore L) :=
  (QuotientGroup.lift (pCore 2 L) h.coreConjugation (by
    intro n hn
    change h.coreConjugation n = 1
    apply MulEquiv.ext
    intro d
    rw [h.coreConjugation_apply]
    apply Subtype.ext
    change (h.coreConjugate n d : J) = (d : J)
    rw [h.coreConjugate_val, hz d.property n (mem_map_of_mem L.subtype hn),
      mul_inv_cancel_right])).comp
      h.quotientEquiv.symm.toMonoidHom

/-- The binary action on the whole core, once the intrinsic kernel centralizes it. -/
noncomputable def linearAction : Representation (ZMod 2) SL (Additive (commutatorCore L)) where
  toFun g := (conjugation h hz g).toMonoidHom.toAdditive.toZModLinearMap 2
  map_one' := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (conjugation h hz 1 v.toMul) = v
    rw [map_one]
    rfl
  map_mul' g k := by
    apply LinearMap.ext
    intro v
    change Additive.ofMul (conjugation h hz (g * k) v.toMul) = _
    rw [map_mul]
    rfl

/-- Descending through the intrinsic two-core preserves literal conjugation. -/
theorem linearAction_compatible (l : L) (d : commutatorCore L) :
    linearAction h hz (h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l))
      (Additive.ofMul d) = Additive.ofMul (h.coreConjugate l d) := by
  change Additive.ofMul (conjugation h hz
    (h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) d) = _
  simp only [conjugation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.symm_apply_apply]
  exact congrArg Additive.ofMul (h.coreConjugation_apply l d)

/-- A genuine FF-action on the entire elementary core; no module shape is assumed. -/
structure CoreFFAction (h : Input κ L R) where
  representation : Representation (ZMod 2) SL (Additive (commutatorCore L))
  compatible : ∀ (l : L) (d : commutatorCore L),
    representation (h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l)) (Additive.ofMul d) =
      Additive.ofMul (h.coreConjugate l d)
  offending : IsFFModule representation

/-- The remaining input to the canonical descended action is a proved offender. -/
noncomputable def coreFFAction
    (hFF : IsFFModule (linearAction h hz)) : CoreFFAction h where
  representation := linearAction h hz
  compatible := linearAction_compatible h hz
  offending := hFF

variable {h} (a : CoreFFAction h)

/-- Fixed vectors are exactly the literal subgroup C_D(L), on the same carrier. -/
theorem CoreFFAction.mem_fixed (v : Additive (commutatorCore L)) :
    v ∈ fixedSpace a.representation ⊤ ↔ v.toMul ∈ coreFixed L := by
  constructor
  · intro hv l hl
    have hh := congrArg (fun w : Additive (commutatorCore L) => (w.toMul : J))
      (hv ⟨h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩), mem_top _⟩)
    change ((a.representation (h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) ⟨l,hl⟩))
      (Additive.ofMul v.toMul)).toMul : J) = (v.toMul : J) at hh
    rw [a.compatible] at hh
    change (h.coreConjugate ⟨l, hl⟩ v.toMul : J) = (v.toMul : J) at hh
    rw [h.coreConjugate_val] at hh
    exact mul_inv_eq_iff_eq_mul.mp hh
  · intro hv g
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) (h.quotientEquiv.symm g.val)
    have hg : h.quotientEquiv (QuotientGroup.mk' (pCore 2 L) l) = g.val := by
      rw [hl, MulEquiv.apply_symm_apply]
    change a.representation g.val (Additive.ofMul v.toMul) = Additive.ofMul v.toMul
    rw [← hg, a.compatible]
    change h.coreConjugate l v.toMul = v.toMul
    apply Subtype.ext
    rw [h.coreConjugate_val]
    exact mul_inv_eq_iff_eq_mul.mpr (hv l l.property)

/-- The group identity [D,L]=D gives full generation by linear displacements. -/
theorem CoreFFAction.full_commutator :
    subspaceCommutator a.representation ⊤ ⊤ = ⊤ := by
  let f : L →* SL := h.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))
  have hf : Function.Surjective f :=
    h.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)
  let := h.component_normal
  have hh := commutator_eq_top_of_conjugation a.representation (commutatorCore L) L
    (by rw [normalizer_eq_top]; exact le_top) f (MonoidHom.id _) Function.surjective_id
    (fun l d => (a.compatible l d).trans
      (congrArg Additive.ofMul (Subtype.ext (h.coreConjugate_val l d))))
    (by rw [commutator_comm]; exact h.commutatorCore_idempotent)
  rwa [f.range_eq_top_of_surjective hf] at hh

/-- Simplicity and full commutator generation make the compatible action faithful.
Faithfulness is proved here, rather than required by the action interface. -/
theorem CoreFFAction.faithful : Function.Injective a.representation := by
  let : IsSimpleGroup Matrix.PSL3Two.PSL := Atlas.psl_simple_high_rank 3 (by decide)
  let : IsSimpleGroup SL := Matrix.PSL3Two.equiv.isSimpleGroup
  apply a.representation.ker_eq_bot_iff.mp
  rcases (inferInstance : a.representation.ker.Normal).eq_bot_or_eq_top with hk | hk
  · exact hk
  · exfalso
    have hfix : (⊤ : Submodule (ZMod 2) (Additive (commutatorCore L))) ≤
        fixedSpace a.representation ⊤ := by
      intro v _ g
      have hg : g.val ∈ a.representation.ker := by
        rw [hk]
        exact mem_top _
      have hg : a.representation g.val = 1 := hg
      change a.representation g.val v = v
      rw [hg]
      rfl
    have hz := (subspaceCommutator_eq_bot_iff a.representation ⊤ ⊤).mpr hfix
    rw [a.full_commutator] at hz
    have hd : commutatorCore L = ⊥ := by
      apply le_bot_iff.mp
      intro d hd
      have hv : Additive.ofMul (⟨d,hd⟩ : commutatorCore L) ∈
          (⊥ : Submodule (ZMod 2) (Additive (commutatorCore L))) := hz ▸ Submodule.mem_top
      exact congrArg (fun v : Additive (commutatorCore L) => (v.toMul : J)) hv
    exact h.commutatorCore_ne_bot hd

/-- Natural coordinates for the fixed-space quotient give the requested group
quotient. The matrix marking, actual kernel, and conjugation formula all transfer. -/
def CoreFFAction.toNaturalQuotient {m : ℕ} (q : ModuleQuotient a.representation m) :
    AbelianCore.NaturalQuotient h m where
  quotientEquiv := h.quotientEquiv.trans q.marking
  projection := {
    toFun d := Multiplicative.ofAdd (q.projection (Additive.ofMul d))
    map_one' := q.projection.map_zero
    map_mul' x y := q.projection.map_add (Additive.ofMul x) (Additive.ofMul y)
  }
  surjective := by
    intro v
    obtain ⟨d, hd⟩ := q.surjective v.toAdd
    exact ⟨d.toMul, congrArg Multiplicative.ofAdd hd⟩
  kernel := by
    ext d
    change q.projection (Additive.ofMul d) = 0 ↔ d ∈ coreFixed L
    change Additive.ofMul d ∈ q.projection.ker ↔ _
    rw [q.kernel]
    exact a.mem_fixed _
  equivariant := by
    intro l d i
    change q.projection (Additive.ofMul (h.coreConjugate l d)) i = _
    rw [← a.compatible]
    exact q.equivariant _ _ i

end AbelianCore.QuotientRecognition
end CFSG.Quasithin.ChapterC.BinaryMS
