module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SelfDualFF.Commutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.EdgeStructure.Containment.AbelianSpans.Offender.SelfDualFF.Forms
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.ExtensionControl

/-!
# Faithful self-dual binary SL₃(2) modules are not FF

Pass to the literal commutator submodule `C = [V, G]`. Perfectness proves
`[C, G] = C`, simplicity and faithfulness make its action faithful, and fixed
codimension monotonicity passes an offender from `V` to `C`. The existing
binary FF classification now supplies a homogeneous natural quotient of `C`
by its fixed space, with one common marking of the actual matrix group.

Self-duality of `V` supplies a nondegenerate invariant bilinear form. Its
restriction to `C` vanishes by `Forms`, including when the extension by fixed
vectors is nonsplit. Annihilator duality then makes `C` fixed in `V`.
Perfectness would make the whole action trivial, contradicting faithfulness.

This is the binary model obstruction used in the first paragraph of
Meierfrankenfeld–Stellmacher, *Pushing up weak BN-pairs of rank two* (1993),
(4.6.4), printed p.902. The central-quotient action and the source-theorem
assembly remain in the parent development; the theorem here needs only
faithfulness, finite dimension and self-duality over the same literal SL₃(2).
-/

public section

set_option backward.isDefEq.respectTransparency false
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
open AbelianCore.QuotientRecognition SelfDualFF

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) SL V)

private lemma commutator_not_fixed (hρ : Function.Injective ρ) :
    ¬ Coinvariants.ker ρ ≤ fixedSpace ρ ⊤ := by
  let : Group.IsPerfect SL := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  intro hc
  have hall := le_fixedSpace_of_commutator_le_fixedSpace ρ ⊤ ⊤
    (le_subspaceStabilizer ρ ⊤ (by simp)) ((fullCommutator_eq ρ).symm ▸ hc)
  obtain ⟨g, hg⟩ := exists_ne (1 : SL)
  apply hg
  apply hρ
  apply LinearMap.ext
  intro v
  have h := hall (show v ∈ (⊤ : Submodule (ZMod 2) V) from Submodule.mem_top)
    ⟨g, Subgroup.mem_top g⟩
  change ρ g v = v at h
  simpa only [map_one, Module.End.one_apply] using h

private lemma commutator_faithful (hρ : Function.Injective ρ) :
    Function.Injective (commutatorSubrepresentation ρ).toRepresentation := by
  let : IsSimpleGroup SL := Atlas.Comparisons.Exceptional.sl3Two_simple
  let σ := (commutatorSubrepresentation ρ).toRepresentation
  rcases (inferInstance : σ.ker.Normal).eq_bot_or_eq_top with hb | ht
  · exact σ.ker_eq_bot_iff.mp hb
  · have he : σ = 1 := MonoidHom.ker_eq_top_iff.mp ht
    apply False.elim
    apply commutator_not_fixed ρ hρ
    intro v hv g
    have h : σ g ⟨v, hv⟩ = ⟨v, hv⟩ := by rw [he]; rfl
    exact congrArg Subtype.val h

variable [FiniteDimensional (ZMod 2) V]

/-- A faithful finite-dimensional binary representation of the literal SL₃(2)
cannot be both self-dual and an FF-module. The equivalence to the dual keeps
the acting matrix group fixed; no twist of the action is assumed. -/
theorem not_isFFModule_of_faithful_selfDual
    (hρ : Function.Injective ρ) (hdual : Nonempty (ρ.Equiv ρ.dual)) :
    ¬ IsFFModule ρ := by
  let : Group.IsPerfect SL := Atlas.sl_perfect (F := ZMod 2) 3 (by decide)
  intro hFF
  obtain ⟨e⟩ := hdual
  let C := commutatorSubrepresentation ρ
  have hfull : subspaceCommutator C.toRepresentation ⊤ ⊤ = ⊤ := commutator_full ρ
  have hFFC : IsFFModule C.toRepresentation := by
    obtain ⟨A, hA, hbudget⟩ := hFF
    exact ⟨A, hA, (fixedCodim_subrepresentation_le ρ C A).trans hbudget⟩
  obtain ⟨m, _, ⟨q⟩⟩ := ExtensionControl.exists_moduleQuotient C.toRepresentation
    (commutator_faithful ρ hρ) hfull hFFC
  let B := e.toLinearEquiv.toLinearMap.compl₁₂ C.toSubmodule.subtype C.toSubmodule.subtype
  have hB (g : SL) (v w : C.toSubmodule) :
      B (C.toRepresentation g v) (C.toRepresentation g w) = B v w := by
    change e (ρ g v) (ρ g w) = e v w
    have he := LinearMap.congr_fun (e.isIntertwining' g) (v : V)
    change e (ρ g v) = ρ.dual g (e v) at he
    rw [he]
    change e v (ρ g⁻¹ (ρ g w)) = e v w
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hzero := form_zero_of_moduleQuotient C.toRepresentation hfull q B hB
  apply commutator_not_fixed ρ hρ
  intro v hv g
  have hfix : e v ∈ ρ.dual.invariants := by
    rw [← dualAnnihilator_coinvariantsKer]
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    have h := LinearMap.congr_fun (LinearMap.congr_fun hzero (⟨v, hv⟩ : C.toSubmodule))
      (⟨w, hw⟩ : C.toSubmodule)
    exact h
  apply e.toLinearEquiv.injective
  exact (LinearMap.congr_fun (e.isIntertwining' g.val) v).trans (hfix g.val)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Containment.SpanOffender
