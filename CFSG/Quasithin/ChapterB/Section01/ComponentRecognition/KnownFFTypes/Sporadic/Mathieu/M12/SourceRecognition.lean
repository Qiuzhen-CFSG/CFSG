module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Mathieu.M12.SourceInput
public import Theory.Representation.Mathieu.SmallModules.M12Recognition.CentralCover
public import CFSG.Quasithin.ChapterH.Section10To12.M12Calculations.Ambient
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The source M₁₂ module and its ambient extension, conditional on degree

The full Chapter K inputs make the M₁₂ central cover centerless. The
self-centralizing generalized Fitting subgroup then embeds the ambient
quotient in Out(M₁₂), so the solvable residual is exactly F*(G) and the
ambient group is M₁₂ or Aut(M₁₂). These group conclusions need no module
degree bound.

Given degree at most ten, the proved intrinsic recognition theorem identifies
the actual restricted representation with the permutation heart. The original
central-quotient marking is preserved through the residual identification.
The H.11 construction supplies the faithful automorphism-group extension
and an equivariant embedding of the original actor G with that same marking.
`Recognition.moduleInput` and `Recognition.ambient` are the literal inputs
for the independent H.11 and K.4 module calculations.

The degree bound remains an explicit premise. Thus this module supplies the
cover, identification and extension steps, while the source recognition task
still requires the M₁₂ degree consequence of Guralnick--Malle. No theorem here
asserts that consequence.

Source: Aschbacher--Smith, Chapter K introduction and K.4, printed pp.451,
457--460, especially K.4.4, and H.11, pp.392--393 (1 March 2004 manuscript).
The degree classification cited by K.4 is Guralnick--Malle, *Classification of
2F-modules, I*, Theorem 6.6 and Table 6.7, DOI 10.1016/S0021-8693(02)00526-4.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
open _root_.Sporadic.Mathieu
open CFSG.Quasithin.ChapterH.Section10To12
open CFSG.Quasithin.ChapterH.Section10To12.M12Calculations
open Representation.MathieuSmall.M12Recognition

private theorem outer_solvable : Group.IsSolvable (MulAut.Outer M12) := by
  have hb := M12A5Fixer.Automorphisms.outerIndexBound
  change Nat.card (MulAut.Outer M12) ≤ 2 at hb
  have hp : 0 < Nat.card (MulAut.Outer M12) := Nat.card_pos
  have hc : Nat.card (MulAut.Outer M12) = 1 ∨ Nat.card (MulAut.Outer M12) = 2 := by omega
  have hd : Nat.card (MulAut.Outer M12) ∣ 2 := (Nat.dvd_prime Nat.prime_two).mpr hc
  let : IsCyclic (MulAut.Outer M12) := isCyclic_of_card_dvd_prime hd
  exact Group.isSolvable_of_comm (IsMulCommutative.is_comm.comm)

variable {G V : Type*} [Group G] [Finite G]
  [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (h : Hypotheses ρ)
  (e : ((generalizedFitting G) ⧸ center (generalizedFitting G)) ≃* M12)

include h e in
/-- The actual source component is centerless, including all initially allowed covers. -/
theorem source_center_eq_bot : center (generalizedFitting G) = ⊥ := by
  let := h.quasisimple
  exact CentralCover.center_eq_bot (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) h.irreducible e

include h e in
/-- The ambient centralizer of the source generalized Fitting subgroup is trivial. -/
theorem source_centralizer_eq_bot :
    centralizer (generalizedFitting G : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  have hxL := centralizer_generalizedFitting_le G hx
  have hz' : (⟨x, hxL⟩ : generalizedFitting G) ∈ center (generalizedFitting G) := by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_centralizer_iff.mp hx y y.property)
  rw [source_center_eq_bot ρ h e, mem_bot] at hz'
  exact congrArg Subtype.val hz'

include h e in
/-- The literal solvable residual agrees with the source generalized Fitting subgroup. -/
theorem source_residual_eq : solvableResidual G = generalizedFitting G := by
  let := h.quasisimple
  let f := CentralCover.groupEquiv (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) h.irreducible e
  let := outer_solvable
  let : Group.IsSolvable (MulAut.Outer (generalizedFitting G)) :=
    MulAut.isSolvable_outer_of_mulEquiv f
  let := quotient_isSolvable_of_centralizer_eq_bot (generalizedFitting G)
    (source_centralizer_eq_bot ρ h e)
  exact le_antisymm (solvableResidual_le_of_solvable_quotient _)
    (le_solvableResidual_of_isPerfect _)

include h e in
/-- The permissible ambient groups, before any degree bound or module recognition. -/
theorem source_group_alternatives :
    Nonempty (G ≃* M12) ∨ Nonempty (G ≃* MulAut M12) := by
  let := h.quasisimple
  let f := CentralCover.groupEquiv (ρ.comp (generalizedFitting G).subtype)
    (h.faithful.comp Subtype.val_injective) h.irreducible e
  rcases M12SmallPair.ValueBoundParabolics.Ambient.ambient_equiv_alternatives
    (generalizedFitting G) (source_centralizer_eq_bot ρ h e) f with
    ⟨_, he⟩ | ⟨E, _⟩
  · exact Or.inl he
  · exact Or.inr ⟨E.trans M12ExceptionalExtension.automorphismEquiv⟩

/-- The marked source module and actual faithful ambient extension. This record
specifies the output; its conditional construction is proved below. -/
structure Recognition where
  residual_eq : solvableResidual G = generalizedFitting G
  moduleInput : M12ModuleInput ρ
  quotient_mark : ∀ r : solvableResidual G,
    moduleInput.residualEquiv r =
      e (QuotientGroup.mk' (center (generalizedFitting G))
        ⟨(r : G), residual_eq.le r.property⟩)
  ambient : AmbientExtension ρ moduleInput
  group_alternatives : Nonempty (G ≃* M12) ∨ Nonempty (G ≃* MulAut M12)

include h in
/-- Construct the exact module and ambient action from the source inputs and
an explicit degree bound. Final K.4 assembly must discharge that bound. -/
theorem source_recognition_of_finrank_le_ten (hd : Module.finrank (ZMod 2) V ≤ 10) :
    Nonempty (Recognition ρ e) := by
  let := h.quasisimple
  let σ := ρ.comp (generalizedFitting G).subtype
  have hf : Function.Injective σ := h.faithful.comp Subtype.val_injective
  let f := CentralCover.groupEquiv σ hf h.irreducible e
  obtain ⟨E⟩ := CentralCover.equiv_heart_of_finrank_le_ten σ hf h.irreducible e hd
  have hR := source_residual_eq ρ h e
  let fR : solvableResidual G ≃* M12 := (MulEquiv.subgroupCongr hR).trans f
  let ER : Representation.Equiv (ρ.comp (solvableResidual G).subtype)
      (m12HeartRepresentation.comp fR.toMonoidHom) :=
    { toLinearEquiv := E.toLinearEquiv
      isIntertwining' := fun r => E.isIntertwining' ((MulEquiv.subgroupCongr hR) r) }
  let hM : M12ModuleInput ρ := ⟨h.faithful, fR, ER⟩
  refine ⟨{
    residual_eq := hR
    moduleInput := hM
    quotient_mark := ?_
    ambient := ambientExtension ρ hM
    group_alternatives := source_group_alternatives ρ h e }⟩
  intro r
  exact CentralCover.groupEquiv_apply σ hf h.irreducible e ((MulEquiv.subgroupCongr hR) r)

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.M12Source
