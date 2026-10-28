module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.AlternatingSixMoved
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.Movement
public import Theory.Alternating.Aut
public import CFSG.Quasithin.KnownSimpleSectionTransport
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.AmbientLayer
/-!
# The native MS93 moving layer in the natural symplectic case

Apply the proved B.5.1 order-360 FF recognition to a normal elementary layer
containing the specified natural subgroup. The projection is restricted to
its actual range in S6, so both the original source and its characteristic
replacement have the same argument. The subgroup inclusion and the original
coordinates identify its full component commutator with the native subgroup.
The literal graph layers then satisfy [X,Ltilde] = [Z,Ltilde] = W: the Z-layer
lies between W and X, and the marked subgroup is fully moved.

The local FF hypothesis is supplied by the source offender calculation; no
splitting assertion or additional module-classification hypothesis is used.
Source: MS93 (3.2)(vi), printed pp.863–864; Aschbacher–Smith B.5.1.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
variable {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)
include s

omit s [Group M] [Finite M] [L.Normal] [W.Normal] in
private theorem alternatingSix_quasisimple : IsQuasisimple (alternatingGroup (Fin 6)) where
  toIsPerfect := ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  simple := by
    let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    exact ((QuotientGroup.quotientMulEquivOfEq
      (alternatingGroup.center_eq_bot (by simp))).trans QuotientGroup.quotientBot).isSimpleGroup

/-- Recognition on any actual central elementary layer containing the native
module, for the original S6 projection restricted to its literal range. -/
theorem centralLayer_commutator
    (X : Subgroup M) [X.Normal] [IsElementaryAbelian 2 X]
    (hWX : W ≤ X)
    (hX : s.projection.ker = centralizer (X : Set M))
    (hsq : IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6)))
    (hff : IsFFModule (NormalElementaryQuotient.representation X s.projection.rangeRestrict
      s.projection.rangeRestrict_surjective (by simpa using hX))) :
    ⁅X,L⁆ = W := by
  let H := s.projection.range
  let C := (alternatingGroup (Fin 6)).subgroupOf H
  let e : C ≃* alternatingGroup (Fin 6) := subgroupOfEquivOfLe s.image_contains_alternating
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup C := e.isSimpleGroup
  let := alternatingSix_quasisimple
  let : IsQuasisimple C := IsQuasisimple.of_mulEquiv e.symm
  have hLC : L.map s.projection.rangeRestrict = C := by
    apply (map_injective H.subtype_injective)
    rw [map_map,map_subgroupOf_eq_of_le s.image_contains_alternating]
    exact s.component_image
  have hc : Nat.card C = 360 := by
    rw [Nat.card_congr e.toEquiv,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hC : centralizer (C : Set H) = ⊥ := by
    apply bot_unique
    intro x hx
    have hm : (x : Equiv.Perm (Fin 6)) ∈ centralizer (alternatingGroup (Fin 6) : Set (Equiv.Perm (Fin 6))) := by
      intro y hy
      exact congrArg Subtype.val (hx ⟨y,s.image_contains_alternating hy⟩ hy)
    rw [GroupTheory.AutAlternating.centralizer_alternatingGroup_eq_bot 6 (by decide)] at hm
    exact mem_bot.mpr (Subtype.ext (mem_bot.mp hm))
  let := s.module_elementary
  apply ChapterB.QuasisimpleSource.normalElementary_card360_commutator_eq W X hWX
    s.projection.rangeRestrict s.projection.rangeRestrict_surjective _ _ L C hLC hc hC
    ((IsSQTK.equiv e).mpr hsq) hff s.module_eq_commutator
  · simpa using s.projection_kernel.trans s.module_centralizer.symm

/-- Once the X-layer has the marked moving subgroup, the intermediate actual
Z-layer has exactly the same commutator; its own FF classification is unnecessary. -/
theorem amalgam_moving_layer
    (hx : ⁅X R (alpha R),Ltilde R (alpha R)⁆ = W.map (embedM R)) :
    ⁅X R (alpha R),Ltilde R (alpha R)⁆ = U R (alpha R) ∧
      U R (alpha R) = W.map (embedM R) := by
  have hl : Ltilde R (alpha R) = L.map (embedM R) := by
    rw [Ltilde_alpha,s.residual]
  have hw : ⁅W.map (embedM R),Ltilde R (alpha R)⁆ = W.map (embedM R) := by
    rw [hl,← map_commutator,s.module_eq_commutator]
  have hu : U R (alpha R) = W.map (embedM R) := by
    apply le_antisymm
    · exact (commutator_mono s.Z_le_X le_rfl).trans hx.le
    · rw [← hw]
      exact commutator_mono s.module_le_Z le_rfl
  exact ⟨hx.trans hu.symm,hu⟩
/-- Native MS93 (3.2) natural moving-layer identification. -/
theorem native_natural_moving_layer
    (hsq : IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6))) :
    ⁅X R (alpha R),Ltilde R (alpha R)⁆ = U R (alpha R) ∧
      U R (alpha R) = W.map (embedM R) := by
  let := s.ambientX_normal
  let := omegaCenter_elementary (pCore 2 M)
  have hc : ⁅ambientX (M := M),L⁆ = W :=
    s.centralLayer_commutator (ambientX (M := M)) s.module_le_ambientX
      (by simpa only [MonoidHom.ker_rangeRestrict] using s.ambientX_kernel)
      hsq s.ambientX_isFFModule
  apply s.amalgam_moving_layer
  rw [s.X_alpha_eq,Ltilde_alpha,s.residual,← map_commutator,hc]
/-- The source SQTK condition supplies its A6 section directly. -/
theorem alternating_sqtk (hsq : IsSQTK KnownSimple.IsKnownSimple M) :
    IsSQTK KnownSimple.IsKnownSimple (alternatingGroup (Fin 6)) := by
  have hquot : IsSQTK KnownSimple.IsKnownSimple (M ⧸ pCore 2 M) := by
    refine ⟨?_,hsq.isKGroup.quotient (pCore 2 M)⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho (pCore 2 M) pCore_isPGroup).trans
      (hsq.stronglyQuasithin p hp ho)
  have hker : s.projection.rangeRestrict.ker = pCore 2 M := by
    rw [MonoidHom.ker_rangeRestrict,s.projection_kernel]
  let e : M ⧸ pCore 2 M ≃* s.projection.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective s.projection.rangeRestrict
        s.projection.rangeRestrict_surjective)
  have hH : IsSQTK KnownSimple.IsKnownSimple s.projection.range :=
    IsSQTK.knownSimple_of_equiv e hquot
  exact (IsSQTK.equiv (subgroupOfEquivOfLe s.image_contains_alternating)).mp
    (hH.subgroup ((alternatingGroup (Fin 6)).subgroupOf s.projection.range))

/-- The source-local SQTK hypothesis is the only external hypothesis of the
native moving-layer conclusion. Every FF and coordinate premise is proved. -/
theorem natural_moving_layer (hsq : IsSQTK KnownSimple.IsKnownSimple M) :
    ⁅X R (alpha R),Ltilde R (alpha R)⁆ = U R (alpha R) ∧
      U R (alpha R) = W.map (embedM R) :=
  s.native_natural_moving_layer (s.alternating_sqtk hsq)

end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
