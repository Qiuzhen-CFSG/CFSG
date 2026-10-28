module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment.Normalization

/-!
# The corrected common three-space in original 11.2.2(5)

The completed parameter and reciprocal-root source families supply the actual
actors, their actions on the entire chosen module, m=2n and r>2n. The ambient
normalization argument now proves that every noncentral Vᵍ in T contains the
whole original C_V(L). Applying the checked root pullback therefore places
an L-conjugate of the full third flag preimage inside V intersect Vᵍ.
No central term is discarded and no false RootSpan.moved field is constructed.

Only the permitted earlier-source maximal-local uniqueness, third-space
centralizer bound and fixed-line conclusions remain explicit; their final
discharge belongs to qt-d-1222-natural-local-geometry. The common full-plane
reconstruction and final weak-closure assembly remain with
qt-d-1222-natural-weak-closure-source. These results establish the repaired
central-containment step, not the entire weak-closure clause.
Source: Aschbacher--Smith 11.2.2(5), printed p.768.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open scoped IsMulCommutative
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.Chapter12.Section02 CFSG.Quasithin.ChapterE
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment
open Atlas.G2 Atlas.G2.Natural
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    (D : ChosenModule T L V) (S : D.NonbinaryNaturalInput)
    (m : ActionEquiv D.centralQuotientAction
      (restrictScalars (k := ZMod 2) (g2Natural S.field.Carrier)))
    (f : InvariantFlag (Coordinates.g2 m))
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → L ≤ N → N = normalizer (L : Set G))
    (hthree : centralizer (f.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (hline : f.Vi 0 ≤ V ⊓ centralizer (sourceTL T L : Set G))

include D S m f hunique hthree hline

/-- The actual noncentral conjugate contains the whole original covering center.
Only the permitted preceding source conclusions remain explicit. -/
theorem source_central_containment (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    V ⊓ centralizer (L : Set G) ≤ V.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨u,a,hact,-,ha,hroots⟩ :=
    ReciprocalRoots.source_root_family D S m f hunique hthree hline g hg hnon
  exact central_le_conjugate D S (ActorRecognition.recentered D S m u) hunique
    (Parameters.source_parameters D S f hunique hthree hline).1
    (RootPullback.strict_globalR_of_preceding D S m f hunique hthree hline)
    g a hact ha hroots

/-- The corrected root-transfer step on the literal original flag. No term
is removed from the full central preimage, and no RootSpan.moved is assumed. -/
theorem source_common_threeSpace (g : G)
    (hg : V.map (MulAut.conj g).toMonoidHom ≤ T)
    (hnon : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    ∃ l : L, (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom ∧
      (f.Vi 2).map (MulAut.conj (l : G)).toMonoidHom ≠ ⊥ := by
  obtain ⟨l,-,hl⟩ := ActorRecognition.flag_containment_of_preceding
    D S m f hunique hthree hline g hg hnon
  refine ⟨l,le_inf ?_ (hl.mpr
    (source_central_containment D S m f hunique hthree hline g hg hnon)),?_⟩
  · exact (map_mono (D.centralQuotientPreimage_le _)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (D.normalizes l.property))
  · intro he
    exact f.V_ne_bot 2 ((map_eq_bot_iff_of_injective _ (MulAut.conj (l : G)).injective).mp he)

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.WeakClosure.G2.CentralContainment
