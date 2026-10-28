module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.SourceGeometry
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Commutator
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction

/-!
# The actual A₅ component action before selecting a component

The original context supplies F.9.1, all13.5.13 geometry, the module order,
and the genuine F.9.5(2) commutator theorem. The literal representation
of H/O₂(H) on U_H/V₁ is faithful and its V-image has fixed codimension
two. Its non-two conjugate pairs are S₃ under the remaining earlier
F.9.5(6) source theorem. These are the action inputs of13.5.20 on the
original quotient, not an assumed model action.
Source: Aschbacher–Smith13.5.20, printed p.923.
-/
public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
open ComponentReduction.Fitting.SourceAction Representation.BinaryOffender
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G} [IsElementaryAbelian 2 V]
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ → ∀ (S : Sylow 2 Y) (B : Subgroup Y),
    B ∈ ChapterA.Section03.localCComponents S → Chapter1.Section02.A312Conclusion B)
  (hH : H ∈ Source.Hz (residualCentralizer L V₁) (T : Subgroup G)
    (centralizer (V₁ : Set G)) (normalizer (L : Set G)))
  (hU : ¬ IsMulCommutative (Source.UH H V₃))
include d hA312 hH hU

/-- The original component-action inputs, retaining only genuine F.9.5(6). -/
theorem source_component_action (hsix : F95Six (G := G)) :
    let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
    let hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
    let : (D.V₁.subgroupOf D.UH).Normal := point_normal_in_UH hf
    let : IsElementaryAbelian 2 (Quotient (D := D)) := quotient_elementary hf
    Function.Injective (representation hf) ∧
      fixedCodim (representation hf) (Source.starImage H V) = 2 ∧
      ∀ x : Source.Hstar H, ¬ IsPGroup 2 (Source.starImage H V ⊔
        (Source.starImage H V).map (MulAut.conj x).toMonoidHom : Subgroup (Source.Hstar H)) →
        Nonempty ((Source.starImage H V ⊔
          (Source.starImage H V).map (MulAut.conj x).toMonoidHom : Subgroup (Source.Hstar H)) ≃*
          Equiv.Perm (Fin 3)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  have hr : let := hf.elementary; Module.finrank (ZMod 2) (Additive D.V) = 4 :=
    (card_V_iff_rank_four hf).mp d.module_card
  apply action_and_pairs source_F95Two hsix hf V₂ (normalizer (L : Set G))
    d.third_index hU hr d.plane_transport
  · intro g hg hp
    have hn := source_plane_normalizes d hA312 hH hU hg hp
    exact Or.inr (le_inf (hn.trans d.module_normalizer) hn)
  · exact inf_le_right.trans ((d.seed_normalizer hA312).trans d.module_normalizer)
  · have hc : normalizer (L : Set G) ⊓ centralizer (V₃ : Set G) ≤ centralizer (V : Set G) :=
      d.third_centralizer_local.le
    rw [commutator_comm,commutator_eq_bot_iff_le_centralizer.mpr hc]
    exact bot_le

end CFSG.Quasithin.Chapter13.Section05.A5Source
