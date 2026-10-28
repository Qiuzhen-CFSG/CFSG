module
public import CFSG.Quasithin.Chapter13.Section05.A5Source.PlaneControl
public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.SourceAction.Pairs

/-!
# Original A₅ geometry in13.5.13 and its F.9.5 consumer

The original source context constructs the plane conjugator, plane
normalization, seed index and centralizer bound. This proves all of
13.5.13 on the original H and the literal starred quotient. Its F.9.5(6)
application retains only that genuine earlier theorem; no additional
plane, transitivity, module marking or F.9.1 premise is assumed.
Source: Aschbacher–Smith13.5.13 and13.5.19–20, printed pp.919,923.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section05.A5Source
open Section06.TerminalContradiction.Ratio Section08
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

/-- Original13.5.13(1), with every earlier geometry premise discharged. -/
theorem source13_5_13_one {g : G} (hg : g ∈ H)
    (hi : V₁ < V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    IsPGroup 2 (V ⊔ V.map (MulAut.conj g).toMonoidHom : Subgroup G) :=
  source13_5_13_of_plane_control d hA312 hH hU
    (fun _ hk hp => source_plane_normalizes d hA312 hH hU hk hp) hg hi

/-- Original13.5.13(2): the exact F.9.5(5–6) antecedents, with the book's
right-conjugation convention and the original starred image. -/
theorem source13_5_13 :
    Source.starImage H V ≠ ⊥ ∧
      (∀ g ∈ H, V₁ < V ⊓ ChapterG.Section02.Setup.conjugate V g →
        IsPGroup 2 (V ⊔ ChapterG.Section02.Setup.conjugate V g : Subgroup G)) ∧
      ⁅V,H ⊓ centralizer (V₃ : Set G)⁆ ≤ V₁ := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  refine ⟨?_,?_,source_seed_centralizer_bound d hA312⟩
  · intro he
    have hc := LocalGeometry.star_V_card_two hf d.third_index hU
    change Nat.card (Source.starImage H V) = 2 at hc
    rw [he] at hc
    simp at hc
  · intro g hg hi
    exact source13_5_13_one d hA312 hH hU (H.inv_mem hg) hi

/-- The literal pair application used in13.5.19–20 now needs only the
genuine earlier F.9.5(6) source theorem. -/
theorem source_non_two_pair
    (hsix : ComponentReduction.Fitting.SourceAction.F95Six (G := G))
    {g : G} (hg : g ∈ H)
    (hn : ¬ IsPGroup 2 (Source.starImage H
      (V ⊔ ChapterG.Section02.Setup.conjugate V g))) :
    Nonempty (Source.starImage H (V ⊔ ChapterG.Section02.Setup.conjugate V g) ≃*
      Equiv.Perm (Fin 3)) := by
  let D : ChapterF.Section09.Setup G := ⟨T,L,V,V₃,V₁,H⟩
  have hf : D.Hypothesis := (source13_5_7 d hA312 hH).f9Hypothesis
  obtain ⟨hv,hpair,hcentral⟩ := source13_5_13 d hA312 hH hU
  exact hsix D hf d.third_index hv hpair hcentral d.module_card g hg hn

end CFSG.Quasithin.Chapter13.Section05.A5Source
