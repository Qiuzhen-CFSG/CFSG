module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCartan
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesOriginalCore

/-!
# The remaining cubic obstruction in the two original cores

The original chosen module gives characteristic two for LT. Its Cartan
and actual PSL₂ quotient put V₂[S,S] in O₂(L). The C-fixed factor is
exactly [S,S] intersect C_G(C), disjoint from V₂, and also lies in the
two-core of the original point centralizer. It centralizes the original
chosen module, whose carrier is kept distinct from the four-plane V₂.

Under the contrary nonabelian-span assumption this is a nontrivial
B-normalized elementary subgroup. The source abelian-span theorem still
requires its exclusion from the full ambient geometry; none of those
extra normalization or vanishing conclusions is assumed here.

Source: Aschbacher--Smith 5.1.21--23, printed pp.644--646,
refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

/-- The entire elementary derived layer lies in the original left two-core. -/
theorem linear_cubic_nonabelian_original_core
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    S.V ⊔ ⁅S.S g,S.S g⁆ ≤ L.pCoreIn 2 := by
  have hchar : L ⊔ (T : Subgroup G) ∈ Chapter1.He G := by
    apply Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
    refine ⟨?_,fun x hx => mem_sup_right hx⟩
    intro he
    exact D.ne_bot (bot_unique (D.le_core.trans he.le))
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  exact core_commutator_plane_le_original_core c d s b D.sylow_normalizes_component
    hpsl (Chapter1.mem_He_iff.mp hchar) g hg hgn

/-- A contrary original span produces a nontrivial fixed derived subgroup
in both literal two-cores, centralizing the original chosen module. -/
theorem linear_cubic_nonabelian_common_core_obstruction
    (D : ChosenModule T L V)
    (h : Hypothesis1221 KnownSimple.IsKnownSimple T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hK : residual H ∈ Chapter1.LStar G (T : Subgroup G))
    (hnf : ¬ ChapterA.Section04.IsFaithfulSignalizerType (residual H))
    (hlinear : ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : LinearFieldCartan T L H A B C n)
    (d : CubicEscape.LocalData T H C z) (hn : 1 < n)
    (hne : ¬ IsMulCommutative (conjugateSpanBy (CubicEscape.plane C z)
      (centralizer ({z} : Set G)))) :
    ∃ g ∈ C, g ∉ normalizer (zpowers z : Set G) ∧
      let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
      let F := S.V ⊔ ⁅S.S g,S.S g⁆
      let X := F ⊓ centralizer (C : Set G)
      F = S.V ⊔ X ∧ X = ⁅S.S g,S.S g⁆ ⊓ centralizer (C : Set G) ∧
        X ≤ L.pCoreIn 2 ⊓ (centralizer ({z} : Set G)).pCoreIn 2 ∧
        X ≤ centralizer (V : Set G) ∧
        IsElementaryAbelian 2 X ∧ X ≠ ⊥ ∧ Disjoint S.V X ∧
        B ≤ normalizer (X : Set G) := by
  obtain ⟨g,hg,hgn⟩ := d.exists_moving_cubic
  let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
  let F := S.V ⊔ ⁅S.S g,S.S g⁆
  let X := F ⊓ centralizer (C : Set G)
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  obtain ⟨hF,hEX,hXE,hBX,hnX,_⟩ :=
    linear_cubic_nonabelian_cartan_fixed_commutator D h hH hK hnf hlinear hpsl c d hn hne g hg hgn
  obtain ⟨hderived,hdis⟩ := core_commutator_fixed_factor c d s b g hg hgn
  have hFK : F ≤ L.pCoreIn 2 := linear_cubic_nonabelian_original_core D h hpsl c d hne g hg hgn
  have hXK : X ≤ L.pCoreIn 2 := inf_le_left.trans hFK
  have hXQ : X ≤ (centralizer ({z} : Set G)).pCoreIn 2 :=
    hXE.trans (inf_le_left.trans s.U_le_core)
  have hJL : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hXV : X ≤ centralizer (V : Set G) :=
    (hXK.trans (pCoreIn_mono_of_normalizes (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left)
      hJL)).trans D.core_centralizes
  have hXne : X ≠ ⊥ := by
    intro he
    exact hnX (he.le.trans bot_le)
  exact ⟨g,hg,hgn,hF,hderived,le_inf hXK hXQ,hXV,hEX,hXne,hdis,hBX⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
