module
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.RankOneModuleGenericExceptionalLinearFieldEscapeModulesFixedLine
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldEscapeModulesCartan

/-!
# A Cartan-invariant obstruction in the original derived core

If the original centralizer span is nonabelian, the established cubic
lower bound forces [S,S] not to lie in the original plane V. The Cartan
splitting then constructs X = (V[S,S]) intersect C_G(C), an elementary
subgroup of the actual S₂, normalized by B and not contained in V.
The accompanying commutator and normalization conclusions retain the
original I, S and faithful opposite projection.

The remaining ambient exclusion of this specific subgroup belongs to the
abelian-span argument; no exclusion or abelianness conclusion is assumed
or asserted here.

Source: Aschbacher--Smith 5.1.22--23, printed pp.645--646,
refs/quasithin.pdf.
-/

public section

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter6.Source.RankOneGeneric CubicEscape ChapterG.Section02.Setup
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V H A B C : Subgroup G} {n : ℕ} {z : G}

theorem linear_cubic_nonabelian_cartan_fixed_commutator
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
      (centralizer ({z} : Set G))))
    (g : G) (hg : g ∈ C) (hgn : g ∉ normalizer (zpowers z : Set G)) :
    let S := CubicEscape.setup T (centralizer ({z} : Set G)) C z
    let F := S.V ⊔ ⁅S.S g,S.S g⁆
    let X := F ⊓ centralizer (C : Set G)
    F = S.V ⊔ X ∧ IsElementaryAbelian 2 X ∧ X ≤ S.S₂ g ∧
      B ≤ normalizer (X : Set G) ∧ ¬ X ≤ S.V ∧ ⁅S.I g,B⁆ ≤ S.S g ∧
      (B.subgroupOf S.H).map (SpanAction.projection (linear_cubic_centralizer_setup h d)) ≤
        normalizer ((((conjugate (S.W g) g).subgroupOf S.H).map
          (SpanAction.projection (linear_cubic_centralizer_setup h d))) :
          Set (SpanAction.Actor (linear_cubic_centralizer_setup h d))) := by
  intro S F X
  let s := linear_cubic_centralizer_setup h d
  let b := d.binaryNaturalData c D.sylow_normalizes_component hpsl s hne
  obtain ⟨hF,hEF,hXE,hBX⟩ := core_commutator_fixed_split c d s b g hg hgn
  let : IsElementaryAbelian 2 F := hEF
  have hX : IsElementaryAbelian 2 X := IsElementaryAbelian.of_le (show X ≤ F from inf_le_left)
  have hnX : ¬ X ≤ S.V := by
    intro hx
    apply linear_cubic_nonabelian_core_commutator D h hH hK hnf hlinear hpsl c d hn hne g hg hgn
    exact (show ⁅S.S g,S.S g⁆ ≤ F from le_sup_right).trans
      (hF.le.trans (sup_le le_rfl hx))
  exact ⟨hF,hX,hXE,hBX,hnX,right_cartan_commutator_le_core c d s b g hg hgn,
    right_cartan_normalizes_opposite_image c d s g hg⟩

end CFSG.Quasithin.Chapter12.Section02.ChosenModule
