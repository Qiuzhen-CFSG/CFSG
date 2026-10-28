module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinarySylow
public import CFSG.Quasithin.Chapter7.Section06To07.Terminal
public import CFSG.Quasithin.ChapterE.Section03.Offenders
public import Stellmacher.ElementaryAbelianMaxFusion
public import Theory.GroupTheory.SubgroupConjugateIncidence
public import Theory.GroupTheory.InvolutionCentralizerControl

/-!
# The binary doubled terminal argument

Thompson normalizer control places the whole two-core of C_G(Z) in the
orbit normalizer for every Z in the orbit. Burnside fusion corrects a
conjugator through a shared involution line to an element of C_G(Z).
Finally, when w=1 and r>1, every normalizing hyperplane of a noncommuting
conjugate realizes the weak-closure minimum: otherwise centralization of
that hyperplane and the r bound would force the conjugates to commute.

The original chosen-module application in `NonFFSourceDoubledBinaryTerminal`
uses these facts with the proved pair-generation theorem in relative
Baer--Suzuki. It keeps the centralizer core and both orbit conjugates literal.
Source: Aschbacher--Smith 3.2.10(2,3,6,8) and 7.6.1,
printed pp.583--584,702--703, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Stellmacher Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTerminal
open ChapterE
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Thompson control places the entire local core in the prescribed normalizer. -/
theorem centralizer_core_le_of_thompson
    (W M : Subgroup G) (T : Sylow 2 G)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hcontrol : ∀ R : Subgroup G, IsPGroup 2 R →
      elementaryAbelianMaxJ (T : Subgroup G) ≤ R → normalizer (R : Set G) ≤ M)
    {Z : Subgroup G} (hZW : Z ≤ W) : (centralizer (Z : Set G)).pCoreIn 2 ≤ M := by
  let C := centralizer (Z : Set G)
  let Q := C.pCoreIn 2
  let J := elementaryAbelianMaxJ (T : Subgroup G)
  have hJT : J ≤ (T : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJC : J ≤ C := hJ.trans (centralizer_le hZW)
  have hCN : C ≤ normalizer (Q : Set G) :=
    C.le_normalizer.trans (normalizer_le_normalizer_characteristic_image C (pCore 2 C))
  have hp : IsPGroup 2 (Q ⊔ J : Subgroup G) :=
    (isPGroup_pCoreIn 2 C).to_sup_of_normal_left' (T.isPGroup'.to_le hJT) (hJC.trans hCN)
  exact le_sup_left.trans ((Q ⊔ J).le_normalizer.trans (hcontrol _ hp le_sup_right))

/-- Thompson fusion moves a conjugate through a shared line by its centralizer. -/
theorem line_conjugate_through
    (W M : Subgroup G) (T : Sylow 2 G)
    (hMW : M ≤ normalizer (W : Set G))
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (W : Set G))
    (hNJ : normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ M)
    {Z : Subgroup G} (hZW : Z ≤ W) (hZ : Nat.card Z = 2)
    (g : G) (hZg : Z ≤ W.map (MulAut.conj g).toMonoidHom) :
    ∃ c ∈ centralizer (Z : Set G),
      W.map (MulAut.conj c).toMonoidHom = W.map (MulAut.conj g).toMonoidHom := by
  have hn {U : Subgroup G} (hUW : U ≤ W) :
      elementaryAbelianMaxJ (T : Subgroup G) ≤ normalizer (U : Set G) :=
    hJ.trans ((centralizer_le hUW).trans (Subgroup.centralizer_le_normalizer _))
  obtain ⟨c,hc,he⟩ := exists_normalizer_conjugator_of_subgroup_fusion Z W (by
    intro a ha
    obtain ⟨n,hnJ,hn⟩ := T.weakly_closed_normalizer_controls_set_fusion
      (elementaryAbelianMaxJ (T : Subgroup G)) (sSup_le fun _ h => h.1)
      (maxJ_weakly_closed_normalizer T)
      (Z : Set G) (Z.map (MulAut.conj a).toMonoidHom : Set G)
      (hn hZW) (hn ha) a rfl
    exact ⟨n,hMW (hNJ hnJ),SetLike.coe_injective hn⟩) g hZg
  exact ⟨c,normalizer_le_centralizer_of_card_two Z hZ hc,he⟩

/-- A normalizing hyperplane of a noncommuting conjugate realizes w=1.
The r bound rules out centralization of that hyperplane. -/
theorem isWOffenderAt_of_normalizing_hyperplane
    {W : Subgroup G} [IsElementaryAbelian 2 W] {T : Sylow 2 G}
    (hT : HypothesisE322 W T) (hw : globalW W T = 1)
    (hr : 1 < globalR W) (g : G) (B : Subgroup G)
    (hBW : B ≤ W.map (MulAut.conj g).toMonoidHom)
    (hBN : B ≤ normalizer (W : Set G))
    (hi : B.relIndex (W.map (MulAut.conj g).toMonoidHom) = 2)
    (hcomm : ⁅W,W.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) :
    IsWOffenderAt W T g := by
  let Wg := W.map (MulAut.conj g).toMonoidHom
  let : IsElementaryAbelian 2 Wg := IsElementaryAbelian.map _
  have hcor : subgroupCorank Wg B = 1 := by
    change Nat.log 2 (B.relIndex Wg) = 1
    rw [hi]
    decide
  have hBC : ¬ B ≤ centralizer (W : Set G) := by
    intro hBC
    have hn : W ≤ normalizer (Wg : Set G) :=
      (le_centralizer_iff.mp hBC).trans
        (centralizer_le_normalizer_of_corank_lt_globalR hBW (by
          rw [hcor,globalR_map_equiv]
          exact hr))
    have hpos : 0 < globalW W T := by rw [hw]; decide
    exact hcomm (commutator_eq_bot_iff_le_centralizer.mpr
      ((lemma_E_3_25 hT hpos g).2.2.mpr hn))
  have hBA : B ≤ offenderNormalizer W g := le_inf hBW hBN
  have hAC : ¬ offenderNormalizer W g ≤ centralizer (W : Set G) :=
    fun h => hBC (hBA.trans h)
  have hlo := globalW_le_corank_of_noncentralizing_normalizes hT g le_rfl hAC
  have hsum := offender_corank_add hBA (show offenderNormalizer W g ≤ Wg from inf_le_left)
  rw [hcor] at hsum
  refine ⟨hcomm,le_antisymm hlo ?_⟩
  rw [hw]
  exact_mod_cast (show subgroupCorank Wg (offenderNormalizer W g) ≤ 1 by omega)

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryTerminal
