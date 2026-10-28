module
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSecondarySourceGeometry

/-!
# The source cubic in the corrected secondary construction

In degree two the natural and doubled-dual modules construct a cubic in
O₂,Z(K), faithful on the original root and moving Q. If R₂≤K, its commutator
with this cubic lies in O₂(K)=Q≤R₂, proving radical normalization. This
derives normalization from containment, rather than assuming it for a
selected torus. The marked parabolics then supply the actual secondary
quotient, strict component containment and nontrivial quotient action.

The constructor retains the original component, its full quotient action,
and explicit torus containment in K. It is conditional on the earlier
component/core/normalizer geometry and on control of R₂ outside K. Those
premises, the original MS witness and the general-degree torus remain
with `qt-d-1222-rankone-uniqueness-nonblock`. It does not assert the full
source theorem or reconstruct the legacy radical-movement field.

Source: Aschbacher--Smith, original 4.3.10--15, printed pp.617--618.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
open Matrix.PSL3.LinearThree
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {c : SourceConfiguration T L}

/-- A core-central actor normalizes the whole radical once its possible
part outside K has been eliminated and the source core identity is known. -/
theorem coreCenter_normalizes_radical_of_le_original
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c) (hRK : R₂ c ≤ K c)
    {X : Subgroup G} (hX : X ≤ (K c).coreCenterIn 2) :
    X ≤ normalizer (R₂ c : Set G) := by
  have hQ : (K c).pCoreIn 2 ≤ Q c :=
    (pCoreIn_mono_of_normalizes le_sup_left
      (sup_le (K c).le_normalizer (inf_le_right.trans c.normalizer_component.le))).trans_eq hcore
  apply le_normalizer_iff_commutator_le_left.mpr
  rw [commutator_comm]
  apply commutator_le.mpr
  intro x hx r hr
  exact (hQ.trans (core_le_radical c))
    (((mem_coreCenterIn_iff 2 (K c) x).mp (hX hx)).2 r (hRK hr))

/-- The actual source cubic supplies the torus in a corrected source witness.
The explicit earlier geometric premises are retained with this source owner. -/
theorem MSData.exists_secondarySourceData_two_of_marked_parabolic
    (d : MSData c 2) (D : Chapter12.Section02.ChosenModule T L V)
    (hL : (L.subgroupOf (K c)).map (linearThreeActor d.model) = lineLocalSL d.field.Carrier)
    (hSL : ((S c ⊓ L).subgroupOf (K c)).map (linearThreeActor d.model) = unipotentSL d.field.Carrier)
    (B : Subgroup (rootNormalizer c)) (hB : B.IsCComponent) (hBn : B.Normal)
    (hBq : IsQuasisimple (B ⧸ pCore 2 B))
    (hsec : secondary c ≤ B.map (rootNormalizer c).subtype)
    (hcore : (K c ⊔ S c).pCoreIn 2 = Q c)
    (hRK : R₂ c ≤ K c)
    (henlarged : (B.map (rootNormalizer c).subtype ⊔ (T : Subgroup G)).pCoreIn 2 ≤ R₂ c)
    (hnorm : normalizer (R₂ c : Set G) ≤ c.H ⊓ normalizer (secondary c : Set G))
    (henlarges : secondary c < (B.map (rootNormalizer c).subtype).pCoreIn 2 ⊔ secondary c) :
    ∃ s : SecondarySourceData c 2, s.component = B ∧
      s.torus ≤ (K c).coreCenterIn 2 ∧ s.torus ≤ K c ∧
      Q c ⊓ Subgroup.centralizer (s.torus : Set G) = ⊥ ∧
      Q c ⊔ ⁅R₂ c, s.torus⁆ ≠ R₂ c := by
  obtain ⟨m⟩ := d.rootCoordinates_of_marked_parabolic hL hSL
  obtain ⟨_,hmodel,hstrict,haction⟩ :=
    d.secondary_structure_of_marked_parabolic (by decide) D hL hSL B hB hBn hsec
      henlarged (hnorm.trans inf_le_right)
  obtain ⟨X,hcard,hX,hr,hfixed,hfaith,_,_,hsecX,hQ,_⟩ := d.exists_source_cubic_root D
  let s : SecondarySourceData c 2 := {
    component := B
    torus := X
    isComponent := hB
    normal := hBn
    quasisimple := hBq
    secondary_le := hsec
    secondary_lt := hstrict
    secondary_model := hmodel
    torus_le := hr
    torus_cyclic := isCyclic_of_prime_card hcard
    torus_card := by simpa using hcard
    torus_faithful := hfaith
    torus_secondary := hsecX
    torus_normalizes_radical := coreCenter_normalizes_radical_of_le_original hcore hRK hX
    core_eq := hcore
    core_moved := hQ
    radical_le := radical_le_root_normalizer D
    radical_normalizer := hnorm
    enlarged_core_le := henlarged
    core_enlarges := henlarges
    radical_action := haction }
  exact ⟨s,rfl,hX,hX.trans (coreCenterIn_le 2 _),hfixed,
    m.coreCenter_not_move_radical (by decide) D X hX⟩

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Nonblock
