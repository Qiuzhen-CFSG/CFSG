module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.PreDescentSource.Geometry
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.SourceClassification.Application
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.ActionComparison
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Source 15.3.67 from the earlier local structure

Construct the offender input on the original G_E from the earlier local
structure, then apply the adequate classifier to the original I_0. Its exact
index-three conclusion supplies the existing descent theorem. The original
Z_S normalizer bound also excludes three from C_M(V). Residual/Sylow coverage
of the given orthogonal action supplies M=Y C_M(V) T before descent.

The only earlier source premises are LocalStructure.EarlierData, simple QTKE,
15.3.49(5) for the actual Z_S, and the full adequate B.5 implication. Their
producers remain the original preliminaries/fusion/line-selection owners and
qt-b05-general-classification; this is not the completed Theorem 15.3.1.

The action comparison is reused at this higher assembly boundary. This leaf
must be reexported after OriginalSource, not imported into its lower files.

Source: Aschbacher--Smith, proof of 15.3.67, printed pp.1153--1154.
-/

@[expose] public section

open Subgroup Stellmacher OrthogonalFourBinary
open scoped Pointwise IsMulCommutative

namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.PreDescentSource

open LocalStructure GoldschmidtCore.LocalRelations
open TerminalSourceEndgame

universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc P E : Subgroup G}

omit [Finite G] in
private theorem module_ne_bot (s : EarlierData T M Mc P E) : localModule T M ≠ ⊥ := by
  intro h
  have hE : E = ⊥ := bot_unique (s.line_le.trans h.le)
  have hc := s.line_card
  rw [hE, card_bot] at hc
  omega

omit [Finite G] in
private theorem module_normalizer_le (s : EarlierData T M Mc P E) :
    normalizer (localModule T M : Set G) ≤ M := by
  let := OriginalSource.standard_elementary s.natural
  have he : M = normalizer (localModule T M : Set G) :=
    s.ordering.1.1.eq_of_le
      ⟨localModule T M, module_ne_bot s,
        IsElementaryAbelian.isPGroup 2 _, rfl⟩ s.natural.normalizes
  exact he.symm.le

private theorem line_sqtk {κ : GroupClass.{u}}
    (s : EarlierData T M Mc P E) (hG : IsSimpleQTKE κ G) :
    IsSQTK κ (lineNormalizer E) := by
  let := OriginalSource.standard_elementary s.natural
  let : IsElementaryAbelian 2 E := IsElementaryAbelian.of_le s.line_le
  have hE : E ≠ ⊥ := by
    intro h
    have hc := s.line_card
    rw [h, card_bot] at hc
    omega
  exact hG.twoLocal_sqtk ⟨E, hE, IsElementaryAbelian.isPGroup 2 E, rfl⟩

private theorem earlier_product (s : EarlierData T M Mc P E) :
    (M : Set G) = (residualY M Mc : Set G) *
      (M ⊓ centralizer (localModule T M : Set G) : Set G) * (T : Set G) := by
  let d := s.natural
  let S := T.subtype s.ordering.1.2
  let Sbar := S.mapSurjective d.onto
  apply Set.Subset.antisymm
  · intro m hm
    let mM : M := ⟨m, hm⟩
    have hmem : d.action mM ∈ pResidual 2 OrthogonalFourBinary.TerminalLines.IsometryGroup ⊔
        (Sbar : Subgroup OrthogonalFourBinary.TerminalLines.IsometryGroup) := by
      rw [pResidual_sup_sylow_eq_top Sbar]
      trivial
    rw [← SetLike.mem_coe, normal_mul] at hmem
    obtain ⟨r, hr, t, ht, hrt⟩ := hmem
    rw [← s.residual_image] at hr
    obtain ⟨y, hy, hyr⟩ := hr
    change t ∈ (S : Subgroup M).map d.action at ht
    obtain ⟨v, hv, hvt⟩ := ht
    let c : M := y⁻¹ * mM * v⁻¹
    have hc : c ∈ d.action.ker := by
      change d.action c = 1
      dsimp [c]
      rw [map_mul, map_mul, map_inv, map_inv, hyr, hvt, ← hrt]
      group
    rw [action_ker d] at hc
    refine ⟨(y : G) * (c : G), ⟨y, hy, c, ⟨c.property, hc⟩, rfl⟩,
      v, ?_, ?_⟩
    · exact hv
    · change (y : G) * ((y : G)⁻¹ * m * (v : G)⁻¹) * v = m
      group
  · rintro m ⟨yc, ⟨y, hy, c, hc, rfl⟩, t, ht, rfl⟩
    exact M.mul_mem
      (M.mul_mem (Chapter14.SourcePreliminaries.sourceResidual_le M Mc hy) hc.1)
      (s.ordering.1.2 ht)

omit [Finite G] in
private theorem centralizer_three_prime
    (hZ : Nat.Coprime 3 (Nat.card (normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G)))) :
    ¬ 3 ∣ Nat.card (M ⊓ centralizer (localModule T M : Set G) : Subgroup G) := by
  have hle : M ⊓ centralizer (localModule T M : Set G) ≤ normalizer
      (fixedPlane (localModule T M) (planeStabilizer T P) : Set G) :=
    inf_le_right.trans ((centralizer_le inf_le_left).trans (Subgroup.centralizer_le_normalizer _))
  intro hd
  exact Nat.prime_three.coprime_iff_not_dvd.mp hZ
    (hd.trans (card_dvd_of_le hle))

variable {κ : GroupClass.{u}}
variable (s : EarlierData T M Mc P E) (hG : IsSimpleQTKE κ G)
variable (hZ : Nat.Coprime 3 (Nat.card (normalizer
  (fixedPlane (localModule T M) (planeStabilizer T P) : Set G))))
variable (classify : ChapterB.SourceInduction.AdequateClassificationInput.{u,u} κ)

include s hG hZ classify

/-- The literal original I_0 has index-three intersection with M_E. All
temporary action, marker and recognized-model inputs are constructed. -/
theorem source_I0_index :
    (lineI0 T (localModule T M) E ⊓ lineM M E).relIndex
      (lineI0 T (localModule T M) E) = 3 := by
  let := OriginalSource.standard_elementary s.natural
  let r := initialStructure s
  let o := originalData s
  have hJ : elementaryAbelianMaxJ (lineT T E) ≤ centralizer (E : Set G) := by
    rw [r.thompson]
    exact (sSup_le fun _ hA => hA.1).trans
      (inf_le_right.trans (centralizer_le s.line_le))
  have hI : ¬ lineI E ≤ lineM M E :=
    fun h => r.thompson_escape (h.trans inf_le_left)
  have h := Offenders.SourceClassification.Application.canonical_original_conclusions_of_classification
    o hJ (module_normalizer_le s) hI r.thompson_product
    r.thompson_normalizer_control (line_sqtk s hG)
    (fixedPlane (localModule T M) (planeStabilizer T P)) inf_le_left hZ classify
  exact h.2.2.2.2.2

/-- Construct the existing descent input on the original groups, including
its actual I_0 index, without either terminal product or centralizer equality. -/
noncomputable def descentInputs : Descent.Inputs M (residualY M Mc) T (localModule T M) E := Classical.choice <| by
  let := OriginalSource.standard_elementary s.natural
  let r := initialStructure s
  obtain ⟨_, _, hQC, hcore, hprod⟩ := Orthogonal.residualY_lineNormalizer_consequences
    s.natural Mc T E s.ordering.1.2 s.line_le s.line_card s.line_singular
    s.residual_image s.residual_core_module s.selected s.selected_map
  have hIN : lineNormalizer E ≤ normalizer (lineI E : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (lineI_le_lineNormalizer E)).mp
      (lineI_normal_in_lineNormalizer E)
  have hcomm : (lineM M E : Set G) * (lineI E : Set G) =
      (lineI E : Set G) * (lineM M E : Set G) :=
    set_mul_normalizer_comm _ _ (inf_le_right.trans hIN)
  exact ⟨{
    line_le := s.line_le
    escapes := s.escape
    normalizer_V_le_M := module_normalizer_le s
    natural_action := (Classical.choice (OriginalSource.coordinates_from_standard s.natural
      (OriginalSource.definite_of_standard s.natural s.plane_le s.plane_card
        s.plane_definite))).action
    maximal_two_local := s.ordering.1.1
    characteristic_two := hG.evenCharacteristic T M s.ordering.1.1 s.ordering.1.2
    centralizer_three_prime := centralizer_three_prime hZ
    T_le_M := s.ordering.1.2
    Y_le_M := Chapter14.SourcePreliminaries.sourceResidual_le M Mc
    Y_normal_in_M := residualY_normal M Mc
    earlier_product := earlier_product s
    sylow := r.line_sylow
    sylow_map := r.line_sylow_map
    thompson_eq := r.thompson
    core_centralizes_line := hQC
    geometric_product := hprod
    product_with_I := r.thompson_product.trans hcomm.symm
    I0_index := source_I0_index s hG hZ classify
    local_core := hcore
    Y_normal := r.residual_normal
    marked := r.quotient }⟩

/-- Source 15.3.67 on the original groups. Clause (2) retains the actual
Sylow inclusion and Baumann subgroup; descent supplies (1), (3) and (4). -/
theorem source_lemma_15_3_67 :
    (∃ S : Sylow 2 (lineNormalizer E),
      (S : Subgroup (lineNormalizer E)).map (lineNormalizer E).subtype = lineT T E) ∧
    lineB T E ≤ (T : Subgroup G) ⊓ centralizer (localModule T M : Set G) ∧
    (lineB T E).characteristicNormalizerClosure ≤ M ∧
    centralizer (localModule T M : Set G) =
      (T : Subgroup G) ⊓ centralizer (localModule T M : Set G) ∧
    (M : Set G) = (residualY M Mc : Set G) * (T : Set G) ∧
    (lineNormalizer E : Set G) =
      (lineY (residualY M Mc) E : Set G) * (lineX E : Set G) * (lineT T E : Set G) ∧
    ((lineY (residualY M Mc) E).subgroupOf (lineNormalizer E)).Normal ∧
    ((lineX E).subgroupOf (lineNormalizer E)).Normal ∧
    Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)) ∧
    Nonempty ((lineY (residualY M Mc) E ⧸ pCore 2 (lineY (residualY M Mc) E)) ≃*
      Multiplicative (ZMod 3)) ∧
    ¬ lineX E ≤ M ∧
    Nonempty ((lineNormalizer E ⧸ pCore 2 (lineNormalizer E)) ≃*
      Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) ∧
    lineX E = ⁅lineX E,
      elementaryAbelianMaxJ ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G))⁆ := by
  let := OriginalSource.standard_elementary s.natural
  let r := initialStructure s
  exact ⟨⟨r.line_sylow, r.line_sylow_map⟩, r.baumann_le, r.characteristic_control,
    Descent.source_descent (descentInputs s hG hZ classify)⟩

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.PreDescentSource
