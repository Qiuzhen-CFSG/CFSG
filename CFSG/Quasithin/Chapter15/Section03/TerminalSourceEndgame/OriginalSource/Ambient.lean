module

public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource.ActionComparison
public import CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.SourceControls
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Descent
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GoldschmidtCore.Assembly
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.SylowKernelCore

/-!
# Original ambient data for the terminal argument

The source group is the literal join of the two local factors, with F the
original right conjugate of E. The genuine earlier local structure and descent
inputs yield centralizer, residual, quotient and Thompson identities.
Conjugating the source 66 local-core identity and using the common Sylow gives
O₂(G₁) = C_T(F), hence [V,O₂(G₁)] = F. No equality of the two local cores is used.

The genuine 68(2) centrality implication and the original I₀ index-three
recognition remain explicit source inputs; this module does not claim to prove
those earlier implications.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.66–68
and the final proof of 15.3.1, printed pp.1152–1155.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource

open Subgroup Stellmacher AbelianAmalgam
open scoped IsMulCommutative Pointwise

universe u
variable {G : Type u} [Group G] [Finite G]

noncomputable abbrev sourceGroup (T : Sylow 2 G) (M Mc E : Subgroup G) (s : G) : Subgroup G :=
  amalgamGroup (residualY M Mc) (T : Subgroup G) E (otherLine E s)

structure SourceData (T : Sylow 2 G) (M Mc P E : Subgroup G) (s : G) where
  earlier : LocalStructure.EarlierData T M Mc P E
  /-- Genuine 66/67 data, including the original I0 index-three conclusion.
  The existing line-offender and descent owners produce this input. -/
  descent : Descent.Inputs M (residualY M Mc) T (localModule T M) E
  conjugator_mem : s ∈ planeStabilizer T P
  conjugator_outside : s ∉ lineT T E
  terminal : GoldschmidtCore.TerminalConfiguration T M (residualY M Mc)
    (localModule T M) E (otherLine E s) earlier.natural
  /-- The actual 68(2) conclusion remains with its centrality owner. -/
  centrality : twoCoreAmbient (sourceGroup T M Mc E s) ≤
    centralizer (localModule T M : Set G)

omit [Finite G] in
/-- Centralizers transport through the same literal subgroup image. -/
theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm (map_centralizer_le_centralizer_image _ _)
  intro x hx
  refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
  intro a ha
  apply e.injective
  simpa only [map_mul, e.apply_symm_apply] using
    hx (e a) (mem_map_of_mem _ ha)

/-- The manuscript's intrinsic residual and the generic prime residual agree. -/
theorem source_twoResidual_eq (A : Subgroup G) :
    twoResidualSubgroup A = pResidual 2 A := by
  unfold twoResidualSubgroup pResidual
  congr 1
  ext N
  constructor
  · rintro ⟨hN, hn⟩
    exact ⟨hN, IsPGroup.iff_card.mpr (by simpa only [index_eq_card] using hn)⟩
  · rintro ⟨hN, hn⟩
    exact ⟨hN, by simpa only [index_eq_card] using hn.exists_card_eq⟩

/-- Every source residual remains two-perfect in its actual ambient image. -/
theorem source_residual_perfect (A : Subgroup G) :
    IsPPerfect 2 (twoResidualAmbient A) := by
  rw [twoResidualAmbient, source_twoResidual_eq]
  exact isPPerfect_embedded_pResidual 2 A

namespace SourceData

variable {T : Sylow 2 G} {M Mc P E : Subgroup G} {s : G}
  (d : SourceData T M Mc P E s)

include d

local notation "V" => localModule T M
local notation "Y" => residualY M Mc
local notation "F₀" => otherLine E s
local notation "D" => lineT (T : Subgroup G) E
local notation "H" => sourceGroup T M Mc E s
local notation "A₁" => firstAmalgamGroup Y (T : Subgroup G) E F₀
local notation "A₂" => secondAmalgamGroup (T : Subgroup G) E

theorem sylow_le : (T : Subgroup G) ≤ M := d.earlier.ordering.1.2

omit d [Finite G] in
theorem residual_le : Y ≤ M := Chapter14.SourcePreliminaries.sourceResidual_le M Mc

theorem sylow_normalizes_residual : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
  d.sylow_le.trans ((normal_subgroupOf_iff_le_normalizer (residual_le (M := M) (Mc := Mc))).mp
    (residualY_normal M Mc))

theorem conjugate_residual : lineY Y F₀ = otherLine (lineY Y E) s :=
  GoldschmidtCore.lineY_otherLine Y E s (d.sylow_normalizes_residual d.conjugator_mem.1)

theorem vector_le_group : V ≤ H :=
  d.terminal.module_le_core.trans (map_subtype_le _)

omit d [Finite G] in
theorem first_le_group : A₁ ≤ H := le_sup_left

omit d [Finite G] in
theorem second_le_group : A₂ ≤ H := le_sup_right

omit d [Finite G] in
theorem common_le_group : D ≤ H := le_sup_right.trans (first_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))

omit d [Finite G] in
theorem first_residual_le_group : lineY Y F₀ ≤ H := le_sup_left.trans (first_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))

omit d [Finite G] in
theorem second_residual_le_group : lineX E ≤ H := le_sup_left.trans (second_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))

theorem singular_le_group : F₀ ≤ H := d.terminal.line_le.trans d.vector_le_group

noncomputable def sourceSylow : Sylow 2 H := Classical.choose d.terminal.sylow

theorem sourceSylow_map :
    (d.sourceSylow : Subgroup H).map (H).subtype = D :=
  Classical.choose_spec d.terminal.sylow

theorem sourceSylow_eq : (d.sourceSylow : Subgroup H) = (D).subgroupOf H := by
  apply map_injective (H).subtype_injective
  rw [d.sourceSylow_map, map_subgroupOf_eq_of_le (common_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))]

theorem core_le_common_of_le {A : Subgroup G} (hDA : D ≤ A) (hAH : A ≤ H) :
    A.pCoreIn 2 ≤ D := by
  have huA : (d.sourceSylow : Subgroup H) ≤ A.subgroupOf H := by
    rw [d.sourceSylow_eq]
    exact comap_mono hDA
  have hc := pCoreIn_le_sylow (A.subgroupOf H) (d.sourceSylow.subtype huA)
  rw [Sylow.coe_subtype, map_subgroupOf_eq_of_le huA] at hc
  have hm := map_mono (f := (H).subtype) hc
  rwa [map_pCoreIn_of_injective 2 _ _ (H).subtype_injective,
    map_subgroupOf_eq_of_le hAH, d.sourceSylow_map] at hm


theorem centralizer_eq : centralizer (V : Set G) =
    (T : Subgroup G) ⊓ centralizer (V : Set G) := by
  let _ := standard_elementary d.earlier.natural
  exact (Descent.source_descent d.descent).1

theorem centralizer_le_common : centralizer (V : Set G) ≤ D := by
  refine le_inf (d.centralizer_eq.le.trans inf_le_left) ?_
  exact (centralizer_le d.earlier.line_le).trans (Subgroup.centralizer_le_normalizer _)

theorem ambient_product : M = Y ⊔ (T : Subgroup G) := by
  let _ := standard_elementary d.earlier.natural
  apply SetLike.coe_injective
  exact (Descent.source_descent d.descent).2.1.trans
    (coe_mul_of_right_le_normalizer_left _ _ d.sylow_normalizes_residual).symm

theorem seed_le_original : centralInvolutions T ≤ E := by
  obtain ⟨_, _, _, _, hz, _⟩ := Orthogonal.line_sylow_geometry_of_source
    d.earlier.natural T P E d.sylow_le d.earlier.plane_le d.earlier.plane_card
    d.earlier.plane_definite d.earlier.line_le d.earlier.line_card
    d.earlier.line_singular d.earlier.central_fixed d.earlier.selected d.earlier.selected_map
  exact hz

theorem original_plane_commutator : ⁅V, (T : Subgroup G) ⊓ centralizer (E : Set G)⁆ = E := by
  obtain ⟨_, _, _, _, _, hc⟩ := Orthogonal.line_sylow_geometry_of_source
    d.earlier.natural T P E d.sylow_le d.earlier.plane_le d.earlier.plane_card
    d.earlier.plane_definite d.earlier.line_le d.earlier.line_card
    d.earlier.line_singular d.earlier.central_fixed d.earlier.selected d.earlier.selected_map
  exact hc

theorem vector_map_conjugator : (V).map (MulAut.conj s⁻¹).toMonoidHom = V :=
  mem_normalizer_iff_map_conj_eq.mp
    (d.earlier.natural.normalizes (M.inv_mem (d.sylow_le d.conjugator_mem.1)))

theorem sylow_map_conjugator : (T : Subgroup G).map (MulAut.conj s⁻¹).toMonoidHom = T :=
  mem_normalizer_iff_map_conj_eq.mp
    ((T : Subgroup G).le_normalizer ((T : Subgroup G).inv_mem d.conjugator_mem.1))

theorem common_map_conjugator : (D).map (MulAut.conj s⁻¹).toMonoidHom = D := by
  rw [lineT, map_inf _ _ _ (MulAut.conj s⁻¹).injective, d.sylow_map_conjugator,
    map_equiv_normalizer_eq]
  exact d.terminal.lineT_eq

theorem conjugate_plane_commutator :
    ⁅V, (T : Subgroup G) ⊓ centralizer (F₀ : Set G)⁆ = F₀ := by
  have h := congrArg (Subgroup.map (MulAut.conj s⁻¹).toMonoidHom) d.original_plane_commutator
  rw [map_commutator, d.vector_map_conjugator,
    map_inf _ _ _ (MulAut.conj s⁻¹).injective, d.sylow_map_conjugator,
    centralizer_map_equiv] at h
  exact h

theorem first_core_centralizer : (A₁).pCoreIn 2 = A₁ ⊓ centralizer (F₀ : Set G) := by
  obtain ⟨_, _, _, hcore, _⟩ := Orthogonal.residualY_lineNormalizer_consequences
    d.earlier.natural Mc T E d.sylow_le d.earlier.line_le d.earlier.line_card
    d.earlier.line_singular d.earlier.residual_image d.earlier.residual_core_module
    d.earlier.selected d.earlier.selected_map
  have hY : (lineY Y E).map (MulAut.conj s⁻¹).toMonoidHom = lineY Y F₀ :=
    d.conjugate_residual.symm
  have h := congrArg (Subgroup.map (MulAut.conj s⁻¹).toMonoidHom) hcore
  change ((lineY Y E ⊔ D : Subgroup G).pCoreIn 2).map
      (MulAut.conj s⁻¹).toMonoidHom = _ at h
  rw [map_pCoreIn_of_injective 2 _ _ (MulAut.conj s⁻¹).injective,
    Subgroup.map_sup, d.common_map_conjugator, hY,
    map_inf _ _ _ (MulAut.conj s⁻¹).injective,
    Subgroup.map_sup, d.common_map_conjugator, hY,
    centralizer_map_equiv] at h
  exact h

/-- The first local core is the original Sylow centralizer of F, not a
claimed equality between the two distinct local cores. -/
theorem first_core_eq_sylow_centralizer :
    (A₁).pCoreIn 2 = (T : Subgroup G) ⊓ centralizer (F₀ : Set G) := by
  apply le_antisymm
  · exact le_inf ((d.core_le_common_of_le le_sup_right (first_le_group (T := T) (M := M) (Mc := Mc) (E := E) (s := s))).trans inf_le_left)
      (d.first_core_centralizer.le.trans inf_le_right)
  · rw [d.first_core_centralizer]
    refine le_inf ?_ inf_le_right
    have hD : (T : Subgroup G) ⊓ centralizer (F₀ : Set G) ≤ D := by
      rw [← d.terminal.lineT_eq]
      exact inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
    exact hD.trans le_sup_right

theorem local_vector_commutator : ⁅V, (A₁).pCoreIn 2⁆ = F₀ := by
  rw [d.first_core_eq_sylow_centralizer]
  exact d.conjugate_plane_commutator

theorem first_residual_core_centralizes :
    (lineY Y F₀).pCoreIn 2 ≤ centralizer (V : Set G) := by
  have hk := Orthogonal.residualY_lineY_action_ker_eq_twoCore
    d.earlier.natural Mc F₀ d.terminal.line_le
    d.earlier.residual_image d.earlier.residual_core_module
  rintro x ⟨y, hy, rfl⟩
  have hyk : y ∈ (d.earlier.natural.action.comp
      (inclusion ((lineY_le Y F₀).trans (inf_le_left.trans (residual_le (M := M) (Mc := Mc)))))).ker := hk.symm ▸ hy
  have hmk : inclusion ((lineY_le Y F₀).trans (inf_le_left.trans (residual_le (M := M) (Mc := Mc)))) y ∈
      d.earlier.natural.action.ker := hyk
  rw [GoldschmidtCore.LocalRelations.action_ker] at hmk
  exact hmk

theorem first_vector_commutator : V = ⁅V, lineY Y F₀⁆ :=
  Orthogonal.lineY_commutator d.earlier.natural Y F₀ (residual_le (M := M) (Mc := Mc))
    d.terminal.line_le d.terminal.line_card d.terminal.line_singular d.earlier.residual_image

theorem original_vector_commutator : V = ⁅V, lineY Y E⁆ :=
  Orthogonal.lineY_commutator d.earlier.natural Y E (residual_le (M := M) (Mc := Mc))
    d.earlier.line_le d.earlier.line_card d.earlier.line_singular d.earlier.residual_image

theorem first_normalized : A₁ ≤ normalizer (lineY Y F₀ : Set G) := by
  refine sup_le (lineY Y F₀).le_normalizer ?_
  rw [← d.terminal.lineT_eq]
  exact lineT_le_normalizer_lineY Y T F₀ d.sylow_normalizes_residual

omit d in
theorem second_normalized : A₂ ≤ normalizer (lineX E : Set G) :=
  (sup_le ((lineX_le_centralizer E).trans (Subgroup.centralizer_le_normalizer _))
    inf_le_right).trans (lineNormalizer_le_normalizer_lineX E)

omit d in
theorem first_perfect : IsPPerfect 2 (lineY Y F₀) :=
  source_residual_perfect (Y ⊓ lineNormalizer F₀)

omit d in
theorem second_perfect : IsPPerfect 2 (lineX E) :=
  source_residual_perfect (centralizer (E : Set G))

/-- The original conjugation, with the manuscript's inverse convention. -/
noncomputable def conjugateResidualEquiv : lineY Y F₀ ≃* lineY Y E :=
  (MulEquiv.subgroupCongr d.conjugate_residual).trans
    ((MulAut.conj s⁻¹).subgroupMap (lineY Y E)).symm

theorem second_odd_quotient :
    Nonempty ((lineX E ⧸ pCore 2 (lineX E)) ≃* Multiplicative (ZMod 3)) := by
  let _ := standard_elementary d.earlier.natural
  obtain ⟨_, _, _, _, _, h, _⟩ := Descent.source_descent d.descent
  exact h

theorem first_odd_quotient :
    Nonempty ((lineY Y F₀ ⧸ pCore 2 (lineY Y F₀)) ≃* Multiplicative (ZMod 3)) := by
  let _ := standard_elementary d.earlier.natural
  obtain ⟨_, _, _, _, _, _, ⟨e⟩, _⟩ := Descent.source_descent d.descent
  let c := d.conjugateResidualEquiv
  exact ⟨(QuotientGroup.congr _ _ c (pCore_map_iso 2 c)).trans e⟩

theorem second_thompson_commutator :
    lineX E = ⁅lineX E, elementaryAbelianMaxJ D⁆ := by
  let _ := standard_elementary d.earlier.natural
  obtain ⟨_, _, _, _, _, _, _, _, _, h⟩ := Descent.source_descent d.descent
  rw [d.descent.thompson_eq]
  exact h

theorem thompson_centralizer :
    elementaryAbelianMaxJ D = elementaryAbelianMaxJ (centralizer (V : Set G)) := by
  rw [d.descent.thompson_eq, ← d.centralizer_eq]

theorem thompson_normalized : A₁ ≤ normalizer (elementaryAbelianMaxJ D : Set G) :=
  (normal_subgroupOf_iff_le_normalizer
    ((show elementaryAbelianMaxJ D ≤ D from sSup_le fun _ hA => hA.1).trans le_sup_right)).mp d.terminal.thompson_normal

theorem vector_card : Nat.card V = 16 := by
  rw [Nat.card_congr d.earlier.natural.coordinates.toEquiv]
  simp [OrthogonalFourBinary.Space, OrthogonalFourBinary.Plane,
    OrthogonalFourBinary.F, Nat.card_eq_fintype_card]

theorem residual_escape : ¬ lineX E ≤ M := by
  let _ := standard_elementary d.earlier.natural
  exact SourceControls.residual_escape_of_earlier_data d.earlier

end SourceData
end CFSG.Quasithin.Chapter15.Section03.TerminalSourceEndgame.OriginalSource
