module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.SourceAction.Indecomposable

/-!
# Movement by the canonical HS component

Transitivity on the nonzero central quotient forces its full image from the
commutator [U,K]. Indecomposability on the tilded module and the Frattini
nongeneration theorem then give [U,K]=U. Relative normality places U inside
O₂(K). The source natural coordinates remain explicit.

Source: Aschbacher--Smith, 14.3.32(4), printed p.1004.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G}

private theorem sourceComponent_moves (F : InvariantFlag T V 3)
    (hc : NaturalCoordinates F) :
    ∃ h : F.H, (h : G) ∈ sourceComponent F ∧ ∃ x : F.Uhat, F.uhatAction h x ≠ x := by
  classical
  let : Nontrivial F.Uhat := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hc.card_uhat F]; decide)
  obtain ⟨x, hx⟩ := exists_ne (1 : F.Uhat)
  by_contra! hfix
  have hs : (Set.univ : Set F.Uhat) ⊆ {1, x} := by
    intro y _
    by_cases hy : y = 1
    · exact Or.inl hy
    right
    obtain ⟨h, hh, he⟩ := hc.sourceComponent_transitive F x y hx hy
    exact he.symm.trans (hfix h hh x)
  have hb := Set.ncard_le_ncard hs
  rw [Set.ncard_univ, hc.card_uhat F, Set.ncard_pair hx.symm] at hb
  omega

theorem NaturalCoordinates.commutator_eq_self [IsMulCommutative V]
    (F : InvariantFlag T V 3) (hc : NaturalCoordinates F) (htwo : IsPGroup 2 F.U)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) (hne : ¬ IsMulCommutative F.U)
    (hZ : Nat.card (center F.U) = 4) : ⁅F.U, sourceComponent F⁆ = F.U := by
  let K := sourceComponent F
  let D := ⁅F.U, K⁆
  have hDU : D ≤ F.U := le_normalizer_iff_commutator_le_left.mp
    ((sourceComponent_le F).trans (le_normalizer_conjugateSpanBy V F.H))
  let m := F.tildeMap F.U F.U_le_H
  let A := (D.subgroupOf F.U).map m
  have hstable (h : F.H) (hh : (h : G) ∈ K) (x : F.tilde F.U) (hx : x ∈ A) :
      F.localTildeAction F.H le_rfl h x ∈ A := by
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨F.uAction h u, ?_, (F.tildeMap_uAction h u).symm⟩
    change (F.uAction h u : G) ∈ D
    rw [F.uAction_apply]
    exact (mem_normalizer_iff.mp (normalizer_commutator_ge_right F.U K hh) u).mp hu
  have hA (h : F.H) (hh : (h : G) ∈ K) :
      A.map ((F.localTildeAction F.H le_rfl) h).toMonoidHom = A := by
    apply le_antisymm
    · rintro x ⟨y, hy, rfl⟩
      exact hstable h hh y hy
    · intro x hx
      refine ⟨F.localTildeAction F.H le_rfl h⁻¹ x, hstable h⁻¹ (K.inv_mem hh) x hx, ?_⟩
      change (F.localTildeAction F.H le_rfl h) (F.localTildeAction F.H le_rfl h⁻¹ x) = x
      rw [map_inv]
      exact MulEquiv.apply_symm_apply _ _
  have hfull : A.map (F.tildeToUhat (by decide)) = ⊤ := by
    rcases hc.invariant_tilde_image F A hA with hb | ht
    · obtain ⟨h, hh, x, hx⟩ := sourceComponent_moves F hc
      apply (hx ?_).elim
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (center F.U) x
      have hm : F.uAction h u / u ∈ D.subgroupOf F.U := by
        change (F.uAction h u : G) / (u : G) ∈ D
        rw [F.uAction_apply, div_eq_mul_inv]
        change ⁅(h : G), (u : G)⁆ ∈ ⁅F.U, K⁆
        rw [commutator_comm]
        exact commutator_mem_commutator hh u.property
      have he : F.tildeToUhat (by decide) (m (F.uAction h u / u)) = 1 :=
        hb.le (mem_map_of_mem _ (mem_map_of_mem m hm))
      rw [F.tildeToUhat_apply_map, map_div] at he
      rw [F.uhatAction_apply_mk]
      exact div_eq_one.mp he
    · exact ht
  have htop : A = ⊤ := hc.invariant_tilde_surjection_eq_top F htwo hphi hne hZ A hA hfull
  have hgen := congrArg (comap m) htop
  rw [comap_map_eq, comap_top, F.tildeMap_U_ker, ← hphi] at hgen
  have hd := frattini_nongenerating hgen
  exact le_antisymm hDU (subgroupOf_eq_top.mp hd)

theorem NaturalCoordinates.le_component_core [IsMulCommutative V]
    (F : InvariantFlag T V 3) (hc : NaturalCoordinates F) (htwo : IsPGroup 2 F.U)
    (hphi : frattini F.U = (F.Vi 1).subgroupOf F.U) (hne : ¬ IsMulCommutative F.U)
    (hZ : Nat.card (center F.U) = 4) : F.U ≤ (sourceComponent F).pCoreIn 2 := by
  have hm := hc.commutator_eq_self F htwo hphi hne hZ
  have hUK : F.U ≤ sourceComponent F := by
    rw [← hm]
    have hn : F.U ≤ normalizer (sourceComponent F : Set G) :=
      F.U_le_H.trans ((normal_subgroupOf_iff_le_normalizer (sourceComponent_le F)).mp
        (sourceComponent_normal F))
    exact le_normalizer_iff_commutator_le_right.mp hn
  exact le_pCoreIn_of_normalizes htwo hUK
    ((sourceComponent_le F).trans (le_normalizer_conjugateSpanBy V F.H))

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
