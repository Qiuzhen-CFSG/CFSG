module

public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.A8Reduction.Algebra
public import CFSG.Quasithin.Chapter2.Section05.A6ShadowRankOne.A8Reduction.Setup

/-!
# Relative normality and placement of the exceptional extension

The solvable-residual equation puts K inside Ki. The two-core equation
makes SC normal in H, and conjugation by x carries its normality in S to
SCˣ. Their trivial intersection therefore makes them commute. This places
SCˣ inside Ki C_S(i), without assuming either Ki or SC is ambient normal.

The A₆ obstruction proves Ki normal in C_G(i). The exact involution-
centralizer consequence of 1.1.3(2) then excludes H₀ from each eligible
conjugate of M, and Sylow conjugacy places its Sylow subgroup in Tᵍ.

Source: Aschbacher–Smith, Lemma 2.5.26, printed pp.568–569, combined
1 March 2004 manuscript. The 1.1.3(2) consequence is an explicit earlier
source input; the symmetric-group extension is not used in these results.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction.LocalData
variable {G : Type*} [Group G] (d : LocalData G)

/-- SC is a subgroup of S by its centralizer definition. -/
theorem core_le_s : d.SC ≤ d.S := d.centralizer_K ▸ inf_le_left

/-- The Sylow subgroup lies in H = KS. -/
theorem s_le_h : d.S ≤ d.H := d.generated ▸ le_sup_right

/-- The actual solvable-residual equation implies K ≤ Ki. -/
theorem K_le_Ki : d.K ≤ d.Ki := by
  rw [d.residual]
  exact (map_subtype_le _).trans inf_le_left

/-- The two-core is normal relative to H. -/
theorem core_normalizer : d.H ≤ normalizer (d.SC : Set G) := by
  rw [d.core]
  exact d.H.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image d.H (pCore 2 d.H))

/-- SC is a two-group because it is the two-core of H. -/
theorem core_isPGroup : IsPGroup 2 d.SC := d.core ▸ isPGroup_pCoreIn 2 d.H

/-- Conjugation by the supplied normalizer element keeps SC inside S. -/
theorem conjugate_core_le_s : d.SC.map (MulAut.conj d.x).toMonoidHom ≤ d.S := by
  have hm := map_mono (f := (MulAut.conj d.x).toMonoidHom) d.core_le_s
  exact hm.trans_eq (mem_normalizer_iff_map_conj_eq.mp d.x_normalizes)

/-- Two disjoint relatively normal subgroups of S commute. -/
theorem conjugate_core_centralizes : d.SC.map (MulAut.conj d.x).toMonoidHom ≤
    centralizer (d.SC : Set G) := by
  let a := MulAut.conj d.x
  let D := d.SC.map a.toMonoidHom
  have hs : d.S ≤ normalizer (d.SC : Set G) := d.s_le_h.trans d.core_normalizer
  have hs' : d.S ≤ normalizer (D : Set G) := by
    have hh := map_mono (f := a.toMonoidHom) hs
    rw [map_equiv_normalizer_eq] at hh
    have he : d.S.map a.toMonoidHom = d.S :=
      mem_normalizer_iff_map_conj_eq.mp d.x_normalizes
    exact he ▸ hh
  have hc : ⁅D, d.SC⁆ ≤ d.SC ⊓ D := le_inf
    (le_normalizer_iff_commutator_le_right.mp (d.conjugate_core_le_s.trans hs))
    (le_normalizer_iff_commutator_le_left.mp (d.core_le_s.trans hs'))
  exact commutator_eq_bot_iff_le_centralizer.mp
    (bot_unique (hc.trans d.disjoint_conjugate.eq_bot.le))

/-- The conjugate of SC lies in Ki C_S(i). -/
theorem conjugate_core_le_extension : d.SC.map (MulAut.conj d.x).toMonoidHom ≤
    d.extension := by
  intro a ha
  apply (le_sup_right : d.S ⊓ centralizer {d.i} ≤ d.extension)
  exact ⟨d.conjugate_core_le_s ha,
    mem_centralizer_singleton_iff.mpr (d.conjugate_core_centralizes ha d.i d.i_mem).symm⟩

/-- The marked involution t belongs to the extension. -/
theorem t_mem_extension : d.t ∈ d.extension := by
  apply (le_sup_right : d.S ⊓ centralizer {d.i} ≤ d.extension)
  exact ⟨d.core_le_s d.t_mem,
    mem_centralizer_singleton_iff.mpr (d.t_central d.i (d.core_le_s d.i_mem)).symm⟩

/-- The marked generators of H₀ already lie in Ki C_S(i). -/
theorem smallExtension_le_extension : d.smallExtension ≤ d.extension := by
  apply sup_le
  · apply sup_le le_sup_left
    apply zpowers_le.mpr
    exact (le_sup_right : d.S ⊓ centralizer {d.i} ≤ d.extension)
      ⟨d.core_le_s d.i_mem, mem_centralizer_singleton_iff.mpr rfl⟩
  · exact zpowers_le.mpr d.t_mem_extension

/-- The remaining centralizer containment identifies the two extensions. -/
theorem smallExtension_eq_extension_of_centralizer_le
    (h : d.S ⊓ centralizer {d.i} ≤ d.smallExtension) :
    d.smallExtension = d.extension :=
  le_antisymm d.smallExtension_le_extension (sup_le (le_sup_left.trans le_sup_left) h)

/-- Centrality in S restricts to centrality in SC. -/
theorem t_mem_center_core : (⟨d.t, d.t_mem⟩ : d.SC) ∈ center d.SC := by
  rw [mem_center_iff]
  intro a
  exact Subtype.ext (d.t_central a (d.core_le_s a.property))

variable [Finite G]

/-- Ki is normal in C_G(i), using its contained A₆ subgroup. -/
theorem Ki_normalizer (hG : IsQuasithin G) :
    centralizer ({d.i} : Set G) ≤ normalizer (d.Ki : Set G) :=
  centralizer_normalizes_component_containing_a6 hG d.K d.Ki d.i d.modelK
    d.K_le_Ki d.Ki_le_centralizer d.component

/-- The source centralizer condition excludes H₀ ≤ M. -/
theorem smallExtension_not_le (hG : IsQuasithin G) (M : Subgroup G)
    (h113 : ∀ j : G, j ∈ M → orderOf j = 2 →
      M ⊓ centralizer ({j} : Set G) ∈ CFSG.Quasithin.Chapter1.He G) :
    ¬ d.smallExtension ≤ M := by
  have hi : d.i ∈ d.smallExtension :=
    (show d.Ki ⊔ zpowers d.i ≤ d.smallExtension from le_sup_left)
      ((show zpowers d.i ≤ d.Ki ⊔ zpowers d.i from le_sup_right) (mem_zpowers d.i))
  apply overgroup_not_le_of_component_centralizer d.Ki d.smallExtension M d.i
    hi d.i_order
    (le_sup_left.trans le_sup_left) d.Ki_le_centralizer d.component
    (d.Ki_normalizer hG) h113

set_option backward.isDefEq.respectTransparency false in
/-- Place any Sylow subgroup of H₀ in a conjugate of the fixed ambient Sylow. -/
theorem smallExtension_sylow_placement (T : Sylow 2 G)
    (U : Sylow 2 d.smallExtension) :
    ∃ g : G, (U : Subgroup d.smallExtension).map d.smallExtension.subtype ≤
      (T : Subgroup G).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨Q, hQ⟩ := (U.isPGroup'.map d.smallExtension.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T Q
  refine ⟨g, ?_⟩
  have he : (Q : Subgroup G) = (T : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  exact hQ.trans_eq he

/-- The same conjugator gives the required Sylow placement and outside-M condition. -/
theorem smallExtension_sylow_placement_outside (hG : IsQuasithin G)
    (T : Sylow 2 G) (M : Subgroup G) (U : Sylow 2 d.smallExtension)
    (h113 : ∀ (g j : G), j ∈ M.map (MulAut.conj g).toMonoidHom → orderOf j = 2 →
      M.map (MulAut.conj g).toMonoidHom ⊓ centralizer ({j} : Set G) ∈
        CFSG.Quasithin.Chapter1.He G) :
    ∃ g : G, (U : Subgroup d.smallExtension).map d.smallExtension.subtype ≤
      (T : Subgroup G).map (MulAut.conj g).toMonoidHom ∧
      ¬ d.smallExtension ≤ M.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := d.smallExtension_sylow_placement T U
  exact ⟨g, hg, d.smallExtension_not_le hG _ (h113 g)⟩

end CFSG.Quasithin.Chapter2.A6ShadowRankOne.A8Reduction.LocalData
