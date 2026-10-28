module

public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellSetup
public import CFSG.Quasithin.ChapterC.Section01.RankOne.GlaubermanNiles.BaumannFixed.CampbellContainment
public import Stellmacher.OmegaOneCenterMap

/-!
# Elementary transport facts for Campbell's marked setup

The source comparison theorem needs a literal containment proof before its
common-Thompson-group transports can be used.  This module records the
elementary subgroup facts that are independent of that source argument.
`CampbellContainment` supplies the marked containments from the precise
fixed-point index consequence of the natural-module theorem. Proving that
source input and the comparison centrality remain separate obligations.
-/

@[expose] public section

universe u v w

namespace CFSG.Quasithin.ChapterC.GlaubermanNiles.Campbell

open Theory.GroupTheory Stellmacher
open scoped Pointwise

variable {T : Type u} [Group T]

private theorem omega_le {G : Type v} [Group G] (A : Subgroup G) :
    omegaOneCenterAmbient A ≤ A := by
  intro x hx
  exact (mem_omegaOneCenterAmbient_iff A x).mp hx |>.1

/- The ambient two-core is normal and hence lies in every supplied Sylow
subgroup.  Keeping this bridge local avoids identifying the two marked
Thompson subgroups prematurely. -/
theorem F_le_pCore {G : Type v} [Group G] [Finite G] :
    F G ≤ pCore 2 G := by
  change omegaOneCenterAmbient (elementaryAbelianMaxJ (pCore 2 G)) ≤ pCore 2 G
  exact (omega_le (elementaryAbelianMaxJ (pCore 2 G))).trans
    (sSup_le fun _ hA => hA.1)

private theorem omega_core_normal {G : Type v} [Group G] [Finite G] :
    (omegaOneCenterAmbient (pCore 2 G)).Normal := by
  let W := omegaOneCenterAmbient (pCore 2 G)
  have hW : W.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    intro g _
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hQ : (pCore 2 G).map (MulAut.conj g).toMonoidHom = pCore 2 G := by
      apply (Subgroup.mem_normalizer_iff_map_conj_eq).mp
      rw [Subgroup.normalizer_eq_top]
      trivial
    calc
      W.map (MulAut.conj g).toMonoidHom =
          omegaOneCenterAmbient ((pCore 2 G).map (MulAut.conj g).toMonoidHom) :=
        (omegaOneCenterAmbient_map_injective (MulAut.conj g).toMonoidHom
          (MulAut.conj g).injective (pCore 2 G)).symm
      _ = W := by rw [hQ]
  exact hW

private theorem V_normal {G : Type v} [Group G] [Finite G] : (V G).Normal := by
  let W := omegaOneCenterAmbient (pCore 2 G)
  have hW : W.Normal := omega_core_normal (G := G)
  change (⁅(⊤ : Subgroup G), W⁆).Normal
  exact @Subgroup.commutator_normal G _ (⊤ : Subgroup G) W inferInstance hW

theorem V_le_pCore {G : Type v} [Group G] [Finite G] :
    V G ≤ pCore 2 G := by
  change ⁅(⊤ : Subgroup G), omegaOneCenterAmbient (pCore 2 G)⁆ ≤ pCore 2 G
  let W := omegaOneCenterAmbient (pCore 2 G)
  have hW : W.Normal := omega_core_normal (G := G)
  exact (@Subgroup.commutator_le_right G _ (⊤ : Subgroup G) W hW).trans
    (omega_le (pCore 2 G))

theorem sylow_commutator_V_le_pCore {G : Type v} [Group G] [Finite G]
    (d : Embedding T G) :
    ⁅(d.sylow : Subgroup G), V G⁆ ≤ pCore 2 G := by
  have hV : (V G).Normal := V_normal (G := G)
  exact (@Subgroup.commutator_le_right G _ (d.sylow : Subgroup G) (V G) hV).trans
    (V_le_pCore (G := G))

theorem F_le_sylow {G : Type v} [Group G] [Finite G]
    (d : Embedding T G) : F G ≤ (d.sylow : Subgroup G) := by
  exact (F_le_pCore (G := G)).trans (pCore_isPGroup.le_sylow_of_normal d.sylow)

theorem V_le_sylow {G : Type v} [Group G] [Finite G]
    (d : Embedding T G) : V G ≤ (d.sylow : Subgroup G) := by
  exact (V_le_pCore (G := G)).trans (pCore_isPGroup.le_sylow_of_normal d.sylow)

theorem transfer_le_marking_range {G : Type v} [Group G]
    {G' : Type w} [Group G'] (d : Embedding T G) (d' : Embedding T G')
    (A : Subgroup G') (_hA : A ≤ d'.marking.range) :
    d.transfer d' A ≤ d.marking.range := by
  rw [Embedding.transfer]
  rintro y ⟨x, hx, rfl⟩
  exact ⟨x, rfl⟩

theorem transfer_eq_of_le_marking {G : Type v} [Group G]
    {G' : Type w} [Group G'] (d : Embedding T G) (d' : Embedding T G')
    (A : Subgroup G') (_hA : A ≤ d'.marking.range) :
    d.transfer d' A = (d'.pull A).map d.marking := rfl

end CFSG.Quasithin.ChapterC.GlaubermanNiles.Campbell

end
