module

public import CFSG.Quasithin.Chapter6.Section01.SourceHStarTwoPerfectOmega
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientHStar
public import Theory.GroupTheory.PResidual.IndexThreeThompson
import all CFSG.Quasithin.Chapter6.Section01.SourceHStarTwoPerfectOmega

/-!
# The residual of the actual H-star seed centralizer

At Sylow index three, a two-kernel quotient whose Thompson image has
two-group normalizer gives Y=[Y,J(T)] for the literal residual of C_H(Z).
The original natural quotient then makes Y centralize the left omega-span.
Its commutators with L lie in O₂(L), so L normalizes this same residual.

The index and image-normalizer conditions are the local geometry supplied
by the symmetric-five overlap source. No normality of O₂(LT) in M is used,
and C_H(Z) is not replaced by the smaller orbit centralizer C_H(U_H).
Source: Aschbacher--Smith 6.1.5, p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter6.Source.Hypothesis611
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V H : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

theorem hstar_seed_residual_of_index_three
    (hout : Chapter3.HasMaximalOutside T M)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hZH : ⁅omegaOneCenterAmbient (T : Subgroup G), H⁆ ≠ ⊥)
    (hi : ((T : Subgroup G).subgroupOf
      (H ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))).index = 3)
    {Q : Type*} [Group Q]
    (q : (H ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) : Subgroup G) →* Q)
    (hk : IsPGroup 2 q.ker)
    (hn : IsPGroup 2 (normalizer
      ((elementaryAbelianMaxJ ((T : Subgroup G).subgroupOf
        (H ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)))).map q : Set Q))) :
    let N := H ⊓ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)
    let Y := (pResidual 2 N).map N.subtype
    Y = ⁅Y,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      Y ≤ centralizer
        (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) L : Set G) ∧
      L ≤ normalizer (Y : Set G) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let U := conjugateSpanBy Z L
  let N := H ⊓ centralizer (Z : Set G)
  let Y := (pResidual 2 N).map N.subtype
  have hTN : (T : Subgroup G) ≤ N := le_inf hH.1.1.2 (by
    intro t ht z hz
    exact (((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 t ht).symm)
  let S := T.subtype hTN
  have hSmap : (S : Subgroup N).map N.subtype = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le hTN
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup N)).map N.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [←elementaryAbelianMaxJ_map_injective N.subtype N.subtype_injective,hSmap]
  have hc : Y = ⁅Y,elementaryAbelianMaxJ (T : Subgroup G)⁆ := by
    have he := congrArg (map N.subtype)
      (residual_eq_thompson_commutator_of_index_three S hi q hk hn)
    simpa only [map_commutator,hJmap] using he
  have hYN : Y ≤ N := map_subtype_le _
  have hTY : (T : Subgroup G) ≤ normalizer (Y : Set G) :=
    (hTN.trans N.le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image N (pResidual 2 N))
  have hm := h.omega_natural_fixed_quotient_of_hstar_moves hout hH hZH
  let hs := h.rankOneInput hout
  have hnorm := hYN.trans (h.hstar_omega_centralizer_normalizes hH hm hZH)
  have hfix : Y ≤ centralizer (U : Set G) := by
    apply twoPerfect_centralizes_of_commutator_two_cover Y
      (elementaryAbelianMaxJ (T : Subgroup G)) ((T : Subgroup G) ⊓ L) U
      (isPPerfect_embedded_pResidual 2 N) (T.isPGroup'.to_le inf_le_left)
      (hnorm.trans inf_le_left) (hnorm.trans inf_le_right)
      (inf_le_right.trans (le_normalizer_conjugateSpanBy Z L)) _ hc
    exact (hs.thompson_le_left_sylow_core_of_natural_quotient
      (h.maximal_eq_normalizer_L ▸ hH) hm hZH).trans
      (sup_le_sup_left (hs.omega_span_core_centralizes hm) _)
  have hYL : Y ≤ normalizer (L : Set G) :=
    h.maximal_eq_normalizer_L ▸ hYN.trans (hstar_omega_centralizer_le_M hH hZH)
  have hLC : L ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy Z L).trans (normalizer_le_normalizer_centralizer U)
  have hcomm : ⁅L,Y⁆ ≤ L.pCoreIn 2 := by
    apply (le_inf (le_normalizer_iff_commutator_le_left.mp hYL) ?_).trans
      (hs.left_omega_span_centralizer_le_core hm)
    exact (commutator_mono le_rfl hfix).trans
      (le_normalizer_iff_commutator_le_right.mp hLC)
  have hQL : L.pCoreIn 2 ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
      (h.sylow_normalizes_L.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hTNnorm : (T : Subgroup G) ≤ normalizer (N : Set G) :=
    hTN.trans N.le_normalizer
  refine ⟨hc,hfix,?_⟩
  exact normalizes_residual_of_commutator_le_two L (T : Subgroup G) N (L.pCoreIn 2)
    hTNnorm hQL (isPGroup_pCoreIn 2 L)
    (L.le_normalizer.trans (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
    hcomm

end CFSG.Quasithin.Chapter6.Source.Hypothesis611
