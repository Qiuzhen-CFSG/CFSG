module

public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.CoverInputs
public import CFSG.Quasithin.Chapter16.Section01To02.CoverAndSylowElimination.Kernel
public import Theory.GroupTheory.QuasithinBasic

/-!
# The final rank contradiction in the covered Suzuki case

The index-eight quotient and nontrivial center force `|Ω₁(T_L)| > 8`.
Once its conjugate is placed in both component normalizers, its actions on
the two components have nontrivial kernels. Normalizer control puts each
component inside `Hᵍ`, contradicting 16.2.9(2).

The placement and elementary structure remain explicit prerequisites here.
Thus this proves the last implication in 16.2.11, not its missing premises.
The only rank bound is the supplied computation for the automorphism group
of the actual Suzuki cover, transported to the actual conjugate component.

Source: Aschbacher–Smith, proof of 16.2.11, printed p.1176.
-/

public section
namespace CFSG.Quasithin.Chapter16.CoverAndSylowElimination

open Subgroup Theory.GroupTheory ChapterI.Section06To08

variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {z u : G} {L : Subgroup G}

/-- The strict size comparison, derived from the actual index rather than
assumed as a rank bound on the ambient group. -/
theorem CoverStructure.omega_card_gt_eight (hs : CoverStructure T L)
    (hne : center L ≠ ⊥) : 8 < Nat.card (sylowOmega T L) := by
  have hc : Nat.card (componentCenter L) = Nat.card (center L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hn : 1 < Nat.card (center L) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hne
  have hh := ((componentCenter L).subgroupOf (sylowOmega T L)).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hs.center_le).toEquiv] at hh
  change Nat.card (componentCenter L) * (componentCenter L).relIndex (sylowOmega T L) = _ at hh
  rw [hs.center_index, hc] at hh
  omega

private theorem component_le_conjugate_normalizer
    (h : EarlierConclusions T z u L) {g : G} {V M : Subgroup G}
    (hVe : IsElementaryAbelian 2 V) (hlarge : 8 < Nat.card V)
    (hVL : V ≤ conjSubgroup L g) (hVN : V ≤ normalizer (M : Set G))
    (hrank : primeRank 2 (MulAut M) ≤ 3) :
    M ≤ conjSubgroup (localComponentNormalizer z L) g := by
  have hCne := elementary_centralizer_ne_bot V M hVN hVe hrank hlarge
  let : IsElementaryAbelian 2 V := hVe
  have hp := (IsElementaryAbelian.isPGroup 2 V).to_le
    (inf_le_left : V ⊓ centralizer (M : Set G) ≤ V)
  have hcontrol := h.conjugate_centralizer_control g hp hCne
    (inf_le_left.trans (hVL.trans (conjSubgroup_mono le_sup_right g)))
  exact (le_centralizer_iff.mpr inf_le_right).trans hcontrol

/-- The placed conjugate cannot exist in the nontrivial covered case.
Its two centralizer kernels force the prohibited containment of `L₀`. -/
theorem not_coverPlacement (h : EarlierConclusions T z u L)
    (hc : center L ≠ ⊥) (d : SuzukiCoverInput T L) (hs : CoverStructure T L) :
    ¬ CoverPlacement T z u L := by
  rintro ⟨g, hg, _, _, _, _, hVN⟩
  let V := conjSubgroup (sylowOmega T L) g
  let : IsElementaryAbelian 2 (sylowOmega T L) := hs.elementary
  have hVe : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hlarge : 8 < Nat.card V := by
    simpa only [V, card_conjSubgroup] using hs.omega_card_gt_eight hc
  have hVL : V ≤ conjSubgroup L g :=
    conjSubgroup_mono (sylowOmega_le.trans inf_le_right) g
  have hL : L ≤ conjSubgroup (localComponentNormalizer z L) g :=
    component_le_conjugate_normalizer h hVe hlarge hVL
      (hVN.trans (inf_le_left.trans inf_le_right)) d.automorphism_rank.le
  have hrank : primeRank 2 (MulAut (conjSubgroup L u)) ≤ 3 := by
    have he := primeRank_equiv 2 (MulAut.congr ((MulAut.conj u).subgroupMap L))
    exact he.symm.le.trans d.automorphism_rank.le
  have hLu : conjSubgroup L u ≤ conjSubgroup (localComponentNormalizer z L) g :=
    component_le_conjugate_normalizer h hVe hlarge hVL
      (hVN.trans inf_le_right) hrank
  exact h.noncontainment g hg (h.closure_eq ▸ sup_le hL hLu)

end CFSG.Quasithin.Chapter16.CoverAndSylowElimination
