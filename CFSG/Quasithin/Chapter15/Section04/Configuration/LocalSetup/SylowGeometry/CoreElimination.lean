module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.InternalModule
public import Theory.GroupTheory.TwoLocalCharacteristicControl
public import Stellmacher.OmegaOneCenterMap

/-!
# Characteristic-two reductions for the contrary Sylow overgroup

The internal-module construction proves F*(H)=O₂(H), constructs the actual
faithful two-reduced conjugation module ⟨Zᴷ⟩, and derives its Thompson offender
from the source factor. The terminal centralizer bound below follows from
two-local uniqueness: XT centralizes the nontrivial two-group C_Z(X), so its
normalizer, and hence its centralizer, lies in M₁. The exchanged factor
lies outside H∩M₁ because otherwise its conjugate, KU and the outside
Y-factor all lie in M₁. Characteristic two also passes to relatively
subnormal components.

The characteristic-two contradiction still requires the C.2.7 hypotheses for
the exchanged component, the full block/module sieve, and the rank-one Borel
argument proving q=4 and C_Z(X)≤Z(H). In particular this module does not
assume that last containment or assert completion of 15.4.20. Final Sylow
assembly remains in the owning SylowGeometry development.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
15.4.20, printed p.1164, final characteristic-two paragraph.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
open Subgroup Stellmacher Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The final centralizer bound comes from two-local uniqueness, independently
of the block-theoretic assertion that C_Z(X) is central in H. -/
theorem fixed_seed_centralizer_le {T X Z M : Subgroup G}
    (hZ : Z = omegaOneCenterAmbient T)
    (hne : Z ⊓ centralizer (X : Set G) ≠ ⊥)
    (hunique : ∀ N : Subgroup G, IsMaximalTwoLocal N → X ⊔ T ≤ N → N = M) :
    centralizer ((Z ⊓ centralizer (X : Set G) : Subgroup G) : Set G) ≤ M := by
  let : IsElementaryAbelian 2 Z := hZ ▸ omegaOneCenterAmbient_elementaryAbelian T
  have hXZ : X ≤ centralizer ((Z ⊓ centralizer (X : Set G) : Subgroup G) : Set G) :=
    le_centralizer_iff.mpr inf_le_right
  have hTZ : T ≤ centralizer (Z : Set G) := by
    intro t ht
    apply mem_centralizer_iff.mpr
    intro z hz
    rw [hZ] at hz
    exact ((mem_omegaOneCenterAmbient_iff T z).mp hz).2.2 t ht |>.symm
  exact centralizer_le_of_unique_twoLocal
    ((IsElementaryAbelian.isPGroup 2 Z).to_le inf_le_left) hne
    ((sup_le hXZ (hTZ.trans (centralizer_le inf_le_left))).trans
      (Subgroup.centralizer_le_normalizer _)) hunique

omit [Finite G] in
/-- An exchanged factor cannot lie in M_H: its conjugate would also lie
in M₁, putting KU and the given outside Y-factor there. -/
theorem exchanged_factor_outside {H K K₁ U Y M : Subgroup G} {r : G}
    (hH : K ⊔ U = H) (hK : K₁ ⊔ K₁.map (MulAut.conj r).toMonoidHom = K)
    (hr : r ∈ U) (hUM : U ≤ M) (hYH : Y ≤ H) (hYM : ¬ Y ≤ M) :
    ¬ K₁ ≤ H ⊓ M := by
  intro hK₁
  have hK₁M : K₁ ≤ M := hK₁.trans inf_le_right
  have hconj : K₁.map (MulAut.conj r).toMonoidHom ≤ M := by
    exact (map_mono hK₁M).trans
      (mem_normalizer_iff_map_conj_eq.mp (M.le_normalizer (hUM hr))).le
  have hKM : K ≤ M := hK ▸ sup_le hK₁M hconj
  exact hYM (hYH.trans (hH ▸ sup_le hKM hUM))

/-- A relatively subnormal component inherits the characteristic-two
condition. Establishing that relative subnormality remains an input here. -/
theorem generalizedFitting_eq_twoCore_of_subnormal
    (L : Subgroup G) (hL : L.IsSubnormal)
    (hF : generalizedFitting G = pCore 2 G) :
    generalizedFitting L = pCore 2 L := by
  apply generalizedFitting_eq_pCore_of_selfCentralizing 2
  apply subnormal_core_selfCentralizing _ L hL
  rw [← hF]
  exact ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination
