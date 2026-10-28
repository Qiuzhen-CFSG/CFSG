module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.QuotientModel.QuotientSylow
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.Lift.SymmetricLocal.LocalSylow

/-!
# The original local Sylow from the selected component structure

The quotient centralizer calculation supplies the model premise of
`lift_local_sylow_of_quotient`. Pulling its witness back through H → H/O₂(H)
gives precisely N_T(D) in H ∩ N_G(D), preserving the original T and selected i.
Together with `core_identities_of_selected`, this completes the three quotient
calculations required by the Core and LocalSylow reductions.

The second theorem also constructs the normalizer preimage using the source
comparison for the centralizer of i modulo ⟨z⟩. This is the comparison obtained
from the selected rank-four action; it does not assert that C_H(i) surjects
onto the quotient centralizer. The selected component data and this comparison
remain earlier-source inputs supplied by the Selection owner. The ambient
normalizer promotion and symmetry assembly remain with SymmetricLocal's owner.

Source: Aschbacher–Smith, Lemma 14.4.9, printed p.1010, using case (3) of
14.4.2, printed pp.1006–1007, and G.11.2(7).
-/

public section

namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.QuotientModel
open Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- Discharge the quotient Sylow premise of the literal LocalSylow contract
from the actual selected component action. No local Sylow conclusion is assumed. -/
theorem local_sylow_of_selected
    (T : Sylow 2 G) (z i : G) (D : Subgroup G)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiT : i ∈ T) (hiz : i ∈ centralizer ({z} : Set G))
    (hpre : (normalizer (D : Set G)).subgroupOf (centralizer ({z} : Set G)) =
      (centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩} :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G))))).comap
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))
    (d : SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) i).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    ∃ P : Sylow 2 (centralizer ({z} : Set G) ⊓ normalizer (D : Set G) : Subgroup G),
      (P : Subgroup (centralizer ({z} : Set G) ⊓ normalizer (D : Set G) : Subgroup G)) =
        (localSylow (T : Subgroup G) D).subgroupOf
          (centralizer ({z} : Set G) ⊓ normalizer (D : Set G)) := by
  exact lift_local_sylow_of_quotient T z i D hTz hiz hpre
    (quotient_centralizer_sylow_of_selected T z i hTz hiT hiz d)

/-- The local witness for D = [U,i]⟨i,z⟩, using the source centralizer-modulo-line
comparison and the proved quotient calculation. The hypotheses retain the actual
rank-four displacement, quotient map, and selected involution. -/
theorem lift_local_sylow_of_selected
    (U : Subgroup G) [IsExtraspecial 2 U] (T : Sylow 2 G) (z i : G)
    (hZ : (center U).map U.subtype = zpowers z)
    (hUcore : (centralizer ({z} : Set G)).pCoreIn 2 = U)
    (hi : orderOf i = 2)
    (hTz : (T : Subgroup G) ≤ centralizer ({z} : Set G))
    (hiT : i ∈ T) (hiz : i ∈ centralizer ({z} : Set G))
    (hD : IsElementaryAbelian 2 (centralizerLift U z i))
    (hmoved : Nat.card (((⁅U,zpowers i⁆).subgroupOf U).map
      (QuotientGroup.mk' (center U))) = 16)
    (hout : i ∉ U)
    (hcompare : ((commutatorPreimage (centralizer ({z} : Set G))
        (zpowers i) (zpowers z)).subgroupOf (centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))) =
      centralizer ({QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩} :
        Set ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))))
    (d : SelectedComponentData
      ((centralizer ({z} : Set G)) ⧸ pCore 2 (centralizer ({z} : Set G)))
      (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G))) ⟨i,hiz⟩)
      (((diagonalResidual (centralizer ({z} : Set G)) i).subgroupOf
        (centralizer ({z} : Set G))).map
        (QuotientGroup.mk' (pCore 2 (centralizer ({z} : Set G)))))) :
    ∃ P : Sylow 2 (centralizer ({z} : Set G) ⊓
        normalizer (centralizerLift U z i : Set G) : Subgroup G),
      (P : Subgroup (centralizer ({z} : Set G) ⊓
        normalizer (centralizerLift U z i : Set G) : Subgroup G)) =
        (localSylow (T : Subgroup G) (centralizerLift U z i)).subgroupOf
          (centralizer ({z} : Set G) ⊓ normalizer (centralizerLift U z i : Set G)) := by
  exact local_sylow_of_selected T z i (centralizerLift U z i) hTz hiT hiz
    (lift_normalizer_quotient_preimage U z i hZ hUcore hi hiz hD hmoved hout hcompare) d

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.QuotientModel
