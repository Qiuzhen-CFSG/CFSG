module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.Assembly
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.ParabolicCore.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Construction
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# The actual exceptional local parabolic two-core

In the moved tensor branch, the marked component equivalence identifies
K* with PSL₂(4) through its genuine five-point action. The even-field Borel
and theta force the covered local case, whose actual L₁ quotient has order
nine. The star map has a two-group kernel, so nine still divides |L₁*|.
Solvability of L₁T normalizes the Borel at the specified Sylow S. In the
full marked coordinates, this places L₁*T* inside S₄ × S₃; its order is
at least 16 · 9, so it fills this parabolic. The coordinate calculation
then gives O₂(L₁*T*) = T* ∩ K*.

The final image identity retains O₂(H) ≤ T and the intersection with K:
T* ∩ K* = (T ∩ K)*. Full coordinates are on the actual moved module W;
no identification W = U or additional faithfulness on W is needed. The
source action, moved-space equality and cubic marking are retained in the
public contract. The group calculation uses the corresponding full marked
equivalence and the earlier local geometry. No local Borel index formula
or alternative-(b) containment L₁ ≤ K enters the proof.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20(a), printed p.954/PDF p.971; Notation 13.2.1, printed p.877.
-/

public section

open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.ParabolicCore
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FFSections
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem psl_four_of_alternating {D : Type*} [Group D]
    (e : D ≃* alternatingGroup (Fin 5)) : ClassicalGroup.IsPSL D 2 (2 ^ 2) := by
  have hc : Nat.card (GaloisField 2 2) = 4 := by rw [GaloisField.card 2 2 (by decide)]; norm_num
  obtain ⟨ef⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hc
  exact ⟨GaloisField 2 2, inferInstance, inferInstance, hc, ⟨e.trans ef.symm⟩⟩

private theorem nine_dvd_star (H D : Subgroup G) (hDH : D ≤ H)
    (hc : Nat.card (D ⧸ pCore 2 D) = 9) : 9 ∣ Nat.card (Source.starImage H D) := by
  let q := starHom H D hDH
  have hk : IsPGroup 2 q.ker := TorusModels.starHom_ker_isTwoGroup H D hDH
  have hcop : Nat.Coprime 9 (Nat.card q.ker) := by
    obtain ⟨n, hn⟩ := hk.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 9 2).pow_right n
  have hd : 9 ∣ Nat.card D := by
    rw [card_eq_card_quotient_mul_card_subgroup (pCore 2 D), hc]
    exact dvd_mul_right _ _
  have he : Nat.card D = Nat.card (Source.starImage H D) * Nat.card q.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup q.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv,
      show q.range = Source.starImage H D from range_starHom H D hDH]
  rw [he] at hd
  exact hcop.dvd_mul_right.mp hd

variable (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁) (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : LocalData H K X L (T : Subgroup G) V V₃ V₁ M f.component_le S)

include f d in
/-- The two-core of the actual marked L₁*T* is the component Sylow intersection. -/
theorem twoCore_eq_intersection
    (ha : ExternalXAlternative H K X) (_hVH : V ≤ H)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H)
    (W : Subrepresentation ρ)
    (_hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K))
    (c : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation (Source.starImage H K) s)
    (_hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X) :
    (Source.starImage H (one L (T : Subgroup G) V₁) ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2 =
      Source.starImage H (T : Subgroup G) ⊓ Source.starImage H K := by
  let D := one L (T : Subgroup G) V₁
  let A := Source.starImage H (D ⊔ (T : Subgroup G))
  let Ks := Source.starImage H K
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  have hDH : D ≤ H := le_sup_left.trans f.setup.local_le
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans f.setup.local_le
  have hgen : H = K ⊔ (D ⊔ (T : Subgroup G)) := by
    rw [f.generation, f.single_component, f.overlap]
  have hHV₁ : H ≤ normalizer (V₁ : Set G) :=
    f.setup.fixes_line.trans (Subgroup.centralizer_le_normalizer _)
  have hmodel : ClassicalGroup.IsPSL Ks 2 (2 ^ 2) := psl_four_of_alternating c.component
  obtain ⟨_, _, _, hs, _⟩ := Structure.MarkedBorel.selected_local_inputs
    L (T : Subgroup G) V V₁ V₃ X T.isPGroup' f.setup.line_normalized
    d.marked_cases d.ordinary_card d.covered_action d.covered_factor d.seed_commutator
  let : Group.IsSolvable (D ⊔ (T : Subgroup G) : Subgroup G) := hs
  have hcov := (Structure.MarkedBorel.source_placements H K L (T : Subgroup G) V V₁ V₃ M X
    f.component_le hgen d.sylow hHV₁ d.marked_cases d.ordinary_card d.covered_action
    d.covered_factor d.seed_commutator d.theta d.solvable_overgroups ha S d.sylow_inter
    (by decide : 1 < 2) hmodel (by decide : Even 2) d.covered_formula).2.1
  obtain ⟨a⟩ := d.covered_action hcov
  have h9 : 9 ∣ Nat.card A := (nine_dvd_star H D hDH
    (a.one_quotient_card (d.covered_factor hcov))).trans
      (card_dvd_of_le (map_mono (subgroupOf_mono H le_sup_left)))
  let : Group.IsSolvable ((D ⊔ (T : Subgroup G)).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe f.setup.local_le).toMonoidHom)
      (subgroupOfEquivOfLe f.setup.local_le).injective
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective
      ((D ⊔ (T : Subgroup G)).subgroupOf H))
  have hPA : (P : Subgroup (Source.Hstar H)) ≤ A := by
    rw [f.sylow_image]
    exact map_mono (subgroupOf_mono H le_sup_right)
  have hSA : (S : Subgroup Ks).map Ks.subtype ≤ A := by
    rw [d.sylow_inter]
    exact inf_le_left.trans (map_mono (subgroupOf_mono H le_sup_right))
  have hn := Structure.MarkedBorel.solvable_normalizes_borel Ks A S
    (by decide : 1 < 2) hmodel hSA
  have he := Coordinates.parabolic_core c S A P hPA hn
    (d.sylow_inter.trans (by rw [f.sylow_image])) h9
  have hA : A = Source.starImage H D ⊔ Source.starImage H (T : Subgroup G) := by
    unfold A Source.starImage
    rw [subgroupOf_sup hDH hTH, Subgroup.map_sup]
  rwa [hA, f.sylow_image] at he

include f d in
/-- The same core is the star image of T ∩ K, with the quotient kernel retained. -/
theorem twoCore_eq_star_intersection
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H) (W : Subrepresentation ρ)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K))
    (c : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation (Source.starImage H K) s)
    (hmark : (alternatingGroup (Fin 3)).map s = Source.starImage H X) :
    (Source.starImage H (one L (T : Subgroup G) V₁) ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2 =
      Source.starImage H ((T : Subgroup G) ⊓ K) := by
  rw [LocalBorel.star_intersection H K (T : Subgroup G) d.sylow]
  exact twoCore_eq_intersection H K X L V V₃ V₁ M T ρ P f S d ha hVH s W hW c hmark

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.ParabolicCore

end
