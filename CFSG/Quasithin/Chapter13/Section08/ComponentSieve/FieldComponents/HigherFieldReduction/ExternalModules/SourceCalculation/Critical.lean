module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation.EarlierData
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.Geometry
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.CriticalInputs.ParabolicCore.Coordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.Construction
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Critical placement from the preceding source geometry

Source: Aschbacher–Smith, 13.8.20(a), printed p.954, using
13.8.4(6), 13.8.8(2), 13.8.18(4), and Notation 13.2.1.

The even marked L₂ Borel and theta force the covered local case. Its actual
order-nine quotient survives the two-group kernel of the star map. Together
with the prescribed Sylow subgroup and Borel normalization, the full moved
coordinates identify O₂(L₁*T*) with T* ∩ K*. The genuine geometric selection
then places the same critical pair's conjugate in that intersection.

Only the prefix of the old marked-Borel argument is required. No covered
centralizer formula, old index, or assumed component placement is used.
The coordinates remain on W = [U,K*], without identifying W with U.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation
open Components.Swapped.LinearTwo
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open FFSections Structure.MarkedBorel
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

section Core
variable (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [(V₁.subgroupOf (Source.UH H V₃)).Normal]
  [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁) (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)

include f d in
/-- The marked even-degree component forces the covered local quotient, using
only the earlier theta and local action data. -/
theorem covered_of_even_component
    (ha : ExternalXAlternative H K X) {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n)) (heven : Even n) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  have hgen : H = K ⊔ (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)) := by
    rw [f.generation, f.single_component, f.overlap]
  have hHV₁ := f.setup.fixes_line.trans (Subgroup.centralizer_le_normalizer _)
  let D := one L (T : Subgroup G) V₁
  let B₀ := HigherFieldReduction.borelLift H K f.component_le (SylowBorel.relativeBorel (Source.starImage H K) S)
  let B := borelResidual B₀
  have hDH : D ≤ H := by rw [hgen]; exact le_sup_left.trans le_sup_right
  have hTH : (T : Subgroup G) ≤ H := by rw [hgen]; exact le_sup_right.trans le_sup_right
  have hTp : IsPGroup 2 (T : Subgroup G) := by
    obtain ⟨P,hP⟩ := d.sylow
    rw [← hP]
    exact P.isPGroup'.map H.subtype
  obtain ⟨hXD,hXp,hXcard,hsol,_⟩ := selected_local_inputs L (T : Subgroup G) V V₁ V₃ X hTp
    (hTH.trans hHV₁) d.marked_cases d.ordinary_card d.covered_action d.covered_factor d.seed_commutator
  let : Group.IsSolvable (D ⊔ (T : Subgroup G) : Subgroup G) := hsol
  obtain ⟨_,hB₀M⟩ := source_borel_normalized_and_le_M H K D (T : Subgroup G) (normalizer (V₁ : Set G)) M
    f.component_le hDH hTH S hn hmodel d.sylow_inter (f.component_le.trans hHV₁)
    ((sup_le hDH hTH).trans hHV₁) d.solvable_overgroups
  have hBK : B ≤ K := (map_subtype_le _).trans (borelLift_le H K f.component_le _)
  have hBM : B ≤ M := (map_subtype_le _).trans hB₀M
  have hDM : D ≤ M := by
    rw [show D = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3} from d.theta, closure_le]
    exact fun _ hx => hx.1.2
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  have hc : Nat.card (Source.starImage H X) = 3 := Structure.star_card_three H X ha.1 hXcard
  have hne : ¬ Source.starImage H X ≤ Source.starImage H K := by
    intro h
    exact ha.2.1 (LinearThree.Geometry.CoveredProduct.ResidualPlacement.le_of_star_le
      H K X f.component_le ha.1 hXp h)
  have hr : 1 < primeRank 3 (B ⊔ X : Subgroup G) :=
    rank_gt_one_of_external_cubic H K B X f.component_le hBK ha.1 hc hne ha.2.2.1
      (marked_borel_star_rank H K f.component_le S hn hmodel heven)
  have hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) :=
    d.marked_cases.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  obtain ⟨_,hcov⟩ := covered_of_external_borel_rank H M L D B X (hBK.trans f.component_le) hBM
    ha.1 (hXD.trans hDM) d.theta hmodels d.ordinary_card hr
  exact hcov

include f d in
/-- The two-core of the actual marked L₁*T* is the component Sylow intersection. -/
theorem twoCore_eq_intersection
    (ha : ExternalXAlternative H K X)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H)
    (W : Subrepresentation ρ)
    (_hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K))
    (c : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation (Source.starImage H K) s) :
    (Source.starImage H (one L (T : Subgroup G) V₁) ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2 =
      Source.starImage H (T : Subgroup G) ⊓ Source.starImage H K := by
  let D := one L (T : Subgroup G) V₁
  let A := Source.starImage H (D ⊔ (T : Subgroup G))
  let Ks := Source.starImage H K
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  have hDH : D ≤ H := le_sup_left.trans f.setup.local_le
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans f.setup.local_le
  have hmodel : ClassicalGroup.IsPSL Ks 2 (2 ^ 2) := psl_four_of_alternating c.component
  obtain ⟨_, _, _, hs, _⟩ := Structure.MarkedBorel.selected_local_inputs
    L (T : Subgroup G) V V₁ V₃ X T.isPGroup' f.setup.line_normalized
    d.marked_cases d.ordinary_card d.covered_action d.covered_factor d.seed_commutator
  let : Group.IsSolvable (D ⊔ (T : Subgroup G) : Subgroup G) := hs
  have hcov := covered_of_even_component H K X L V V₃ V₁ M T ρ P f S d ha
    (by decide : 1 < 2) hmodel (by decide : Even 2)
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
  have he := CriticalInputs.ParabolicCore.Coordinates.parabolic_core c S A P hPA hn
    (d.sylow_inter.trans (by rw [f.sylow_image])) h9
  have hA : A = Source.starImage H D ⊔ Source.starImage H (T : Subgroup G) := by
    unfold A Source.starImage
    rw [subgroupOf_sup hDH hTH, Subgroup.map_sup]
  rwa [hA, f.sylow_image] at he

include f d in
/-- The same core is the star image of T ∩ K, with the quotient kernel retained. -/
theorem twoCore_eq_star_intersection
    (ha : ExternalXAlternative H K X)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H) (W : Subrepresentation ρ)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K))
    (c : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation (Source.starImage H K) s) :
    (Source.starImage H (one L (T : Subgroup G) V₁) ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2 =
      Source.starImage H ((T : Subgroup G) ⊓ K) := by
  rw [LocalBorel.star_intersection H K (T : Subgroup G) d.sylow]
  exact twoCore_eq_intersection H K X L V V₃ V₁ M T ρ P f S d ha s W hW c

end Core

section Selection
open CriticalGeometry CriticalInputs
variable {G : Type u} [Group G] [Finite G]
  (H K X L V V₃ V₁ M : Subgroup G) (T : Sylow 2 G)
  [(K.subgroupOf H).Normal]
  [IsElementaryAbelian 2 (Source.UH H V₃)] [IsElementaryAbelian 2 (Source.VH H V)]
  (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
  (P : Sylow 2 (Source.Hstar H)) {𝒦 : GroupClass.{u}}
  (f : SourceOrbit.F918Hypotheses H K L (one L (T : Subgroup G) V₁)
    (T : Subgroup G) V V₃ V₁ ρ P 𝒦)
  (S : Sylow 2 (Source.starImage H K))
  (d : EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)

include f d in
/-- Construct one source critical pair with rank greater than one, quadratic
action on the original U, and its actual H-conjugate placed in T₀* ≤ K*.
The output identifies T₀* both as T* ∩ K* and as O₂(L₁*T*). -/
theorem exists_critical_witness
    (ha : ExternalXAlternative H K X) (hVH : V ≤ H)
    (initial : CriticalPair L (T : Subgroup G) H V)
    (e : EarlierInputs L (T : Subgroup G) H V V₃ V₁ ρ)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H) (W : Subrepresentation ρ)
    (hW : W.toSubmodule = subspaceCommutator ρ ⊤ (Source.starImage H K))
    (c : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation
      (Source.starImage H K) s) :
    ∃ w : SelectedWitness L (T : Subgroup G) H V (one L (T : Subgroup G) V₁) V₃ V₁ ρ,
      Source.starImage H w.alpha ≤ Source.starImage H ((T : Subgroup G) ⊓ K) ∧
      Source.starImage H ((T : Subgroup G) ⊓ K) =
        Source.starImage H (T : Subgroup G) ⊓ Source.starImage H K ∧
      Source.starImage H ((T : Subgroup G) ⊓ K) =
        (Source.starImage H (one L (T : Subgroup G) V₁) ⊔
          Source.starImage H (T : Subgroup G)).pCoreIn 2 ∧
      Source.starImage H ((T : Subgroup G) ⊓ K) ≤ Source.starImage H K := by
  obtain ⟨w⟩ := CriticalInputs.exists_selected_witness H K L (one L (T : Subgroup G) V₁)
    (T : Subgroup G) V V₃ V₁ ρ P f initial hVH e s W hW c
  have hcore := twoCore_eq_star_intersection
    H K X L V V₃ V₁ M T ρ P f S d ha s W hW c
  refine ⟨w, ?_, LocalBorel.star_intersection H K (T : Subgroup G) d.sylow,
    hcore.symm, map_mono (subgroupOf_mono H inf_le_right)⟩
  rw [← hcore]
  exact w.alpha_star_le_core (le_sup_left.trans f.setup.local_le)
    (le_sup_right.trans f.setup.local_le)

end Selection

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation

end
