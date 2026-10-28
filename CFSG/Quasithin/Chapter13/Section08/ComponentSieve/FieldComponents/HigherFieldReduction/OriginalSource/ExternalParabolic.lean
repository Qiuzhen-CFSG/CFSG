module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource.Critical
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.SourceCalculation.Critical
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.ParabolicMarking.Quotients

/-!
# Original external parabolic and marked-five contradiction

The original local setup supplies the ordinary and covered quotient actions,
theta, solvable overgroup control and the literal Sylow intersection. An even
external PSL₂ component forces the full hexacode cover. Its order-nine residual
image and the marked S₄ × S₃ calculation identify O₂(L₁*T*) with T* ∩ K*.
The original critical witness then contradicts a faithful marked-five tensor
action on any invariant subspace of U_H/V₁.

This discharges the parabolic and geometric premises of the external PSL₂
endpoint. It does not identify the component moved space with all of U_H/V₁.
Construction of the actual FF constituent and its coordinates, the other field
branches and final source assembly remain with qt-d-138-fields-source;
qt-d-1381-source supplies the preceding original context.
Source: Aschbacher–Smith, 13.8.18(4) and 13.8.20(a), printed pp.953–954.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
open SourceCompletion TransvectionRecognition.Component.ModelExtension
open LinearThree.Geometry.CoveredProduct.ResidualPlacement
open ExternalModules ExternalModules.FFSections
open Components.Swapped.LinearTwo Structure.MarkedBorel
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ M G₁ H K X : Subgroup G}

private theorem source_covered_action
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hc : Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms)) :
    Nonempty (LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃) := by
  rcases local_quotient_alternatives c.localSetup with ⟨e,he⟩ | ⟨e,he⟩
  · obtain ⟨ec⟩ := hc
    have hh := Nat.card_congr (centerCongr (e.symm.trans ec)).toEquiv
    rw [Representation.Hexacode.even_center_card,
      alternatingGroup.center_eq_bot (by simp),card_bot] at hh
    omega
  · exact local_covered_flag_model c.localSetup e he

/-- All local inputs to the marked external parabolic calculation follow
from the original context, with the same Sylow intersection and full cover. -/
theorem source_external_local_data
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁))
    (S : Sylow 2 (Source.starImage H K))
    (hS : (S : Subgroup (Source.starImage H K)).map (Source.starImage H K).subtype =
      Source.starImage H (T : Subgroup G) ⊓ Source.starImage H K) :
    SourceCalculation.EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S := by
  refine {
    local_cases := hlocal.imp id (fun h => ⟨SourceAssembly.tripleCover_of_hex_mark h.1.some,h⟩)
    ordinary_card := LocalFitting.ordinary_core_card c.localSetup
    covered_action := source_covered_action c
    covered_factor := ?_
    seed_commutator := (Section07.ModelExclusions.seed_commutator_point_residual
      (localNaturalSetup c.localSetup)).symm
    theta := (Section07.ModelExclusions.theta_intersection (localNaturalSetup c.localSetup)
      c.maximal c.component.local_overgroup).symm
    solvable_overgroups := ?_
    sylow := ⟨T.subtype (le_sup_right.trans c.component.local_overgroup.1.2),
      map_subgroupOf_eq_of_le (le_sup_right.trans c.component.local_overgroup.1.2)⟩
    sylow_inter := hS }
  · intro hc
    obtain ⟨a⟩ := source_covered_action c hc
    exact CoverFactorization.source_factorization a
  · intro J hJ hJG hs
    apply SolvableSource.solvable_overgroup_source c.localSetup c.maximal c.f9
      c.centralizer c.noncentral_core c.earlier1339 J hJ _ hs
    simpa only [c.localSetup.first_normalizer] using hJG

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

variable (S : Sylow 2 (Source.starImage H K))

/-- An even-degree external PSL₂ component forces the full covered local quotient. -/
theorem source_external_covered_of_even_component
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (d : SourceCalculation.EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)
    (ha : ExternalXAlternative H K X) {n : ℕ} (hn : 1 < n)
    (hmodel : ClassicalGroup.IsPSL (Source.starImage H K) 2 (2 ^ n)) (heven : Even n) :
    Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) := by
  let : (K.subgroupOf H).Normal := c.component.normal
  have hKH : K ≤ H := (le_sup_left.trans le_sup_left).trans_eq c.component.generated
  have hgen : H = K ⊔ (one L (T : Subgroup G) V₁ ⊔ (T : Subgroup G)) := by
    simpa only [sup_assoc] using c.component.generated.symm
  have hHV₁ := (c.f9 H c.component.local_overgroup).H_centralizes.trans (Subgroup.centralizer_le_normalizer _)
  let D := one L (T : Subgroup G) V₁
  let B₀ := HigherFieldReduction.borelLift H K hKH (SylowBorel.relativeBorel (Source.starImage H K) S)
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
    hKH hDH hTH S hn hmodel d.sylow_inter (hKH.trans hHV₁)
    ((sup_le hDH hTH).trans hHV₁) d.solvable_overgroups
  have hBK : B ≤ K := (map_subtype_le _).trans (borelLift_le H K hKH _)
  have hBM : B ≤ M := (map_subtype_le _).trans hB₀M
  have hDM : D ≤ M := by
    rw [show D = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3} from d.theta, closure_le]
    exact fun _ hx => hx.1.2
  let : (X.subgroupOf H).Normal := ha.2.2.2.1
  have hc : Nat.card (Source.starImage H X) = 3 := Structure.star_card_three H X ha.1 hXcard
  have hne : ¬ Source.starImage H X ≤ Source.starImage H K := by
    intro h
    exact ha.2.1 (LinearThree.Geometry.CoveredProduct.ResidualPlacement.le_of_star_le
      H K X hKH ha.1 hXp h)
  have hr : 1 < primeRank 3 (B ⊔ X : Subgroup G) :=
    rank_gt_one_of_external_cubic H K B X hKH hBK ha.1 hc hne ha.2.2.1
      (marked_borel_star_rank H K hKH S hn hmodel heven)
  have hmodels : Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) :=
    d.marked_cases.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  obtain ⟨_,hcov⟩ := covered_of_external_borel_rank H M L D B X (hBK.trans hKH) hBM
    ha.1 (hXD.trans hDM) d.theta hmodels d.ordinary_card hr
  exact hcov

/-- The two-core of the actual marked L₁*T* is the component Sylow intersection. -/
theorem source_external_five_core
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (ρ : Representation (ZMod 2) (Source.Hstar H) (SeedAction.Space H V₃ V₁))
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (d : SourceCalculation.EarlierLocalData H K X L (T : Subgroup G) V V₃ V₁ M S)
    (ha : ExternalXAlternative H K X)
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H)
    (W : Subrepresentation ρ)
    (coord : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation (Source.starImage H K) s) :
    (Source.starImage H (one L (T : Subgroup G) V₁) ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2 =
      Source.starImage H (T : Subgroup G) ⊓ Source.starImage H K := by
  let : (K.subgroupOf H).Normal := c.component.normal
  obtain ⟨P, hP⟩ := LinearThree.Geometry.ParabolicMarking.starImage_sylow H T
    (le_sup_right.trans c.component.local_overgroup.1.2)
  let D := one L (T : Subgroup G) V₁
  let A := Source.starImage H (D ⊔ (T : Subgroup G))
  let Ks := Source.starImage H K
  let : Ks.Normal := (inferInstance : (K.subgroupOf H).Normal).map _
    (QuotientGroup.mk'_surjective _)
  have hDH : D ≤ H := le_sup_left.trans c.component.local_overgroup.1.2
  have hTH : (T : Subgroup G) ≤ H := le_sup_right.trans c.component.local_overgroup.1.2
  have hmodel : ClassicalGroup.IsPSL Ks 2 (2 ^ 2) := psl_four_of_alternating coord.component
  obtain ⟨_, _, _, hs, _⟩ := Structure.MarkedBorel.selected_local_inputs
    L (T : Subgroup G) V V₁ V₃ X T.isPGroup' c.localSetup.line_stable
    d.marked_cases d.ordinary_card d.covered_action d.covered_factor d.seed_commutator
  let : Group.IsSolvable (D ⊔ (T : Subgroup G) : Subgroup G) := hs
  have hcov := source_external_covered_of_even_component S c d ha
    (by decide : 1 < 2) hmodel (by decide : Even 2)
  obtain ⟨a⟩ := d.covered_action hcov
  have h9 : 9 ∣ Nat.card A := (nine_dvd_star H D hDH
    (a.one_quotient_card (d.covered_factor hcov))).trans
      (card_dvd_of_le (map_mono (subgroupOf_mono H le_sup_left)))
  let : Group.IsSolvable ((D ⊔ (T : Subgroup G)).subgroupOf H) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe c.component.local_overgroup.1.2).toMonoidHom)
      (subgroupOfEquivOfLe c.component.local_overgroup.1.2).injective
  let : Group.IsSolvable A := Group.isSolvable_of_surjective
    ((QuotientGroup.mk' (pCore 2 H)).subgroupMap_surjective
      ((D ⊔ (T : Subgroup G)).subgroupOf H))
  have hPA : (P : Subgroup (Source.Hstar H)) ≤ A := by
    rw [hP]
    exact map_mono (subgroupOf_mono H le_sup_right)
  have hSA : (S : Subgroup Ks).map Ks.subtype ≤ A := by
    rw [d.sylow_inter]
    exact inf_le_left.trans (map_mono (subgroupOf_mono H le_sup_right))
  have hn := Structure.MarkedBorel.solvable_normalizes_borel Ks A S
    (by decide : 1 < 2) hmodel hSA
  have he := CriticalInputs.ParabolicCore.Coordinates.parabolic_core coord S A P hPA hn
    (d.sylow_inter.trans (by rw [hP])) h9
  have hA : A = Source.starImage H D ⊔ Source.starImage H (T : Subgroup G) := by
    unfold A Source.starImage
    rw [subgroupOf_sup hDH hTH, Subgroup.map_sup]
  rwa [hA, hP] at he


/-- The marked five-by-three action on any actual invariant source subspace
contradicts the original critical geometry. No equality W = U is used. -/
theorem source_external_movedFive_false
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    (c : FieldComponents.SourceContext T L V V₁ V₂ V₃ M G₁ H K)
    (act : LinearThree.SourceAction H V₃ V₁)
    (ha : ExternalXAlternative H K X)
    (hlocal : (Nonempty ((L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 6)) ∧ X = one L T V₁) ∨
      (Nonempty ((L ⧸ pCore 2 L) ≃* Atlas.Codes.HexEvenAutomorphisms) ∧ X = plus L T V₁))
    (s : Equiv.Perm (Fin 3) →* Source.Hstar H)
    (W : Subrepresentation act.representation)
    (coord : LinearTwo.FiveReconstruction.FullCoordinates W.toRepresentation (Source.starImage H K) s) :
    False := by
  let : (K.subgroupOf H).Normal := c.component.normal
  let : (Source.starImage H K).Normal :=
    c.component.normal.map _ (QuotientGroup.mk'_surjective _)
  have hT : Chapter1.IsSylowIn 2 (T : Subgroup G) H :=
    ⟨T.subtype (le_sup_right.trans c.component.local_overgroup.1.2),
      map_subgroupOf_eq_of_le (le_sup_right.trans c.component.local_overgroup.1.2)⟩
  let S := LocalBorel.sourceSylow H K (T : Subgroup G) hT
  let d := source_external_local_data c hlocal S (LocalBorel.sourceSylow_image H K _ hT)
  have hcore := source_external_five_core S act.representation c d ha s W coord
  have hqs := (SolvableSource.component_fitting_source c.localSetup c.maximal c.f9
    c.centralizer c.noncentral_core c.earlier1339 c.component.local_overgroup K
    c.component.component).2
  obtain ⟨w⟩ := CriticalSource.exists_selected_witness c.localSetup c.component.local_overgroup
    (c.f9 H c.component.local_overgroup) (by rw [←c.component.generated,sup_assoc])
    c.component.component c.component.normal hqs c.centralizer c.noncentral_core
    act.representation act.conjugation (coord.no_transvection_on_ambient W)
  have hcore' : Source.starImage H ((T : Subgroup G) ⊓ K) =
      (Source.starImage H (one L T V₁) ⊔ Source.starImage H (T : Subgroup G)).pCoreIn 2 :=
    (LocalBorel.star_intersection H K _ hT).trans hcore.symm
  have hplace : Source.starImage H w.alpha ≤ Source.starImage H ((T : Subgroup G) ⊓ K) := by
    rw [hcore']
    exact w.alpha_star_le_core (le_sup_left.trans c.component.local_overgroup.1.2)
      (le_sup_right.trans c.component.local_overgroup.1.2)
  exact LinearTwo.FiveReconstruction.tensor_branch_impossible_on_moved H K (one L T V₁)
    V₃ V₁ w.pair.Vgamma w.alpha ((T : Subgroup G) ⊓ K) T act.representation s W
    act.conjugation c.component.generated.symm coord (fun _ _ _ => w.rank_gt_one)
    w.actor_le w.conjugator rfl hplace hcore' (map_mono (subgroupOf_mono H inf_le_right)) w.quadratic

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.OriginalSource
