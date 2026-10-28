module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableSix
public import Theory.GroupAction.MarkedCubicRecognition.BinaryDegree
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableThompson
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.EqualCoreSourceAt

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# The complete solvable noncommuting alternative of 13.4.7(1)

Equal vertex cores give commuting residual actions, so they are excluded
in this branch. The literal X/O₂(X) is the marked Heisenberg extension and
its kernel on the original omega span is exactly O₂(X). The common fixed
space is the original central four-group. The extraspecial degree and
Sylow fixed-space calculation therefore give order 64 for the whole span.
Together with the proved ordinary Thompson normality, these are all four
assertions of alternative (1iii), without a supplied degree, model, kernel,
or unequal-core premise.

The earlier Chapter12/13.3 hypotheses and the original relative-centralizer
and prime-to-three residual clause remain explicit. Excluding this
alternative for the literal marked plane pair still requires the second
amalgam on printed pp.903--904; it is not a consequence of this theorem.
Source: Aschbacher--Smith 13.4.7(1iii), printed pp.901--902.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam

open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- All four assertions of the solvable noncommuting alternative (1iii),
for the original admitted pair. Equal vertex cores are excluded internally. -/
theorem original_pair_solvable_case_three_at
    (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (hTA : (T : Subgroup G) ≤ A) (hTB : (T : Subgroup G) ≤ B)
    (eA : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eB : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3)) (hne : A ≠ B)
    (hindexL : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexA : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (A : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hindexB : (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (B : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2)
    (hcentral : let X := A ⊔ B
      let Z := omegaOneCenterAmbient (T : Subgroup G)
      let K₁ := (pResidual 2 A).map A.subtype
      let K₂ := (pResidual 2 B).map B.subtype
      let C₁ := X ⊓ centralizer ((Z ⊓ centralizer (K₁ : Set G) : Subgroup G) : Set G)
      let C₂ := X ⊓ centralizer ((Z ⊓ centralizer (K₂ : Set G) : Subgroup G) : Set G)
      X ∈ Chapter1.HOver G (T : Set G) →
        (K₁.subgroupOf C₁).Normal ∧ (K₂.subgroupOf C₂).Normal ∧
        ((primeToResidual 3 C₁).map C₁.subtype = K₁ ∨
          (primeToResidual 3 C₂).map C₂.subtype = K₂))
    (hs : Group.IsSolvable (A ⊔ B : Subgroup G))
    (hcomm : ¬ ⁅(pResidual 2 A).map A.subtype,(pResidual 2 B).map B.subtype⁆ ≤
      centralizer (conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) (A ⊔ B) : Set G)) :
    let X := A ⊔ B
    let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
    X ⊓ centralizer (W : Set G) = X.pCoreIn 2 ∧
      Nonempty ((X ⧸ pCore 2 X) ≃* MarkedCubicRecognition.HeisenbergExtension) ∧
      Nat.card W = 64 ∧ X ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  have hcores : A.pCoreIn 2 ≠ B.pCoreIn 2 := by
    intro he
    have hbound := (original_pair_equal_core_solvable_at h structural D m
      hTA hTB eA eB hne hindexL hindexA hindexB hcentral h₀ hs he).2.1
    let K₁ := (pResidual 2 A).map A.subtype
    have hAK : A ≤ normalizer (K₁ : Set G) := by
      have hh := (pResidual 2 A).le_normalizer_map A.subtype
      simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
    have hKcore : K₁.pCoreIn 2 ≤ A.pCoreIn 2 :=
      pCoreIn_mono_of_normalizes (map_subtype_le _) hAK
    have hnormal : A ⊔ B ≤ normalizer (A.pCoreIn 2 : Set G) := by
      apply sup_le
      · exact A.le_normalizer.trans (normalizer_le_normalizer_characteristic_image A (pCore 2 A))
      · rw [he]
        exact B.le_normalizer.trans (normalizer_le_normalizer_characteristic_image B (pCore 2 B))
    have hcore : A.pCoreIn 2 ≤ (A ⊔ B).pCoreIn 2 :=
      le_pCoreIn_of_normalizes (isPGroup_pCoreIn 2 A)
        ((A.pCoreIn_le 2).trans le_sup_left) hnormal
    have hkT := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).2.2.2
    exact hcomm (hbound.trans (inf_le_left.trans (hKcore.trans
      (hcore.trans (hkT.symm.le.trans inf_le_right)))))
  obtain ⟨hk,⟨e⟩⟩ := original_pair_solvable_noncommuting_model h₀ D m
    hTA hTB eA eB hne hindexA hindexB hcentral hcores hs hcomm
  have hJ := original_pair_solvable_thompson_normal h₀ D m hTA hTB eA eB hne
    hindexA hindexB hcentral hcores hs hcomm
  refine ⟨hk,⟨e⟩,?_,hJ⟩
  let X := A ⊔ B
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let U := W.subgroupOf X
  have hTX : (T : Subgroup G) ≤ X := hTA.trans le_sup_left
  let S := T.subtype hTX
  have hWX : W ≤ X := conjugateSpanBy_le (fun z hz =>
    hTX ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1) X.le_normalizer
  have hr := (original_pair_action_kernel h₀ D m hTA hTB eA eB hne hindexA hindexB).1
  have hker : centralizer (U : Set X) = pCore 2 X := by
    apply map_injective X.subtype_injective
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective
      (⊤ : Subgroup X) U
    have hm : (centralizer (U : Set X)).map X.subtype = X ⊓ centralizer (W : Set G) := by
      simpa only [U,top_inf_eq,←MonoidHom.range_eq_map,range_subtype,
        map_subgroupOf_eq_of_le hWX] using hh.symm
    exact hm.trans hk
  have homega : (omegaOneCenterAmbient (S : Subgroup X)).map X.subtype =
      omegaOneCenterAmbient (T : Subgroup G) := by
    rw [←omegaOneCenterAmbient_map_injective X.subtype X.subtype_injective,
      Sylow.coe_subtype,map_subgroupOf_eq_of_le hTX]
  have hseed : omegaOneCenterAmbient (S : Subgroup X) ≤ U := by
    intro z hz
    exact le_conjugateSpanBy _ _ (homega ▸ mem_map_of_mem X.subtype hz)
  have hZ : Nat.card (omegaOneCenterAmbient (S : Subgroup X)) = 4 := by
    rw [←card_map_of_injective X.subtype_injective,homega]
    exact (original_pair_source_seed_at h structural D m hTA hTB eA eB hne
      hindexL hindexA hindexB hcentral).2.2.1
  let : U.Normal := hr.normal
  let : IsElementaryAbelian 2 U := hr.elementary
  have hc := MarkedCubicRecognition.omega_seed_card S U hseed hZ hker e
  rw [natCard_subgroupOf_eq W X hWX] at hc
  exact hc

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
