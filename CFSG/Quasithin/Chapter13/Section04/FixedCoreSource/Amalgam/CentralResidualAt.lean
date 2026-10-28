module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.CentralResidual
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.PlanePairAt
public import Theory.GroupAction.MarkedCubicRecognition.CentralSeed
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam.SolvableSixAt

/-!
This guarded version uses earlier structure only at the original G,T.
All literal residuals, quotient maps and original source hypotheses are retained.

# The escaping central residual of the original solvable amalgam

Construct Y_Z as the full preimage of Z(O₃(X/O₂(X))) and take its literal
two-residual Y₂. The completed solvable alternative supplies the same
kernel and Heisenberg quotient used by the central fixed-space theorem.
Thus C_W(Y₂)=1 and the Y₂-orbit of Z equals [Z,Y₂], an elementary
subgroup of order sixteen. The original fixed line lies in W, so Y₂ escapes its
centralizer N_G(L). The residual is normal in X, not in the ambient group.

This proves the subgroup construction, rank-four movement and escape for the
second Goldschmidt triple in 13.4.7(3). The second triple, its kernel,
F.6 selection and the final chief-factor contradiction remain separate
obligations; the original two-index-two pair interface does not apply to it.
Source: Aschbacher--Smith 13.4.7(3), printed p.903.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V A B : Subgroup G}

/-- The literal Y₂ is normal in X, has the source central cubic image,
acts without fixed points on W, and moves the central seed to its full
order-sixteen orbit span; in particular it escapes N_G(L). -/
theorem original_pair_central_three_residual_at
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
    let Y₂ := (MarkedCubicRecognition.centralThreeResidual X).map X.subtype
    Y₂ ≤ X ∧ X ≤ normalizer (Y₂ : Set G) ∧
      (MarkedCubicRecognition.centralThreeResidual X).map
          (QuotientGroup.mk' (pCore 2 X)) =
        (center (pCore 3 (X ⧸ pCore 2 X))).map (pCore 3 (X ⧸ pCore 2 X)).subtype ∧
      W ⊓ centralizer (Y₂ : Set G) = ⊥ ∧
      conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) Y₂ =
        ⁅omegaOneCenterAmbient (T : Subgroup G),Y₂⁆ ∧
      Nat.card (⁅omegaOneCenterAmbient (T : Subgroup G),Y₂⁆ : Subgroup G) = 16 ∧
      ¬ Y₂ ≤ normalizer (L : Set G) := by
  obtain ⟨hk,⟨e⟩,_,_⟩ := original_pair_solvable_case_three_at h₀ h structural D m
    hTA hTB eA eB hne hindexL hindexA hindexB hcentral hs hcomm
  let X := A ⊔ B
  let W := conjugateSpanBy (omegaOneCenterAmbient (T : Subgroup G)) X
  let U := W.subgroupOf X
  let R := MarkedCubicRecognition.centralThreeResidual X
  let Y₂ := R.map X.subtype
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
  let : R.Normal := MarkedCubicRecognition.centralThreeResidual_normal
  have hn : X ≤ normalizer (Y₂ : Set G) := by
    have hh := R.le_normalizer_map X.subtype
    simpa only [normalizer_eq_top,←MonoidHom.range_eq_map,range_subtype] using hh
  have hfixed : W ⊓ centralizer (Y₂ : Set G) = ⊥ := by
    have hh := map_inf_centralizer_of_injective X.subtype X.subtype_injective U R
    rw [map_subgroupOf_eq_of_le hWX,
      MarkedCubicRecognition.centralThreeResidual_fixed_free S U hseed hZ hker e,Subgroup.map_bot] at hh
    exact hh
  obtain ⟨hspan,hcard⟩ := MarkedCubicRecognition.centralThreeResidual_seed_span S U hseed hZ hker e
  have hspanG := congrArg (fun P : Subgroup X => P.map X.subtype) hspan
  rw [map_conjugateSpanBy,Subgroup.map_commutator,homega] at hspanG
  rw [←card_map_of_injective X.subtype_injective,Subgroup.map_commutator,homega] at hcard
  refine ⟨map_subtype_le _,hn,MarkedCubicRecognition.centralThreeResidual_image e,
    hfixed,hspanG,hcard,?_⟩
  intro hYM
  have hFW : V ⊓ centralizer (L : Set G) ≤ W :=
    (LocalGeometry.fixed_le_original_omegaCenter_at h structural D m).trans (le_conjugateSpanBy _ _)
  have hFY : V ⊓ centralizer (L : Set G) ≤ centralizer (Y₂ : Set G) :=
    le_centralizer_iff.mp (hYM.trans (normalizer_component_le_fixed_centralizer_at h structural D m))
  exact m.fixed_ne_bot (bot_unique (hfixed ▸ le_inf hFW hFY))

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
