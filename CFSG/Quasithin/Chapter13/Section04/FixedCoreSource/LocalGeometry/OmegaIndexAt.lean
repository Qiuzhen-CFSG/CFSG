module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.OmegaSourceAt
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry.CentralFourAt
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.ReducedChosenMovementCore
public import Theory.GroupTheory.ReducedNormal.ComponentSeedSplitting
public import Theory.GroupTheory.NormalizedSupCard

/-!
# The original omega decomposition and fixed index at the same G,T

The escaping omega point gives L=[L,J(T)]. Hence J(T) moves the chosen V,
and the proved B.5.1 reduced-action theorem gives [R₂(LT),L]=V. The
reduced omega span splits into its moved and central parts. Intersecting
that splitting with the original omega-center gives Z=(V∩Z)C_Z(L).
The actual escaping point forces |V∩Z|=4, while |C_V(L)|=2; the subgroup
product formula therefore gives |Z:C_Z(L)|=2.

All groups are the original embedded subgroups. This works for both
central-cover rows and assumes no full-omega bound or fixed index.
The earlier structural and recognition inputs are used only at the same
G,T, including their original chosen-module guards. FixedModuleAt applies
these results to the original nonzero fixed-part premise, in both rows.
Source: Aschbacher--Smith 13.4.3(2--3), printed p.897, using B.5.1(2)
and B.2.14, printed pp.99 and78.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (h₀ : Hypothesis1331 T L)
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (earlier : Theorem12213At KnownSimple.IsKnownSimple T)
include h₀ h structural D m earlier

/-- The full reduced commutator is exactly the chosen augmentation core. -/
theorem original_reduced_commutator_at :
    ⁅(ReducedModule (L ⊔ (T : Subgroup G))).map (L ⊔ (T : Subgroup G)).subtype,L⁆ = V := by
  have hgen := original_core_thompson_generation_at h₀ h structural D m earlier
  have hmove : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
    intro hc
    have hLC : L ≤ centralizer (V : Set G) := hgen.symm.le.trans
      ((commutator_mono le_rfl hc).trans
        (le_normalizer_iff_commutator_le_right.mp
          (D.normalizes.trans (normalizer_le_normalizer_centralizer V))))
    exact D.ne_bot (D.eq_commutator.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hLC)))
  exact le_antisymm
    (Chapter12.Section02.RecognitionSource.ReducedChosenMovement.reduced_commutator_le_chosen_of_thompson_movement
      h D m.fixed_ne_bot hmove)
    (D.eq_commutator.le.trans (commutator_mono D.le_reduced le_rfl))

/-- Original 13.4.3(3), on the whole Sylow omega-center. -/
theorem original_omega_decomposition_at :
    omegaOneCenterAmbient (T : Subgroup G) =
      (V ⊓ omegaOneCenterAmbient (T : Subgroup G)) ⊔
      (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)) := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let H := L ⊔ (T : Subgroup G)
  let F := Z ⊓ centralizer (L : Set G)
  let W := conjugateSpanBy Z H
  have hZT : Z ≤ (T : Subgroup G) := fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).1
  have hZC : Z ≤ centralizer (T : Set G) := fun _ hz => ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2
  have hchar : centralizer (pCore 2 H : Set H) ≤ pCore 2 H :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (h.simpleQTKE.evenCharacteristic T)
      ⟨h.maximal_faithful.1.1.2.2,fun _ hx => (le_sup_right : (T : Subgroup G) ≤ H) hx⟩)
  let : IsElementaryAbelian 2 Z := omegaOneCenterAmbient_elementaryAbelian _
  have hred := reduced_conjugateSpan_of_sylow_central T H Z le_sup_right hZT hZC hchar
  have hWH : W ≤ H := conjugateSpanBy_le_self (hZT.trans le_sup_right)
  have hWR : W ≤ (ReducedModule H).map H.subtype := by
    rw [←map_subgroupOf_eq_of_le hWH]
    exact map_mono hred.le_reducedPSubgroup
  have hspan : W = conjugateSpanBy Z L :=
    conjugateSpanBy_sup_of_normalizes_seed Z L (T : Subgroup G)
      ((le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _))
      D.sylow_normalizes_component
  have hm : ⁅W,L⁆ ≤ V := (commutator_mono hWR le_rfl).trans
    (original_reduced_commutator_at h₀ h structural D m earlier).le
  have hs := omegaCenter_component_span_split T L D.sylow_normalizes_component hchar
  rw [←hspan] at hs
  have hW : W ≤ V ⊔ F := hs.le.trans (sup_le_sup hm le_rfl)
  have hVF : V ≤ normalizer (F : Set G) :=
    (le_centralizer_iff.mp ((inf_le_left.trans hZC).trans (centralizer_le D.le_sylow))).trans
      (Subgroup.centralizer_le_normalizer _)
  apply le_antisymm ?_ (sup_le inf_le_right inf_le_left)
  intro z hz
  have hzprod : z ∈ (V : Set G) * (F : Set G) := by
    rw [←coe_mul_of_left_le_normalizer_right V F hVF]
    exact hW (le_conjugateSpanBy Z H hz)
  obtain ⟨v,hv,f,hf,rfl⟩ := hzprod
  have hvZ : v ∈ Z := by
    have he := Z.mul_mem hz (Z.inv_mem hf.1)
    simpa only [mul_inv_cancel_right] using he
  exact mul_mem_sup ⟨hv,hvZ⟩ hf

/-- Original 13.4.3(2): the fixed subgroup has index two in the whole omega-center. -/
theorem original_omega_fixed_index_at :
    (omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G)).relIndex
      (omegaOneCenterAmbient (T : Subgroup G)) = 2 := by
  let Z := omegaOneCenterAmbient (T : Subgroup G)
  let F := Z ⊓ centralizer (L : Set G)
  let A := V ⊓ Z
  have hZ : Z = A ⊔ F := original_omega_decomposition_at h₀ h structural D m earlier
  obtain ⟨z,hz1,hzT,_,hzout⟩ := exists_nonfixed_omega_escape_at h₀ h structural D m earlier
  have hA : Nat.card A = 4 := m.central_four_card_eq_four_at h structural z hz1 hzT hzout
  have hfixed : V ⊓ centralizer (L : Set G) ≤ Z := by
    intro x hx
    rcases (m.fixed_iff ⟨x,hx.1⟩).mp hx.2 with he | he
    · have he' : x = 1 := congrArg Subtype.val he
      exact he' ▸ one_mem Z
    · have he' : x = m.constant.val := congrArg Subtype.val he
      exact he' ▸ (m.constant_mem_central_four_at h structural).2
  have hinf : A ⊓ F = V ⊓ centralizer (L : Set G) := by
    apply le_antisymm
    · exact le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right)
    · intro x hx
      exact ⟨⟨hx.1,hfixed hx⟩,hfixed hx,hx.2⟩
  have hn : F ≤ normalizer (A : Set G) := by
    apply le_trans _ (Subgroup.centralizer_le_normalizer _)
    apply le_trans _ (centralizer_le (show (A : Set G) ⊆ (T : Set G) from
      fun _ hx => D.le_sylow hx.1))
    exact fun _ hx => ((mem_omegaOneCenterAmbient_iff _ _).mp hx.1).2.2
  have hc := card_mul_eq_card_inf_mul_card_sup_of_normalizes A F hn
  rw [←hZ,hinf,hA,m.card_fixed] at hc
  have hi := relIndex_mul_card_of_le (show F ≤ Z from inf_le_left)
  have hpos : 0 < Nat.card F := Nat.card_pos
  change F.relIndex Z = 2
  nlinarith

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.LocalGeometry
