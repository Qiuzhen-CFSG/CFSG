module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Geometry.ChiefFactors
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.LocalProduct.ShortBlock
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Displacement
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds

/-!
# The three-factor budget for the original short block

For the literal five-dimensional chosen module, shortness identifies
[O₂(L),L] with V. Thus a cubic's movement on O₂(L) equals its movement
on V and contributes at most two binary chief factors. Intersecting with
the actual second residual preserves the cubic fixed index, since O₂(L)
normalizes that residual. Its marked A₄ quotient adds exactly one factor.

The final theorem constructs the A₄ action from the actual inner
second-parabolic image. LinearBlockSource applies this budget with the
literal identity K₂=L₂, discharging the numerical premise of the block
exclusion in Aschbacher–Smith 13.4.7(4), printed p.903. No block alternative
or preceding trichotomy is asserted here.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
open Chapter12.Section02
open Section08.TransvectionRecognition.Component.ModelExtension
open Theory.SpecificGroups.SymmetricSix.ResidualPairRecognition
open NoncentralChiefRefinement
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- In the original short-block branch, every complete chief series of the
marked second residual has at most three noncentral binary factors. -/
theorem marked_plane_residual_short_chief_budget
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (K : Subgroup G) (hKL : K ≤ L) (hTK : (T : Subgroup G) ≤ normalizer (K : Set G))
    (f : K →* A) (hf : Function.Surjective f)
    (hmark : ∀ k : K, (m.quotient (QuotientGroup.mk' (centralCore L)
      (inclusion hKL k))).val = synthemeHom (f k))
    (s : ChiefSeries K) (h0 : s.head = ⊥) (h1 : s.last = ⊤) :
    s.noncentralTwoCount ≤ 3 := by
  let Q := L.pCoreIn 2
  have hk : f.ker = Q.subgroupOf K := by
    ext k
    change f k = 1 ↔ k.val ∈ Q
    rw [←synthemeHom_injective.eq_iff,map_one,←hmark k]
    change (m.quotient (QuotientGroup.mk' (centralCore L) (inclusion hKL k))).val =
      (1 : alternatingGroup (Fin 6)).val ↔ _
    rw [Subtype.val_injective.eq_iff,m.quotient.map_eq_one_iff,
      QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff,
      Solvable.centralCore_eq_twoCore_of_short_core_marking D m hb]
    exact (mem_map_iff_mem L.subtype_injective).symm
  have hp : IsPGroup 2 f.ker := by
    rw [hk]
    exact (isPGroup_pCoreIn 2 L).comap_subtype
  have hd : 3 ∣ Nat.card K := dvd_trans (b := Nat.card A) (by
    rw [nat_card_alternatingGroup]; norm_num) (card_dvd_of_surjective f hf)
  obtain ⟨E₀,hE₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := K) 3
    (n := 1) (by simpa using hd)
  let E := E₀.map K.subtype
  have hEK : E ≤ K := map_subtype_le E₀
  have hE : Nat.card E = 3 := (card_map_of_injective K.subtype_injective).trans
    (by simpa using hE₀)
  have hEL : E ≤ L := hEK.trans hKL
  have hQL : L ≤ normalizer (Q : Set G) := L.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hVL : L ≤ normalizer (V : Set G) := D.normalizes
  let : (V.subgroupOf Q).Normal :=
    normal_subgroupOf_of_le_normalizer ((L.pCoreIn_le 2).trans hVL)
  have hcomm : ⁅Q,L⁆ = V := by
    rw [←Solvable.chosen_eq_block_layer D hb]
    change ⁅(pCore 2 L).map L.subtype,L⁆ = (⁅pCore 2 L,⊤⁆ : Subgroup L).map L.subtype
    rw [map_commutator,←MonoidHom.range_eq_map,range_subtype]
  have he := CubicComparison.length_eq_of_commutator_le E Q V
    (IsPGroup.of_card (n := 1) (by simpa using hE)) (isPGroup_pCoreIn 2 L)
    D.le_componentCore (hEL.trans hQL) (hEL.trans hVL)
    ((commutator_mono le_rfl hEL).trans hcomm.le)
  have hv : conjugationCubicLength E V ≤ 2 := by
    have hh := CubicComparison.length_le_log_card E V
    rw [m.card_module] at hh
    exact hh
  have hQT : Q ≤ (T : Subgroup G) :=
    (isPGroup_pCoreIn 2 L).le_sylow_of_normalized T
      (D.sylow_normalizes_component.trans
        (normalizer_le_normalizer_characteristic_image L (pCore 2 L)))
  have hinter := CubicComparison.intersection_length_eq E Q K
    (IsPGroup.of_card (n := 1) (by simpa using hE)) (isPGroup_pCoreIn 2 L)
    hEK (hQT.trans hTK) (hKL.trans hQL)
  have hEI : E.subgroupOf K = E₀ :=
    comap_map_eq_self_of_injective K.subtype_injective E₀
  have hlen := CubicComparison.length_subgroupOf E (Q ⊓ K) K hEK inf_le_right
  rw [inf_subgroupOf_right,←hk,hEI] at hlen
  have hc := CubicComparison.alternatingFour_count f hf hp E₀
    (by simpa using hE₀) s h0 h1
  omega
/-- The source second-parabolic marking supplies the short-block budget on
its embedded two-residual, with no chief-count premise. -/
theorem second_parabolic_residual_short_chief_budget
    (D : ChosenModule T L V) (m : CoreMarking D) (hb : ChapterC.IsShort L)
    (J : Subgroup G) (hJL : J ≤ L)
    (hTJ : (T : Subgroup G) ≤ normalizer (J : Set G))
    (himage : (J.subgroupOf L).map
      ((alternatingGroup (Fin 6)).subtype.comp
        (m.quotient.toMonoidHom.comp (QuotientGroup.mk' (centralCore L)))) =
      Theory.SpecificGroups.SymmetricSix.synthemeStabilizer ⊓ alternatingGroup (Fin 6))
    (s : ChiefSeries ((pResidual 2 J).map J.subtype))
    (h0 : s.head = ⊥) (h1 : s.last = ⊤) : s.noncentralTwoCount ≤ 3 := by
  obtain ⟨f,hf,hm⟩ := Solvable.second_parabolic_residual_action D m J hJL himage
  exact marked_plane_residual_short_chief_budget D m hb _ ((map_subtype_le _).trans hJL)
    (hTJ.trans (normalizer_le_normalizer_characteristic_image J (pResidual 2 J)))
    f hf hm s h0 h1

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Amalgam
