module
public import Glauberman.PushingUpClassTwoChief
public import Glauberman.PushingUpCenterCovering

/-!
# The abelian-core branch of the original Main Hypothesis

If the original two-core Q is abelian, its central omega is Q and the
self-centralizing generalized Fitting hypothesis identifies the original
PSL₂(4) kernel with Q. The maximum abelian offender covers the Sylow image,
so it and Q generate the Sylow subgroup. The original center-covering
identity puts [Q,S] in Z(S), hence all Sylow commutators are central.

This closes the abelian-core branch of Niles, *Pushing-up in finite groups*
(1979), Sections 5–6, and leaves only nonabelian cores in the final Theorem B
class-bound input. It uses the original groups and quotient marking.
-/

public section
open Subgroup Theory.GroupTheory NoncentralChiefRefinement
open scoped IsMulCommutative
namespace Glauberman
universe u v
variable {H : Type u} {F : Type v} [Group H] [Finite H] [Field F] [Finite F]

/-- The abelian two-core branch of the original Main Hypothesis has Sylow
class at most two. -/
theorem original_psl2_four_class_le_two_of_core_abelian
    (hF : Nat.card F = 4) (S : Sylow 2 H) (α : MulAut S)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoInvariantNormal (S : Subgroup H) α)
    (hQ : IsMulCommutative (pCore 2 H)) : Group.nilpotencyClass S ≤ 2 := by
  let _ := hQ
  let _ := S.isPGroup'.isNilpotent
  have hZQ : centerIn (pCore 2 H) = pCore 2 H :=
    inf_eq_left.mpr (le_centralizer_iff_isMulCommutative.mpr hQ)
  have hV : omegaCenterIn (pCore 2 H) = pCore 2 H :=
    (original_psl2_four_omegaCenters_eq_centers hF S α hu K e hf hno).2.trans hZQ
  have hK : K = pCore 2 H := by
    have hk := (original_psl2_four_omegaAction_kernel_eq hF S hu K e hf
      hno.noCharacteristicNormal).1
    rw [omegaAction_kernel, hV] at hk
    exact hk.symm.trans (le_antisymm (by simpa only [hf] using centralizer_generalizedFitting_le H)
      (le_centralizer_iff_isMulCommutative.mpr hQ))
  obtain ⟨_,_,_,A,hA,_,he⟩ := original_psl2_four_omegaAction_sylow hF S hu K e hf
    hno.noCharacteristicNormal
  have hQS : pCore 2 H ≤ (S : Subgroup H) := pCore_isPGroup.le_sylow_of_normal S
  have hgen : A ⊔ pCore 2 H = (S : Subgroup H) := by
    have hh := congrArg (fun U : Subgroup (H ⧸ K) => U.comap (QuotientGroup.mk' K)) he
    simpa only [comap_map_eq, QuotientGroup.ker_mk', hK, sup_eq_left.mpr hQS] using hh
  have hcomm : ⁅pCore 2 H, (S : Subgroup H)⁆ ≤ centerIn (S : Subgroup H) := by
    have hh := original_psl2_four_center_commutator_covering hF S α hu K e hf hno
    rw [hZQ] at hh
    exact le_sup_left.trans hh.le
  have hnorm : (S : Subgroup H) ≤ normalizer (centerIn (S : Subgroup H) : Set H) :=
    (le_centralizer_iff.mpr inf_le_right).trans (Subgroup.centralizer_le_normalizer _)
  have hAA : ⁅A,A⁆ = ⊥ := commutator_self_eq_bot_iff.mpr hA.2.1
  have hAS : ⁅A, (S : Subgroup H)⁆ ≤ centerIn (S : Subgroup H) := by
    rw [commutator_comm]
    have hh := commutator_sup_le_of_relative_normal (S : Subgroup H) A (pCore 2 H)
      A (centerIn (S : Subgroup H)) hnorm hA.1 hQS (hAA.le.trans bot_le)
      ((commutator_mono le_rfl hA.1).trans hcomm)
    rwa [hgen] at hh
  have hSS : ⁅(S : Subgroup H), (S : Subgroup H)⁆ ≤ centerIn (S : Subgroup H) := by
    have hh := commutator_sup_le_of_relative_normal (S : Subgroup H) A (pCore 2 H)
      (S : Subgroup H) (centerIn (S : Subgroup H)) hnorm hA.1 hQS hAS hcomm
    rwa [hgen] at hh
  have hd : _root_.commutator S ≤ center S := by
    intro x hx
    have hh : (x : H) ∈ centerIn (S : Subgroup H) := by
      apply hSS
      rw [← map_subtype_commutator]
      exact mem_map_of_mem (S : Subgroup H).subtype hx
    exact mem_center_iff.mpr (fun y => Subtype.ext (hh.2 y y.property))
  apply Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp
  rw [Subgroup.lowerCentralSeries_succ, Subgroup.top_lowerCentralSeries_one]
  exact commutator_top_right_eq_bot_iff_le_center.mpr hd
/-- Only Main Hypothesis groups with nonabelian two-core remain in the
source class-bound callback for the complete original Theorem B. -/
theorem niles_theoremB_four_of_nonabelian_main_class
    (hF : Nat.card F = 4) (S : Sylow 2 H)
    (hu : Order.HasUniqueMaximalOver (S : Subgroup H) ⊤)
    (K : Subgroup H) [K.Normal]
    (e : (H ⧸ K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F)
    (hf : generalizedFitting H = pCore 2 H)
    (hno : NoCharacteristicNormal (S : Subgroup H))
    (hmain : ∀ (X : Type u) [Group X] [Finite X] (P : Sylow 2 X)
      (L : Subgroup X) [L.Normal],
      ((X ⧸ L) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) →
      generalizedFitting X = pCore 2 X →
      Order.HasUniqueMaximalOver (P : Subgroup X) ⊤ →
      (∃ β : MulAut P, NoInvariantNormal (P : Subgroup X) β) →
      ¬ IsMulCommutative (pCore 2 X) →
      Group.nilpotencyClass P ≤ 2) :
    Group.nilpotencyClass S = 2 ∧ Monoid.exponent S = 4 ∧
      Nonempty ((H ⧸ pCore 2 H) ≃* Matrix.SpecialLinearGroup (Fin 2) F) ∧
      ∃ eQ : (H ⧸ pCore 2 H) ≃* Representation.SL2FourNatural.SL,
        K = pCore 2 H ∧
        ∀ s : SeriesOn (pCore 2 H), s.noncentralCount = 1 ∧
          ∀ i : Fin s.series.length, ¬ s.Central i →
            Nat.card (s.Factor i) = 16 ∧
            ∃ f : s.Factor i ≃* Multiplicative Representation.SL2FourNatural.V,
              ∀ h x, (f (s.action i h x)).toAdd =
                Representation.specialLinearNatural 2
                  (eQ (QuotientGroup.mk' (pCore 2 H) h)) (f x).toAdd := by
  apply niles_theoremB_four_of_main_class hF S hu K e hf hno
  intro X _ _ P L _ eL hfX huP hb
  by_cases hc : IsMulCommutative (pCore 2 X)
  · obtain ⟨β,hβ⟩ := hb
    exact original_psl2_four_class_le_two_of_core_abelian hF P β huP L eL hfX hβ hc
  · exact hmain X P L eL hfX huP hb hc

end Glauberman
