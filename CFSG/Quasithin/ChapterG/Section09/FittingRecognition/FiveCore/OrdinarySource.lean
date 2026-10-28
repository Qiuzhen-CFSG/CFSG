module
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore.Source
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.FiveCore.OrdinaryCubic
public import Theory.Representation.CommutingFiveFixedRank
public import Theory.GroupTheory.Fitting.PrimeSubgroups

/-!
# Eliminating the ordinary factors in the noncubic G.9.4 branch

A cubic element of F(G)A lies in F(G), since the image of the elementary
two-actor in G/F(G) has exponent two. Nilpotence then places that element
in O₃(G), which commutes with O₅(G). Faithfulness and irreducibility give
zero O₅(G)-invariants when this five-core is nontrivial. The whole space
and the fixed space of the commuting cubic therefore both have dimensions
divisible by four; so does its displacement.

Each genuine ordinary factor of the G.9.2 decomposition supplies a cubic
whose displacement is exactly two. This contradiction removes every ordinary
factor and supplies the existing fixed-space callback on its literal internal
decomposition. The final application discharges all inputs to G.9.4(2).
Source: Aschbacher–Smith G.9.4, printed pp.354–355.
-/

public section
namespace CFSG.Quasithin.ChapterG.Section09.FittingRecognition
open Subgroup NilpotentRigidity Theory.GroupTheory
open scoped commutatorElement
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]
  {K : GroupClass.{u}} {ρ : Representation (ZMod 2) G V} {A : Subgroup G} {m : ℕ}

namespace FiveCore

private theorem cubic_mem_fitting (h : Setup ρ A m) {x : G}
    (hx : x ∈ fittingSubgroup G ⊔ A) (h3 : x ^ 3 = 1) : x ∈ fittingSubgroup G := by
  let q := QuotientGroup.mk' (fittingSubgroup G)
  have hF : (fittingSubgroup G).map q = ⊥ := by
    exact (Subgroup.map_eq_bot_iff _).mpr (by rw [QuotientGroup.ker_mk'])
  have hq : q x ∈ A.map q := by
    have hh := mem_map_of_mem q hx
    rw [Subgroup.map_sup,hF,bot_sup_eq] at hh
    exact hh
  obtain ⟨a,ha,he⟩ := hq
  let _ := h.elementary
  have h2 : q x ^ 2 = 1 := by
    rw [← he, ← map_pow,elemPow_eq_one_of_isElementaryAbelian (p := 2) a ha,map_one]
  have hc : q x ^ 3 = 1 := by rw [← map_pow,h3,map_one]
  apply (QuotientGroup.eq_one_iff x).mp
  change q x = 1
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (by decide : Nat.Coprime 2 3)
    (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hc))

private theorem cubic_mem_threeCore (h : Setup ρ A m) {x : G}
    (hx : x ∈ fittingSubgroup G ⊔ A) (h3 : x ^ 3 = 1) : x ∈ pCore 3 G := by
  have hp : IsPGroup 3 (zpowers x) := by
    apply IsPGroup.of_card_dvd_pow (n := 1)
    simpa only [Nat.card_zpowers,pow_one] using orderOf_dvd_of_pow_eq_one h3
  exact hp.le_pCore_of_le_fitting (zpowers_le.mpr (cubic_mem_fitting h hx h3)) (mem_zpowers x)

omit [Finite G] in
private theorem threeCore_commutes_fiveCore {x : G} (hx : x ∈ pCore 3 G)
    (y : pCore 5 G) : Commute x (y : G) := by
  have hd : Disjoint (pCore 3 G) (pCore 5 G) :=
    pCore_isPGroup.disjoint_of_coprime pCore_isPGroup (by decide : Nat.Coprime 3 5)
  apply commutatorElement_eq_one_iff_commute.mp
  have hc : ⁅x,(y : G)⁆ ∈ (pCore 3 G) ⊓ (pCore 5 G) :=
    commutator_le_inf (pCore 3 G) (pCore 5 G) (commutator_mem_commutator hx y.property)
  exact Subgroup.mem_bot.mp (hd.eq_bot ▸ hc)

private theorem cubic_rank_four_dvd (h : FittingHypothesis K ρ A m)
    (hne : pCore 5 G ≠ ⊥) {x : G} (hx : x ∈ fittingSubgroup G ⊔ A)
    (h3 : x ^ 3 = 1) :
    4 ∣ Module.finrank (ZMod 2) (LinearMap.range (ρ x - LinearMap.id)) := by
  have hz := fiveCore_invariants_eq_bot h hne
  have hf : 4 ∣ Module.finrank (ZMod 2) (LinearMap.ker (ρ x - LinearMap.id)) :=
    Representation.four_dvd_fixedRank_of_commuting_five (ρ.comp (pCore 5 G).subtype)
      pCore_isPGroup hz (ρ x) (by
        intro y v
        change (ρ x * ρ y) v = (ρ y * ρ x) v
        rw [← map_mul,← map_mul,(threeCore_commutes_fiveCore
          (cubic_mem_threeCore h.toSetup hx h3) y).eq])
  have hd : 4 ∣ Module.finrank (ZMod 2) V := by
    simpa only [Representation.BinaryPrimeDegree.orderOf_two_mod_five] using
      Representation.BinaryOffender.orderOf_two_dvd_finrank_of_isPGroup
        (ρ.comp (pCore 5 G).subtype) (by decide : Nat.Prime 5) (by decide) pCore_isPGroup hz
  have he := (ρ x - LinearMap.id).finrank_range_add_finrank_ker
  omega


/-- A nontrivial five-core excludes every ordinary factor of the actual
internal decomposition: its cubic displacement would be both two and
divisible by four. -/
theorem ordinaryFactorsFixed_of_fiveCore_ne_bot (h : FittingHypothesis K ρ A m)
    (hne : pCore 5 G ≠ ⊥) : OrdinaryFactorsFixed ρ A := by
  intro H hH d i hi
  obtain ⟨g,hg3,hgdim⟩ := ordinary_factor_rank_two_cubic ρ h.faithful d.internal i
    (d.ordinary_factor i (Or.inr hi))
  have hx : (g : G) ∈ fittingSubgroup G ⊔ A :=
    hH (d.internal.factor_le i g.property)
  have hd := cubic_rank_four_dvd h hne hx hg3
  rw [hgdim] at hd
  norm_num at hd

/-- The noncubic source premise provides the five-core used to remove the
ordinary-factor callback. -/
theorem ordinaryFactorsFixed_from_source (h : FittingHypothesis K ρ A m)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) :
    OrdinaryFactorsFixed ρ A :=
  ordinaryFactorsFixed_of_fiveCore_ne_bot h (fiveCore_ne_bot h (nilpotentRigidityInput ρ) hn)

end FiveCore

/-- The original noncubic branch of G.9.4, with the G.9.2 decomposition,
ordinary-factor action and linear five-normalizer all discharged. -/
theorem caseTwo_from_source (h : FittingHypothesis K ρ A m) (hm : 0 < m)
    (hn : ¬ IsPGroup 3 (⁅fittingSubgroup G, A⁆ : Subgroup G)) : CaseTwo ρ A m :=
  caseTwo_of_ordinaryFactorsFixed h hm hn (FiveCore.ordinaryFactorsFixed_from_source h hn)

end CFSG.Quasithin.ChapterG.Section09.FittingRecognition
