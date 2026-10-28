module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.Statement
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MinimalPlanes
public import Theory.Representation.BinaryOffender.InvolutionRatio
public import Theory.Representation.BinaryOffender.DualDisplacement
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.ElementaryAbelian.Injective
/-!
# Small-support and Fitting branches of B.5.13

An involution has the same fixed-space codimension on a binary module and
its actual dual. Thus a dual offender of rank at most two, or an involution
whose dual displacement lies in a two-dimensional support, gives quadratic
ratio at most two on the original module.

The symmetric-three alternative and the minimal-offender Fitting planes
supply such supports. If an odd normal subgroup lies in the Fitting subgroup
and its centralizer has two-rank at most two, every dual FF action is handled:
either a minimal best offender moves the Fitting subgroup, or a minimal best
offender lies in that centralizer. No splitting of the original module is used.
Source: Aschbacher–Smith B.1.9 and B.5.13, printed pp.71 and110.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.SourceB513
open SourceInduction QuasisimpleSource
variable {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- An actual involution with a dual support of dimension at most two gives the bound. -/
theorem quadraticRatio_le_two_of_dual_support (ρ : Representation (ZMod 2) D V)
    (A : Subgroup D) (hdim : Module.finrank (ZMod 2) (subspaceCommutator ρ.dual ⊤ A) ≤ 2)
    (t : D) (htA : t ∈ A) (ht : orderOf t = 2) : quadraticRatio ρ ≤ 2 := by
  have hb : fixedCodim ρ (zpowers t) ≤ 2 := by
    rw [← fixedCodim_zpowers_dual ρ t, fixedCodim_zpowers_eq_displacement_rank]
    apply (Submodule.finrank_mono ?_).trans hdim
    rintro v ⟨w,rfl⟩
    exact Submodule.subset_span ⟨t,htA,w,Submodule.mem_top,rfl⟩
  obtain ⟨hA,hr,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ t ht
  exact (quadraticRatio_le_two_iff ρ).mpr ⟨zpowers t,hA,hquad,by simpa [hr] using hb⟩

/-- A dual offender of rank at most two supplies a suitable cyclic actor. -/
theorem quadraticRatio_le_two_of_dual_offender_rank (ρ : Representation (ZMod 2) D V)
    {A : Subgroup D} (hA : IsOffender ρ.dual A) (hr : rank A ≤ 2) :
    quadraticRatio ρ ≤ 2 := by
  obtain ⟨t,ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA.1.1
  let : IsElementaryAbelian 2 A := hA.1.2
  have ht2 : (t : D)^2 = 1 := elemPow_eq_one_of_isElementaryAbelian (t : D) t.property
  have ho : orderOf (t : D) = 2 := orderOf_eq_prime ht2 (fun he => ht (Subtype.ext he))
  have hspace : fixedSpace ρ.dual A ≤ fixedSpace ρ.dual (zpowers (t : D)) := by
    intro v hv a
    exact hv ⟨a,(zpowers_le.mpr t.property) a.property⟩
  have hdim := Submodule.finrank_mono hspace
  have h1 := fixedCodim_add_finrank ρ.dual A
  have h2 := fixedCodim_add_finrank ρ.dual (zpowers (t : D))
  have hb : fixedCodim ρ (zpowers (t : D)) ≤ 2 := by
    rw [← fixedCodim_zpowers_dual ρ (t : D)]
    have hh := hA.2
    omega
  obtain ⟨he,heRank,hquad,_⟩ := involution_actor_rank_and_fixedCodim ρ (t : D) ho
  exact (quadraticRatio_le_two_iff ρ).mpr
    ⟨zpowers (t : D),he,hquad,by simpa [heRank] using hb⟩

/-- The literal symmetric-three source alternative gives the bound. -/
theorem quadraticRatio_le_two_of_dual_symmetricThree (ρ : Representation (ZMod 2) D V)
    (c : SymmetricThreeCase ρ.dual) : quadraticRatio ρ ≤ 2 := by
  let e : D ≃* Equiv.Perm (Fin 3) := c.equiv
  let t : D := e.symm (Equiv.swap 0 1)
  have ht : orderOf t = 2 := by
    exact (e.symm.orderOf_eq (Equiv.swap 0 1)).trans
      (orderOf_eq_prime (by simp [pow_two]) (by decide))
  apply quadraticRatio_le_two_of_dual_support ρ ⊤ ?_ t (mem_top t) ht
  simpa only [moved] using c.dimension.le

/-- A minimal-offender Fitting plane controls the original action. -/
theorem quadraticRatio_le_two_of_dual_minimalFittingPlane (ρ : Representation (ZMod 2) D V)
    {A : Subgroup D} (c : FittingStructure.MinimalFittingPlane ρ.dual A) :
    quadraticRatio ρ ≤ 2 := by
  have hA : A ≠ ⊥ := by
    intro he
    have hc := c.actor_card
    rw [he] at hc
    simp at hc
  obtain ⟨t,ht⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA
  have ht2 : (t : D)^2 = 1 := by
    have hp := pow_card_eq_one' (x:=t)
    rw [c.actor_card] at hp
    exact congrArg Subtype.val hp
  have ho : orderOf (t : D) = 2 := orderOf_eq_prime ht2 (fun he => ht (Subtype.ext he))
  apply quadraticRatio_le_two_of_dual_support ρ A ?_ t t.property ho
  have hh : subspaceCommutator ρ.dual ⊤ A ≤
      subspaceCommutator ρ.dual ⊤ (⁅fittingSubgroup D,A⁆ ⊔ A) := by
      apply Submodule.span_mono
      rintro v ⟨a,ha,w,hw,rfl⟩
      exact ⟨a,(show A ≤ ⁅fittingSubgroup D,A⁆ ⊔ A from le_sup_right) ha,w,hw,rfl⟩
  rw [← c.support_eq] at hh
  exact (Submodule.finrank_mono hh).trans_eq c.dimension

/-- The proved B.1.9 local plane theorem discharges the moving-Fitting branch. -/
theorem quadraticRatio_le_two_of_dual_fittingMoved (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ.dual) (hc : pCore 2 D = ⊥)
    (hm : FittingStructure.fittingMoved ρ.dual ≠ ⊥) : quadraticRatio ρ ≤ 2 := by
  obtain ⟨A,hA,hn⟩ := (FittingStructure.fittingMoved_ne_bot_iff ρ.dual).mp hm
  obtain ⟨c⟩ := FittingStructure.localPlaneLaw ρ.dual hf hc A hA hn
  exact quadraticRatio_le_two_of_dual_minimalFittingPlane ρ c

/-- An actual Fitting subgroup with a small centralizer handles every dual FF action. -/
theorem quadraticRatio_le_two_of_fitting_centralizer_rank (ρ : Representation (ZMod 2) D V)
    (hf : Function.Injective ρ.dual) (hc : pCore 2 D = ⊥) (hff : IsFFModule ρ.dual)
    (N : Subgroup D) (hNF : N ≤ fittingSubgroup D)
    (hr : primeRank 2 (centralizer (N : Set D)) ≤ 2) : quadraticRatio ρ ≤ 2 := by
  by_cases hm : FittingStructure.fittingMoved ρ.dual = ⊥
  · obtain ⟨A,hA⟩ := (isFFModule_iff_exists_bestOffender ρ.dual).mp hff
    obtain ⟨B,hB,_⟩ := hA.exists_minimal ρ.dual
    have hJ : FittingStructure.minimalGenerated ρ.dual ≤
        centralizer (fittingSubgroup D : Set D) := by
      exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hm)
    have hBN : B ≤ centralizer (N : Set D) := by
      exact (FittingStructure.minimal_le ρ.dual hB).trans
        (hJ.trans (centralizer_le hNF))
    have hrB : rank B ≤ 2 := by
      let : IsElementaryAbelian 2 B := hB.1.1.2
      have hel : IsElementaryAbelian 2 (B.subgroupOf (centralizer (N : Set D))) :=
        IsElementaryAbelian.of_injective (subgroupOfEquivOfLe hBN).toMonoidHom
          (subgroupOfEquivOfLe hBN).injective
      have hb := (primeRank_le_iff_elementary_card_le (centralizer (N : Set D))).mp hr
        (B.subgroupOf (centralizer (N : Set D))) hel
      have hh := Nat.log_mono_right (b := 2) hb
      change rank (B.subgroupOf (centralizer (N : Set D))) ≤ _ at hh
      simpa only [rank_subgroupOf hBN, Nat.log_pow (by decide : 1 < 2)] using hh
    exact quadraticRatio_le_two_of_dual_offender_rank ρ (hB.1.isOffender ρ.dual) hrB
  · exact quadraticRatio_le_two_of_dual_fittingMoved ρ hf hc hm

end CFSG.Quasithin.ChapterB.SourceB513
