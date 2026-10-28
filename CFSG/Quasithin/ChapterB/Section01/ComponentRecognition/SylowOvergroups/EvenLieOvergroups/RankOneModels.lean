module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.SylowOvergroups.EvenLieOvergroups.RankOneReduction
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Linear
public import CFSG.Quasithin.ChapterF.Section01.RankOneBorels.Suzuki
public import Theory.SpecificGroups.SL2.EvenBorel
public import Theory.SpecificGroups.Suzuki.AbelianSubgroups

/-!
# Concrete linear and Suzuki proper Sylow overgroups

The matrix root centralizer bounds, together with exhaustive containment of
proper Sylow overgroups in the rank-one Borel, give the intrinsic generalized
Fitting bound. Actual model equivalences transfer it to the component, and
the literal B.1.13 local intersection then forces equality of the components.

The linear result includes the field of order two. The Suzuki result uses
m > 0, the simple parameter range; it does not identify the nonsimple group
Sz(2), an arbitrary central extension, or a unitary model with these carriers.

Source: Aschbacher–Smith B.1.13, printed p.74 (PDF p.85), and F.1.3(1),
printed pp.259–260. The imported matrix calculations are the upper-unipotent
SL₂ centralizer and Huppert–Blackburn XI.3.6 and XI.3.10 for Suzuki groups.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups

open CFSG.Quasithin.ChapterF.Source BenderSuzuki.Converse

/-- The binary projective linear Sylow bound follows from the upper-transvection centralizer. -/
theorem sylowCenterControl_psl2 (F : Type*) [Field F] [Finite F] [CharP F 2] :
    SylowCenterControl (PSL2 F) := by
  apply sylowCenterControl_of_equiv
    (MulEquiv.ofBijective (pi F) ⟨pi_injective, pi_surjective⟩).symm
  apply sylowCenterControl_of_selfCentralizing_sylow
    (Matrix.SpecialLinearGroup.upperUnipotentSylow F 2)
  rw [← Sylow.coe_coe, Matrix.SpecialLinearGroup.coe_upperUnipotentSylow,
    Theory.SpecificGroups.SL2.EvenBorel.unipotent_centralizer]

/-- The proper-overgroup bound for every actual binary PSL₂ model, including field order two. -/
theorem properSylowFittingBound_psl2 (F : Type*) [Field F] [Finite F]
    (n : ℕ) (hn : 0 < n) (hcard : Nat.card F = 2 ^ n)
    {G : Type*} [Group G] [Finite G] (e : G ≃* PSL2 F) :
    ProperSylowFittingBound G := by
  let := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact properSylowFittingBound_of_rankOne_equiv e
    (Linear.projective_facts F n hn hcard) (sylowCenterControl_psl2 F)

open BenderSuzuki.MatrixGroups

/-- The nontrivial Suzuki root-element centralizer controls every Sylow centralizer. -/
theorem sylowCenterControl_suzuki (m : ℕ) (hm : 0 < m) : SylowCenterControl (SuzukiMatrixGroup m) := by
  obtain ⟨S, hS⟩ := suzukiRootSubgroup_isSylow m hm
  apply sylowCenterControl_of_selfCentralizing_sylow S
  rw [← Sylow.coe_coe, hS]
  have hcard : 1 < Nat.card (SuzukiRootSubgroup m) := by
    rw [suzukiRootSubgroup_card m hm]
    exact one_lt_pow₀ (one_lt_pow₀ (by decide) (by omega)) (by decide)
  let : Nontrivial (SuzukiRootSubgroup m) := Finite.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨x, hx⟩ := exists_ne (1 : SuzukiRootSubgroup m)
  have hxne : (x : SuzukiMatrixGroup m) ≠ 1 := by
    intro h
    exact hx (Subtype.ext h)
  exact (centralizer_le (Set.singleton_subset_iff.mpr x.property)).trans
    (suzukiRootSubgroup_centralizer_le m hm x.property hxne)

/-- The proper-overgroup bound for the actual Suzuki groups in their simple parameter range. -/
theorem properSylowFittingBound_suzuki (m : ℕ) (hm : 0 < m)
    {G : Type*} [Group G] [Finite G] (e : G ≃* SuzukiMatrixGroup m) :
    ProperSylowFittingBound G :=
  properSylowFittingBound_of_rankOne_equiv e (suzuki_rankOneSylowFacts m) (sylowCenterControl_suzuki m hm)

variable {G : Type*} [Group G] [Finite G]

/-- Discharge the B.1.13 proper-overgroup premise when the containing component is binary PSL₂. -/
theorem eq_component_of_psl2 (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (F : Type*) [Field F] [Finite F] (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = 2 ^ n) (e : L ≃* PSL2 F) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_psl2 F n hn hcard e)

/-- Discharge the B.1.13 proper-overgroup premise when the containing component is a Suzuki group. -/
theorem eq_component_of_suzuki (K L : Subgroup G) (T : Sylow 2 G)
    (hL : IsComponent G L) (hLK : ⁅L, K⁆ = L)
    (hkind : IsQuasisimple K ∨ Nat.card K = 3)
    (hK : (K.subgroupOf (K ⊔ (T : Subgroup G))).IsSubnormal) (hKL : K ≤ L)
    (m : ℕ) (hm : 0 < m) (e : L ≃* SuzukiMatrixGroup m) : K = L :=
  eq_component_of_proper_sylow_fitting_bound K L T hL hLK hkind hK hKL
    (properSylowFittingBound_suzuki m hm e)

end CFSG.Quasithin.ChapterB.ComponentRecognition.SylowOvergroups
