module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.LocalNormality
public import CFSG.Quasithin.Chapter1.Section02.Adequate.Chains

/-!
# Normal odd radicals in local overgroups

In the first reduction of 13.1.4, normality of Ξₚ(L) in a larger local
component K implies that K/O₂(K) is not quasisimple. The restricted map
Ξₚ(L) → K/O₂(K) has kernel O₂(Ξₚ(L)), so its normal p-image forces p to
divide the Fitting subgroup. Here p > 3, whereas the quasisimple branch of
A.3.6 has Fitting subgroup of order one or three. This is a structural
argument on the actual quotients, independent of a model-list certificate.

The source's preceding proof of normality uses 1.3.4 and 13.1.2(3).
Those earlier embedding and exclusion implications are not asserted here.
Source: Aschbacher--Smith, combined manuscript (1 March 2004),
13.1.4, printed p.867, and the setup of 13.1.7, printed p.868.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter1 CFSG.Quasithin.Chapter1.Section02

namespace CFSG.Quasithin.Chapter13.Section01

variable {G : Type*} [Group G]

/-- The literal restriction of the quotient map of the larger subgroup. -/
def normalRadicalMap {X K : Subgroup G} (hXK : X ≤ K) : X →* XiQuotient K :=
  (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hXK)

/-- Relative normality identifies the kernel with the radical's own two-core. -/
theorem normalRadicalMap_ker {X K : Subgroup G} (hXK : X ≤ K)
    (hN : (X.subgroupOf K).Normal) : (normalRadicalMap hXK).ker = pCore 2 X := by
  have hker : IsPGroup 2 (normalRadicalMap hXK).ker := by
    change IsPGroup 2 (((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hXK)).ker)
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hXK)
  refine le_antisymm (le_sSup ⟨inferInstance, hker⟩) ?_
  have hcore := pCoreIn_mono_of_normalizes (p := 2) hXK
    ((normal_subgroupOf_iff_le_normalizer hXK).mp hN)
  intro x hx
  obtain ⟨y, hy, he⟩ := hcore (mem_map_of_mem X.subtype hx)
  have he' : inclusion hXK x = y := Subtype.ext he.symm
  change QuotientGroup.mk' (pCore 2 K) (inclusion hXK x) = 1
  exact (QuotientGroup.eq_one_iff _).mpr (he' ▸ hy)

/-- The image in K/O₂(K) is isomorphic to the literal radical quotient. -/
noncomputable def normalRadicalEquiv {X K : Subgroup G} (hXK : X ≤ K)
    (hN : (X.subgroupOf K).Normal) :
    XiQuotient X ≃* (normalRadicalMap hXK).range :=
  (QuotientGroup.quotientMulEquivOfEq (normalRadicalMap_ker hXK hN).symm).trans
    (QuotientGroup.quotientKerEquivRange (normalRadicalMap hXK))

private theorem normalRadicalMap_range {X K : Subgroup G} (hXK : X ≤ K) :
    (normalRadicalMap hXK).range =
      (X.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) := by
  rw [normalRadicalMap, MonoidHom.range_comp, inclusion_range]

/-- A normal odd radical forces its prime into the larger quotient's Fitting subgroup. -/
theorem prime_dvd_fitting_of_normal_radical [Finite G]
    {X K : Subgroup G} (hXK : X ≤ K) (hN : (X.subgroupOf K).Normal)
    {p : ℕ} [Fact p.Prime] (hX : XiOddQuotient p (XiQuotient X)) :
    p ∣ Nat.card (fittingSubgroup (XiQuotient K)) := by
  have hp : IsPGroup p (normalRadicalMap hXK).range :=
    hX.isPGroup.of_equiv (normalRadicalEquiv hXK hN)
  have hn : (normalRadicalMap hXK).range.Normal := by
    rw [normalRadicalMap_range]
    exact hN.map _ (QuotientGroup.mk'_surjective _)
  have hle : (normalRadicalMap hXK).range ≤ fittingSubgroup (XiQuotient K) :=
    (show (normalRadicalMap hXK).range ≤ pCore p (XiQuotient K) from
      le_sSup ⟨hn, hp⟩).trans (pCore_le_fitting _ p)
  have hd : p ∣ Nat.card (normalRadicalMap hXK).range := by
    rw [← Nat.card_congr (normalRadicalEquiv hXK hN).toEquiv]
    rcases hX with ⟨_, he⟩ | ⟨_, he, _⟩
    · rw [he]; exact dvd_pow_self p (by decide)
    · rw [he]; exact dvd_pow_self p (by decide)
  exact hd.trans (card_dvd_of_le hle)

private theorem not_quasisimple_of_fitting_eq {K : Type*} [Group K] [Finite K]
    (h : generalizedFitting K = fittingSubgroup K) : ¬ IsQuasisimple K := by
  intro hK
  let := hK
  have htop : (⊤ : Subgroup K) ≤ generalizedFitting K :=
    component_le_generalizedFitting K ⊤
      ⟨(inferInstance : (⊤ : Subgroup K).Normal).isSubnormal,
        IsQuasisimple.of_mulEquiv topEquiv.symm⟩
  have hfit : fittingSubgroup K = ⊤ := top_unique (h ▸ htop)
  let : Group.IsNilpotent K := Group.nilpotent_of_mulEquiv
    ((MulEquiv.subgroupCongr hfit).trans topEquiv)
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := Function.Surjective.nontrivial
    (QuotientGroup.mk'_surjective (center K))
  exact Group.IsPerfect.not_isSolvable K inferInstance

private theorem not_quasisimple_of_fitting_prime {K : Type*} [Group K] [Finite K]
    (h : A36Common K) {p : ℕ} (hp3 : 3 < p)
    (hd : p ∣ Nat.card (fittingSubgroup K)) : ¬ IsQuasisimple K := by
  rcases h.2.2.1 with h | h
  · exact not_quasisimple_of_fitting_eq h.1.symm
  · rcases h.2.2 with he | he <;> rw [he] at hd
    · have := Nat.le_of_dvd (by decide : 0 < 1) hd
      omega
    · have := Nat.le_of_dvd (by decide : 0 < 3) hd
      omega

private theorem fitting_map_le {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (fittingSubgroup A).map e.toMonoidHom ≤ fittingSubgroup B := by
  apply map_le_iff_le_comap.mpr
  apply sSup_le
  rintro N ⟨hN, hnil⟩
  apply map_le_iff_le_comap.mp
  let := hnil
  exact le_sSup ⟨hN.map _ e.surjective, Group.nilpotent_of_mulEquiv (e.subgroupMap N)⟩

universe u
variable {E : Type u} [Group E] [Finite E]

/-- The normal-radical inference in 13.1.4. It applies to every local
overgroup, before selecting a maximal one. -/
theorem local_not_quasisimple_of_normal_radical {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ → ∀ C : Subgroup D,
      C.IsCComponent → A36Conclusion C)
    {T X K : Subgroup E} (hK : K ∈ L E T)
    (hQ : IsSQTK 𝒦 ((K ⊔ T : Subgroup E) ⧸ pCore 2 (K ⊔ T : Subgroup E)))
    (hXK : X ≤ K) (hN : (X.subgroupOf K).Normal)
    {p : ℕ} [Fact p.Prime] (hp3 : 3 < p)
    (hX : XiOddQuotient p (XiQuotient X)) :
    ¬ IsQuasisimple (XiQuotient K) := by
  let e := radicalLocalQuotientEquiv hK
  have hd := prime_dvd_fitting_of_normal_radical hXK hN hX
  have hd' : p ∣ Nat.card (fittingSubgroup (radicalLocalImage T K)) := by
    rw [Nat.card_congr (e.subgroupMap (fittingSubgroup (XiQuotient K))).toEquiv] at hd
    exact hd.trans (card_dvd_of_le (fitting_map_le e))
  have hC := proposition_1_2_1_four_earlier_conclusion hA36 hQ hK.1
  intro hn
  let := hn
  exact not_quasisimple_of_fitting_prime hC.2 hp3 hd'
    (IsQuasisimple.of_mulEquiv e)

/-- Literal Ξₚ(L) application: the earlier A.3.6 theorem constructs the
odd quotient and the bound p > 3 from the source nonquasisimple component.
Only its placement as a normal subgroup of K remains from 1.3.4/13.1.2. -/
theorem overgroup_not_quasisimple_of_XiP_normal {𝒦 : GroupClass.{u}}
    (hA36 : ∀ (D : Type u) [Group D] [Finite D],
      IsSQTK 𝒦 D → pCore 2 D = ⊥ → ∀ C : Subgroup D,
      C.IsCComponent → A36Conclusion C)
    {T L₀ K : Subgroup E} (hL : L₀ ∈ L E T) (hK : K ∈ L E T)
    (hQL : IsSQTK 𝒦 ((L₀ ⊔ T : Subgroup E) ⧸ pCore 2 (L₀ ⊔ T : Subgroup E)))
    (hQK : IsSQTK 𝒦 ((K ⊔ T : Subgroup E) ⧸ pCore 2 (K ⊔ T : Subgroup E)))
    (hn : ¬ IsQuasisimple (XiQuotient L₀)) (hLK : L₀ ≤ K)
    {p : ℕ} [Fact p.Prime] (ho : Odd p)
    (hd : p ∣ Nat.card (fittingSubgroup (XiQuotient L₀)))
    (hN : ((XiP p L₀).subgroupOf K).Normal) :
    ¬ IsQuasisimple (XiQuotient K) := by
  obtain ⟨hp3, hX⟩ := XiP_oddQuotient_of_A36 hA36 hL hQL hn ho hd
  exact local_not_quasisimple_of_normal_radical hA36 hK hQK
    ((XiP_le p L₀).trans hLK) hN hp3 hX

end CFSG.Quasithin.Chapter13.Section01
