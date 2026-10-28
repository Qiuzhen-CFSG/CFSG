module

public import CFSG.Quasithin.ChapterJ.Section04To05.SteinbergCommutator.Closure
public import CFSG.Quasithin.ChapterJ.Section04To05.SteinbergCommutator.GroupCommutators
public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.Products

/-!
# The literal second-parabolic quotient

We quotient the original plane normalizer by its actual Steinberg commutator
preimage S₂. The original S and R₂ have images of orders four and sixteen;
the first image is elementary and central in the second. These statements
use the original Ru1 coordinates and actual group commutators throughout.

Source: Aschbacher–Smith, J.4.4, printed p.441.
-/

@[expose] public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

instance Plane.secondKernel_normal : (p.S₂.subgroupOf p.parabolic).Normal :=
  normal_subgroupOf_of_le_normalizer p.S₂_normalized

/-- The literal source quotient G₂/S₂. -/
abbrev Plane.SecondQuotient := p.parabolic ⧸ p.S₂.subgroupOf p.parabolic

/-- The actual projection of the original plane normalizer. -/
def Plane.secondMap : p.parabolic →* p.SecondQuotient := QuotientGroup.mk' _

/-- The original subgroup image in G₂/S₂. -/
def Plane.secondBar (A : Subgroup G) : Subgroup p.SecondQuotient :=
  (A.subgroupOf p.parabolic).map p.secondMap

theorem Plane.secondMap_eq_one (a : p.parabolic) :
    p.secondMap a = 1 ↔ (a : G) ∈ p.S₂ := QuotientGroup.eq_one_iff a

theorem Plane.secondBar_mono {A B : Subgroup G} (h : A ≤ B) :
    p.secondBar A ≤ p.secondBar B := map_mono (comap_mono h)

theorem Plane.secondBar_card (A : Subgroup G) (hA : A ≤ p.parabolic) :
    Nat.card (p.secondBar A) * Nat.card (A ⊓ p.S₂ : Subgroup G) = Nat.card A := by
  let f := p.secondMap.comp (inclusion hA)
  have hk : f.ker = (A ⊓ p.S₂).subgroupOf A := by
    ext a
    change p.secondMap (inclusion hA a) = 1 ↔ (a:G) ∈ A ⊓ p.S₂
    rw [p.secondMap_eq_one]
    exact ⟨fun h => ⟨a.property,h⟩,fun h => h.2⟩
  have hr : f.range = p.secondBar A := by
    rw [MonoidHom.range_comp,inclusion_range]
    rfl
  have hh := f.ker.index_mul_card
  rw [index_ker,hr,hk,Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at hh
  exact hh

theorem Plane.S₂_le_R₂ : p.S₂ ≤ p.R₂ := p.S₂_le_S.trans p.S_le_R₂

theorem Plane.secondBar_S_card : Nat.card (p.secondBar d.toTypeRuSetup.S) = 4 := by
  have h := p.secondBar_card d.toTypeRuSetup.S p.S_le_parabolic
  rw [inf_eq_right.mpr p.S₂_le_S,p.card_S₂,d.ru1.card_S] at h
  omega

theorem Plane.secondBar_R₂_card : Nat.card (p.secondBar p.R₂) = 16 := by
  have h := p.secondBar_card p.R₂ (p.R₂_le_T.trans p.sylow_le_parabolic)
  rw [inf_eq_right.mpr p.S₂_le_R₂,p.card_S₂,p.card_R₂] at h
  omega

theorem Plane.secondBar_S_elementary : IsElementaryAbelian 2 (p.secondBar d.toTypeRuSetup.S) := by
  have hlift (x : p.secondBar d.toTypeRuSetup.S) :
      ∃ a : d.toTypeRuSetup.S, p.secondMap (inclusion p.S_le_parabolic a) =
        (x : p.SecondQuotient) := by
    obtain ⟨a,ha,he⟩ := x.property
    exact ⟨⟨a,ha⟩,he⟩
  refine {toIsMulCommutative := ⟨⟨?_⟩⟩,exponent_dvd_p := ?_}
  · intro x y
    obtain ⟨a,ha⟩ := hlift x
    obtain ⟨b,hb⟩ := hlift y
    apply Subtype.ext
    change (x:p.SecondQuotient)*(y:p.SecondQuotient) = (y:p.SecondQuotient)*(x:p.SecondQuotient)
    rw [← ha,← hb,← commutatorElement_eq_one_iff_mul_comm,← map_commutatorElement]
    apply (p.secondMap_eq_one _).mpr
    apply p.V_le_S₂
    change ((⁅a,b⁆ : d.toTypeRuSetup.S):G) ∈ d.V
    apply (d.ru1.steinberg.coordinates_eq_one_iff ⁅a,b⁆).mp
    rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm _ _
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    obtain ⟨a,ha⟩ := hlift x
    apply Subtype.ext
    change (x:p.SecondQuotient)^2 = 1
    rw [← ha,← map_pow]
    apply (p.secondMap_eq_one _).mpr
    apply p.V_le_S₂
    change ((a^2 : d.toTypeRuSetup.S):G) ∈ d.V
    apply (d.ru1.steinberg.coordinates_eq_one_iff (a^2)).mp
    rw [map_pow]
    change (2:ℕ) • (d.ru1.steinberg.coordinates a).toAdd = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod 2),ZMod.natCast_self,zero_smul]

theorem Plane.secondBar_S_centralizes_R₂ :
    p.secondBar d.toTypeRuSetup.S ≤ centralizer (p.secondBar p.R₂ : Set p.SecondQuotient) := by
  rintro _ ⟨s,hs,rfl⟩ _ ⟨a,ha,rfl⟩
  rw [← commutatorElement_eq_one_iff_mul_comm,← map_commutatorElement]
  apply (p.secondMap_eq_one _).mpr
  exact p.commutator_R₂_S_le_S₂ (commutator_mem_commutator ha hs)

end CFSG.Quasithin.ChapterJ.RuSubgroup
