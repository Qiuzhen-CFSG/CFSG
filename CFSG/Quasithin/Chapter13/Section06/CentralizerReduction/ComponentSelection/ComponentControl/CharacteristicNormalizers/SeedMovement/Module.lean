module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.Geometry.Thompson
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.CharacteristicNormalizers.SeedMovement.NonquasisimpleFactorization.Action
public import Theory.GroupTheory.NormalClosureSylowActionCore
public import Theory.GroupTheory.SolvableOuterQuotient
/-!
# The actual local seed module

Inside H ≤ C_G(v), the module is the normal closure of the cyclic seed
subgroup. Its ambient image is exactly ⟨z^H⟩. Characteristic two in C_G(v)
(the earlier 13.6.6) puts this span in Ω₁(Z(O₂(C_G(v)))), using the checked
B.2.14 argument. The action quotient has trivial two-core because the
actual Sylow subgroup fixes z. Both conclusions use the original subgroup
inclusions, and the quotient is literally H/C_H(W).

Only the elementary B.2.14 lemmas in Geometry.Thompson are used; no
13.6.8–15 conclusion is invoked. Source: Aschbacher–Smith, combined
1 March 2004 manuscript, B.2.14, printed p.78, and 13.6.16(2), p.930.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement
open NonquasisimpleFactorization
variable {G : Type*} [Group G]

/-- The internal normal closure of the actual cyclic seed subgroup. -/
def seedSpan (H : Subgroup G) (z : G) (hz : z ∈ H) : Subgroup H :=
  normalClosure (zpowers (⟨z, hz⟩ : H) : Set H)
instance (H : Subgroup G) (z : G) (hz : z ∈ H) : (seedSpan H z hz).Normal :=
  normalClosure_normal

/-- The literal seed belongs to its internal module. -/
theorem seed_mem (H : Subgroup G) (z : G) (hz : z ∈ H) :
    (⟨z, hz⟩ : H) ∈ seedSpan H z hz := le_normalClosure (mem_zpowers _)

/-- Mapping the internal closure gives exactly the ambient conjugate span. -/
theorem seedSpan_map (H : Subgroup G) (z : G) (hz : z ∈ H) :
    (seedSpan H z hz).map H.subtype = conjugateSpanBy (zpowers z) H := by
  let E := conjugateSpanBy (zpowers z) H
  have hEH : E ≤ H := conjugateSpanBy_le_self (zpowers_le.mpr hz)
  let : (E.subgroupOf H).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  apply le_antisymm
  · apply map_le_iff_le_comap.mpr
    change seedSpan H z hz ≤ E.subgroupOf H
    apply normalClosure_le_normal
    apply zpowers_le.mpr
    exact le_conjugateSpanBy _ _ (mem_zpowers z)
  · apply conjugateSpanBy_le
    · exact zpowers_le.mpr (mem_map_of_mem H.subtype (seed_mem H z hz))
    · apply (normal_subgroupOf_iff_le_normalizer (map_subtype_le _)).mp
      change (((seedSpan H z hz).map H.subtype).comap H.subtype).Normal
      rw [comap_map_eq_self_of_injective H.subtype_injective]
      infer_instance

variable [Finite G]

/-- A Sylow-central seed makes its faithful conjugation quotient two-reduced. -/
theorem seedSpan_twoCore (H : Subgroup G) (z : G) (hz : z ∈ H)
    (P : Sylow 2 H) (hc : (P : Subgroup H) ≤ centralizer ({⟨z, hz⟩} : Set H)) :
    pCore 2 (ActionQuotient (seedSpan H z hz)) = ⊥ := by
  let W := seedSpan H z hz
  let f : H →* MulAut W := MulAut.conjNormal
  have hZP : zpowers (⟨z, hz⟩ : H) ≤ centralizer (P : Set H) := by
    apply zpowers_le.mpr
    exact mem_centralizer_iff.mpr (fun p hp => mem_centralizer_singleton_iff.mp (hc hp))
  have hr : pCore 2 f.range = ⊥ :=
    pCore_conjNormal_range_eq_bot_of_normalClosure P (zpowers (⟨z, hz⟩ : H)) W rfl hZP
  let e : ActionQuotient W ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq (MulAut.conjNormal_ker_eq_centralizer W).symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  exact (map_eq_bot_iff_of_injective _ e.injective).mp
    ((pCore_map_iso 2 e).trans hr)

/-- The earlier characteristic-two conclusion supplies elementary abelianity. -/
theorem seedSpan_elementary (T : Subgroup G) (z v : G)
    (hSylow : Chapter1.IsSylowIn 2 (Tv T v) (Gv v))
    (hz : z ∈ omegaOneCenterAmbient (Tv T v))
    (hf : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (H : Subgroup G) (hH : H ≤ Gv v) (hzH : z ∈ H) :
    IsElementaryAbelian 2 (seedSpan H z hzH) := by
  let E := omegaOneCenterAmbient (Qv v)
  let : IsElementaryAbelian 2 E := omegaOneCenterAmbient_elementaryAbelian _
  have hle : (seedSpan H z hzH).map H.subtype ≤ E := by
    rw [seedSpan_map]
    exact (conjugateSpanBy_mono le_rfl hH).trans (Uv_le_coreOmega T z v hSylow hz hf)
  let f : seedSpan H z hzH →* E :=
    ((H.subtype.comp (seedSpan H z hzH).subtype)).codRestrict E
      (fun x => hle (mem_map_of_mem H.subtype x.property))
  have hi : Function.Injective f :=
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun a : E => (a : G)) h))
  refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
  · apply hi
    simp only [map_mul]
    exact mul_comm _ _
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    apply hi
    rw [map_pow, map_one]
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (p := 2) (f x : G) (f x).property)
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.SeedMovement

end
