module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Source
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Actor
public import Theory.ElementaryAbelian.AbelianNormalClosure
/-!
# Structure of the literal U₀/V section

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.948, Lemma 13.8.6(5), using the earlier
local containments in 13.7.3.

The seed commutator bound propagates through L-conjugates by normalization of
the restricted centralizer kernel. The abelian H-span makes U_L centralize V,
so U₀ lies in that kernel. Its quotient by V is consequently commutative, and
its involutory seed generators give exponent two. Normality is only inside
U₀, and U_L need not be abelian. The earlier containment C_LT(V) ≤ T remains
explicit, rather than silently identifying a centralizer with a two-core.
-/

@[expose] public section

open Subgroup
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed
variable {G : Type*} [Group G]

/-- The genuine abelian H-span of the elementary flag is elementary abelian. -/
theorem VH_elementary (H V : Subgroup G) [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)] : IsElementaryAbelian 2 (Source.VH H V) := by
  let : IsMulCommutative (closure {x : G | ∃ h ∈ H, ∃ v ∈ V, h * v * h⁻¹ = x}) :=
    (inferInstance : IsMulCommutative (Source.VH H V))
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨h, hh, v, hv, rfl⟩
  rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian v hv, mul_one, mul_inv_cancel]

/-- The source UH inherits elementary abelianness from the abelian H-span. -/
theorem UH_elementary (H V₃ V : Subgroup G) [IsElementaryAbelian 2 V]
    [IsMulCommutative (Source.VH H V)] (hV₃V : V₃ ≤ V) :
    IsElementaryAbelian 2 (Source.UH H V₃) := by
  let : IsElementaryAbelian 2 (Source.VH H V) := VH_elementary H V
  exact IsElementaryAbelian.of_le
    (show Source.UH H V₃ ≤ Source.VH H V from conjugateSpanBy_mono hV₃V le_rfl)

/-- A kernel commutator estimate on a seed propagates through conjugators
normalizing both the kernel and denominator. -/
theorem span_commutator_le (P D L C V : Subgroup G)
    (hDP : D ≤ P) (hLP : L ≤ P) (hPV : P ≤ normalizer (V : Set G))
    (hLC : L ≤ normalizer (C : Set G)) (hDC : ⁅D, C⁆ ≤ V) :
    ⁅conjugateSpanBy D L, C⁆ ≤ V := by
  have hspan : conjugateSpanBy D L ≤ commutatorPreimage P C V :=
    conjugateSpanBy_le (le_commutatorPreimage hDP hDC)
      (commutatorPreimage_normalized P C V L hPV
        (hLP.trans P.le_normalizer) hLC (hLP.trans hPV))
  exact (commutator_mono hspan le_rfl).trans
    (commutator_commutatorPreimage_le P C V hPV)

/-- The source abelian H-span makes the L-span centralize V; no abelianness
of the latter span is used. -/
theorem UL_centralizes_V (L H V₃ V : Subgroup G)
    [IsMulCommutative (Source.VH H V)] (hV₃V : V₃ ≤ V)
    (hLV : L ≤ normalizer (V : Set G)) :
    Source.UL L H V₃ ≤ centralizer (V : Set G) := by
  let : IsMulCommutative (conjugateSpanBy V H) :=
    (inferInstance : IsMulCommutative (Source.VH H V))
  apply conjugateSpanBy_le ?_ (centralizer_normalized V L hLV)
  intro u hu v hv
  exact setLike_mul_comm (le_conjugateSpanBy V H hv)
    ((conjugateSpanBy_mono hV₃V le_rfl) hu)

/-- Relative normality of V in U₀ follows from its LT-normalization. -/
theorem U0_relative_normal (L H K T V₃ V : Subgroup G)
    (hUL : Source.UL L H V₃ ≤ L ⊔ T)
    (hV : L ⊔ T ≤ normalizer (V : Set G)) :
    (V.subgroupOf (Source.U0 L H K V₃)).Normal :=
  normal_subgroupOf_of_le_normalizer ((Source.U0_le_UL L H K V₃).trans (hUL.trans hV))

/-- The constructed source actor kernel kills U₀/V. -/
theorem U0_kernel_commutator (L H K T L₁ V₃ V V₁ : Subgroup G)
    (hUL : Source.UL L H V₃ ≤ L ⊔ T)
    (hV : L ⊔ T ≤ normalizer (V : Set G))
    (hkernelT : centralizer (V : Set G) ⊓ (L ⊔ T) ≤ T)
    (hV₁V : V₁ ≤ V) (hcomm : ⁅L₁ ⊔ T, Source.U1 H K V₃⁆ ≤ V₁) :
    ⁅Source.U0 L H K V₃, (actorKernel (L ⊔ T) V).map (L ⊔ T).subtype⁆ ≤ V := by
  rw [actorKernel_map]
  apply span_commutator_le (L ⊔ T) (Source.U1 H K V₃) L _ V
    (((le_conjugateSpanBy _ L).trans (Source.U0_le_UL L H K V₃)).trans hUL)
    le_sup_left hV
  · exact (le_inf (centralizer_normalized V L (le_sup_left.trans hV))
      (le_sup_left.trans (L ⊔ T).le_normalizer)).trans inf_normalizer_le_normalizer_inf
  · rw [commutator_comm]
    exact (commutator_mono (hkernelT.trans le_sup_right) le_rfl).trans (hcomm.trans hV₁V)

private theorem quotient_commutative (B V : Subgroup G) [(V.subgroupOf B).Normal]
    (hcomm : ⁅B, B⁆ ≤ V) : IsMulCommutative (B ⧸ V.subgroupOf B) := by
  refine ⟨⟨?_⟩⟩
  intro x y
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf B) x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf B) y
  apply commutatorElement_eq_one_iff_mul_comm.mp
  rw [← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr
    (hcomm (commutator_mem_commutator a.property b.property))

private theorem elementary_quotient_of_span (D L V : Subgroup G)
    [IsElementaryAbelian 2 D] [(V.subgroupOf (conjugateSpanBy D L)).Normal]
    (hcomm : ⁅conjugateSpanBy D L, conjugateSpanBy D L⁆ ≤ V) :
    IsElementaryAbelian 2 (conjugateSpanBy D L ⧸ V.subgroupOf (conjugateSpanBy D L)) := by
  let B := conjugateSpanBy D L
  let := quotient_commutative B V hcomm
  let q : B →* B ⧸ V.subgroupOf B := QuotientGroup.mk' _
  let F := (powMonoidHom 2).comp q
  have hBF : B ≤ F.ker.map B.subtype := by
    apply (Subgroup.closure_le _).mpr
    rintro x ⟨l, hl, d, hd, rfl⟩
    let xB : B := ⟨l * d * l⁻¹, subset_closure ⟨l, hl, d, hd, rfl⟩⟩
    refine ⟨xB, ?_, rfl⟩
    change (q xB) ^ 2 = 1
    rw [← map_pow]
    have hx : xB ^ 2 = 1 := by
      apply Subtype.ext
      change (l * d * l⁻¹) ^ 2 = 1
      rw [conj_pow, elemPow_eq_one_of_isElementaryAbelian d hd, mul_one, mul_inv_cancel]
    rw [hx, map_one]
  refine { exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  intro x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (V.subgroupOf B) x
  obtain ⟨b', hb', he⟩ := hBF b.property
  have he' : b' = b := Subtype.ext he
  subst b'
  exact hb'

/-- U₀/V is elementary abelian because the actor kernel contains U₀ and
kills it modulo V, while the seed consists of involutions. -/
theorem U0_section_elementary (L H K T L₁ V₃ V V₁ : Subgroup G)
    [IsElementaryAbelian 2 V] [IsMulCommutative (Source.VH H V)]
    [(V.subgroupOf (Source.U0 L H K V₃)).Normal]
    (hV₃V : V₃ ≤ V) (hUL : Source.UL L H V₃ ≤ L ⊔ T)
    (hV : L ⊔ T ≤ normalizer (V : Set G))
    (hkernelT : centralizer (V : Set G) ⊓ (L ⊔ T) ≤ T)
    (hV₁V : V₁ ≤ V) (hcomm : ⁅L₁ ⊔ T, Source.U1 H K V₃⁆ ≤ V₁) :
    IsElementaryAbelian 2 (Source.U0section L H K V₃ V) := by
  have hkill := U0_kernel_commutator L H K T L₁ V₃ V V₁ hUL hV hkernelT hV₁V hcomm
  have hU0C : Source.U0 L H K V₃ ≤ (actorKernel (L ⊔ T) V).map (L ⊔ T).subtype := by
    rw [actorKernel_map]
    exact le_inf ((Source.U0_le_UL L H K V₃).trans
      (UL_centralizes_V L H V₃ V hV₃V (le_sup_left.trans hV)))
      ((Source.U0_le_UL L H K V₃).trans hUL)
  let : IsElementaryAbelian 2 (Source.UH H V₃) := UH_elementary H V₃ V hV₃V
  let : IsElementaryAbelian 2 (Source.U1 H K V₃) :=
    IsElementaryAbelian.of_le (show Source.U1 H K V₃ ≤ Source.UH H V₃ from inf_le_left)
  let : (V.subgroupOf (conjugateSpanBy (Source.U1 H K V₃) L)).Normal :=
    (inferInstance : (V.subgroupOf (Source.U0 L H K V₃)).Normal)
  exact elementary_quotient_of_span (Source.U1 H K V₃) L V
    ((commutator_mono le_rfl hU0C).trans hkill)

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed

end
