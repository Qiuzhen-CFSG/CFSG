module

public import CFSG.Quasithin.ChapterJ.Section04To05.FiveDecomposition.Center
public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.CoreProduct

/-!
# The original central preimage and conjugate span in J.4

The preimage Q₀ of Z(H/U) has order 64 and lies in HC, hence in S.
The L₂-conjugate span W₀ of U is also the full G₂-conjugate span: T
normalizes both U and L₂. Thus W₀ is G₂-invariant. The source subgroup
W = W₀Q₀ is defined in the original ambient group and lies in S.

These are the constructions immediately preceding J.4.2, printed p.440.
Their later identification with S₂ is a separate assertion.
-/

public section
noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
variable {G : Type*} [Group G] [Finite G] (d : LocalSetup G)

/-- The full preimage in the original H of the center of H/U. -/
def Q₀ : Subgroup G := ((center (Hat d)).comap (hatMap d)).map d.toTypeRuSetup.H.subtype

theorem Q₀_le_H : Q₀ d ≤ d.toTypeRuSetup.H := map_subtype_le _

theorem Q₀_normalized : d.toTypeRuSetup.H ≤ normalizer (Q₀ d : Set G) := by
  have h := ((center (Hat d)).comap (hatMap d)).le_normalizer_map
    d.toTypeRuSetup.H.subtype
  rwa [normalizer_eq_top,← MonoidHom.range_eq_map,range_subtype] at h

theorem mem_Q₀ (h : d.toTypeRuSetup.H) :
    (h:G) ∈ Q₀ d ↔ hatMap d h ∈ center (Hat d) := by
  change (h:G) ∈ Subgroup.map _ _ ↔ _
  exact mem_map_iff_mem d.toTypeRuSetup.H.subtype_injective

theorem U_le_Q₀ : d.toTypeRuSetup.U ≤ Q₀ d := by
  intro u hu
  apply (mem_Q₀ d ⟨u,d.ru2.natural.section_le hu⟩).mpr
  rw [(hatMap_eq_one d _).mpr hu]
  exact (center (Hat d)).one_mem

/-- The original central preimage has exactly the intended quotient image. -/
theorem hat_Q₀ : hat d (Q₀ d) = center (Hat d) := by
  ext a
  constructor
  · rintro ⟨h,hh,rfl⟩
    exact (mem_Q₀ d h).mp hh
  · intro ha
    obtain ⟨h,rfl⟩ := QuotientGroup.mk'_surjective
      (d.toTypeRuSetup.U.subgroupOf d.toTypeRuSetup.H) a
    exact ⟨h,(mem_Q₀ d h).mpr ha,rfl⟩

theorem Q₀_le_Q : Q₀ d ≤ d.toTypeRuSetup.Q := by
  intro q hq
  let a : d.toTypeRuSetup.H := ⟨q,Q₀_le_H d hq⟩
  have hh := center_le_hat_Q d ((mem_Q₀ d a).mp hq)
  rw [← hatStar_kernel,MonoidHom.mem_ker,hatStar_apply] at hh
  have hk : a ∈ d.ru2.quotientMap.ker := hh
  rw [d.ru2.quotient_kernel] at hk
  exact hk

/-- Centrality modulo U puts Q₀ inside the genuine fixed subgroup HC. -/
theorem Q₀_le_HC : Q₀ d ≤ d.toTypeRuSetup.HC := by
  intro q hq
  apply (d.mem_HC_iff_commutator_mem_U d.Q_le_K q).mpr
  refine ⟨Q₀_le_Q d hq,fun k hk => ?_⟩
  let a : d.toTypeRuSetup.H := ⟨q,Q₀_le_H d hq⟩
  let b : d.toTypeRuSetup.H := ⟨k,d.toTypeRuSetup.K_le_H hk⟩
  apply (hatMap_eq_one d ⁅b,a⁆).mp
  rw [map_commutatorElement,commutatorElement_eq_one_iff_mul_comm]
  exact mem_center_iff.mp ((mem_Q₀ d a).mp hq) (hatMap d b)

theorem Q₀_le_S : Q₀ d ≤ d.toTypeRuSetup.S := by
  have hc : d.toTypeRuSetup.HC ≤ centralizer (d.V : Set G) :=
    inf_le_right.trans (centralizer_le (le_conjugateSpan _ _))
  rw [d.ru1.centralizer_V] at hc
  exact (Q₀_le_HC d).trans hc

/-- The original central preimage has order 2⁶. -/
theorem card_Q₀ : Nat.card (Q₀ d) = 64 := by
  have h := hat_card d (Q₀ d) (Q₀_le_H d)
  rw [hat_Q₀,center_hat_card,inf_eq_right.mpr (U_le_Q₀ d),d.ru2.card_U d.card_Z] at h
  exact h.symm

variable {d} (p : Plane d)

/-- The original L₂-conjugate span of U. -/
def Plane.W₀ : Subgroup G := conjugateSpan p.L₂ d.toTypeRuSetup.U

theorem Plane.W₀_eq_conjugateSpanBy :
    p.W₀ = conjugateSpanBy d.toTypeRuSetup.U p.L₂ := by
  rw [conjugateSpanBy_eq_iSup_conj]
  rfl

theorem Plane.U_le_W₀ : d.toTypeRuSetup.U ≤ p.W₀ := le_conjugateSpan _ _

theorem Plane.W₀_le_S : p.W₀ ≤ d.toTypeRuSetup.S :=
  iSup_le fun l => ConjugateIntersections.conjugateU_le_S d l (p.L₂_le_L l.property)

/-- Both the residual and the original Sylow group normalize the span. -/
theorem Plane.W₀_normalized : p.parabolic ≤ normalizer (p.W₀ : Set G) := by
  rw [p.W₀_eq_conjugateSpanBy,← p.residual_sup_sylow]
  refine sup_le (le_normalizer_conjugateSpanBy _ _) ?_
  apply le_normalizer_closure_iff.mpr
  rintro t ht x ⟨l,hl,u,hu,rfl⟩
  have htL : t ∈ normalizer (p.L₂ : Set G) :=
    p.L₂_normalized (p.sylow_le_parabolic ht)
  have htl := (mem_normalizer_iff.mp htL l).mp hl
  have htu := (mem_normalizer_iff.mp
    (d.ru2.natural.normalized (d.toTypeRuSetup.T_le_H ht)) u).mp hu
  apply Subgroup.subset_closure
  refine ⟨t*l*t⁻¹,htl,t*u*t⁻¹,htu,?_⟩
  group

/-- The original L₂-span is the full second-parabolic span. -/
theorem Plane.W₀_eq_parabolic_span : p.W₀ = conjugateSpan p.parabolic d.toTypeRuSetup.U := by
  have hle : p.W₀ ≤ conjugateSpanBy d.toTypeRuSetup.U p.parabolic := by
    rw [p.W₀_eq_conjugateSpanBy]
    exact conjugateSpanBy_mono le_rfl p.L₂_le_parabolic
  have hge := conjugateSpanBy_le p.U_le_W₀ p.W₀_normalized
  rw [conjugateSpanBy_eq_iSup_conj] at hle hge
  exact le_antisymm hle hge

/-- The source product W₀Q₀, as a subgroup of the original group. -/
def Plane.W : Subgroup G := p.W₀ ⊔ Q₀ d

theorem Plane.U_le_W : d.toTypeRuSetup.U ≤ p.W := p.U_le_W₀.trans le_sup_left

theorem Plane.W_le_S : p.W ≤ d.toTypeRuSetup.S := sup_le p.W₀_le_S (Q₀_le_S d)

open scoped Pointwise in
/-- The subgroup join is literally the product W₀Q₀ from the source. -/
theorem Plane.W_eq_product : (p.W : Set G) = (p.W₀ : Set G) * (Q₀ d : Set G) :=
  coe_mul_of_left_le_normalizer_right _ _
    (p.W₀_le_S.trans (d.S_le_H.trans (Q₀_normalized d)))

/-- The center line in H/U is contained in the image of the actual source W. -/
theorem Plane.center_le_hat_W : center (Hat d) ≤ hat d p.W := by
  rw [← hat_Q₀]
  exact hat_mono d le_sup_right

end CFSG.Quasithin.ChapterJ.RuSubgroup
