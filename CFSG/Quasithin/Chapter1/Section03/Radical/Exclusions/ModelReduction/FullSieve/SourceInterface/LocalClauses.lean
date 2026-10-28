module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.StarTransport
public import CFSG.Quasithin.Chapter1.Section03.Radical.Exclusions.ModelReduction.FullSieve.ModelCases
public import Theory.Representation.NormalElementaryQuotient
public import Theory.Representation.BinaryOffender.Basic
public import Stellmacher.ElementaryAbelianMaxDefs

/-!
# The local assertions in C.2.7(1)–(2)

All subgroups here use the actual star quotient KR/C_KR(V), with
V = Ω₁(Z(O₂(KR))). Its binary representation is the descended conjugation
action, constructed by the existing centralizer-quotient API. FF and FF-star
offenders use the definitions of B.1 on that actual representation. In
particular FF-star means a best offender, not a minimal best offender.

This module states the source clauses and proves elementary facts about their
constructions. It does not assert C.2.7 or replace its alternatives by model tags.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.1.1–3,
printed pp.67–68; B.2.11, p.77; C.2.7(1)–(2), pp.145–147.
-/

@[expose] public section

namespace CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface

open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
universe u
variable {G : Type u} [Group G]

/-- The image M_K* of the actual intersection M_H ∩ K. -/
def starM (K R MH : Subgroup G) : Subgroup (StarQuotient K R) :=
  starImage K R (MH ⊓ K)

/-- The source's K*R* is the whole star quotient, using the images of the
actual two generating subgroups of KR. -/
theorem starImage_sup_eq_top (K R : Subgroup G) :
    starImage K R K ⊔ starImage K R R = ⊤ := by
  unfold starImage
  rw [← Subgroup.map_sup, ← subgroupOf_sup le_sup_left le_sup_right, subgroupOf_self,
    map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]

/-- The conjugation-fixed subgroup of V for A ≤ (KR)*. Every lift of every
element of A must commute with the vector; thus no arbitrary action is used. -/
def starFixed (K R : Subgroup G) (A : Subgroup (StarQuotient K R)) :
    Subgroup (starV K R) :=
  (centralizer (A.comap (QuotientGroup.mk' (starKernel K R)) :
    Set (K ⊔ R : Subgroup G))).subgroupOf (starV K R)

/-- The omega-center construction is elementary abelian before applying C.2.7. -/
instance starV_elementary (K R : Subgroup G) : IsElementaryAbelian 2 (starV K R) := by
  let _ := IsElementaryAbelian.omega₁_of_isMulCommutative
    (p := 2) (center (pCore 2 (K ⊔ R : Subgroup G)))
  let _ := IsElementaryAbelian.map_subtype (p := 2)
    (H := omega₁ (center (pCore 2 (K ⊔ R : Subgroup G))) (p := 2))
  exact IsElementaryAbelian.map_subtype (p := 2)

/-- The actual binary action of KR/C_KR(V) on V, with no chosen model. -/
noncomputable def starRepresentation (K R : Subgroup G) :
    Representation (ZMod 2) (StarQuotient K R) (Additive (starV K R)) :=
  Representation.NormalElementaryQuotient.representation (starV K R)
    (QuotientGroup.mk' (starKernel K R))
    (QuotientGroup.mk'_surjective _) (QuotientGroup.ker_mk' _)

/-- An FF-offender on the actual star module. -/
def IsStarOffender (K R : Subgroup G) (A : Subgroup (StarQuotient K R)) : Prop :=
  Representation.BinaryOffender.IsOffender (starRepresentation K R) A

/-- An FF-star offender, in the precise best-offender sense of B.1.3. -/
def IsStarBestOffender (K R : Subgroup G)
    (A : Subgroup (StarQuotient K R)) : Prop :=
  Representation.BinaryOffender.IsBestOffender (starRepresentation K R) A

/-- Exactly V ∈ R₂(KR): V is normal elementary abelian and its faithful
conjugation quotient has trivial two-core. Normality is included explicitly,
although it also follows from the construction of `starV`. -/
def StarReduced (K R : Subgroup G) : Prop :=
  (starV K R).Normal ∧ IsElementaryAbelian 2 (starV K R) ∧
    pCore 2 (StarQuotient K R) = ⊥

/-- Both centralizer inclusions and the reduced-module clause in C.2.7(1). -/
structure KernelConclusion (K R : Subgroup G) : Prop where
  lower : pCore 2 (K ⊔ R : Subgroup G) ≤ starKernel K R
  upper : StarKernelBound K R
  reduced : StarReduced K R

/-- The three assertions in C.2.7(2), with J the elementary Thompson subgroup.
The second is the existence of an FF-offender for the full faithful action;
the third locates an FF-star offender inside the actual image of R. -/
structure OffenderConclusion (K R : Subgroup G) : Prop where
  thompson : ¬ Stellmacher.elementaryAbelianMaxJ R ≤
    Stellmacher.elementaryAbelianMaxJ ((K ⊔ R).pCoreIn 2)
  ff : ∃ A : Subgroup (StarQuotient K R), IsStarOffender K R A
  best : ∃ A : Subgroup (StarQuotient K R),
    A ≤ starImage K R R ∧ IsStarBestOffender K R A

/-- The characteristic construction of V supplies its relative normality. -/
theorem starV_normal (K R : Subgroup G) : (starV K R).Normal := inferInstance

/-- Every vector is fixed by the identity subgroup of the faithful quotient. -/
theorem starFixed_bot (K R : Subgroup G) : starFixed K R ⊥ = ⊤ := by
  apply top_unique
  intro v _
  change (v : (K ⊔ R : Subgroup G)) ∈ centralizer _
  apply mem_centralizer_iff.mpr
  intro x hx
  have hx' : x ∈ starKernel K R := by
    apply (QuotientGroup.eq_one_iff _).mp
    exact mem_bot.mp hx
  exact ((mem_centralizer_iff.mp hx') v v.property).symm

/-- The binary action is literally conjugation of representatives. -/
theorem starRepresentation_apply (K R : Subgroup G)
    (g : (K ⊔ R : Subgroup G)) (v : Additive (starV K R)) :
    ((starRepresentation K R (QuotientGroup.mk' (starKernel K R) g) v).toMul :
      (K ⊔ R : Subgroup G)) = g * (v.toMul : (K ⊔ R : Subgroup G)) * g⁻¹ :=
  Representation.NormalElementaryQuotient.representation_apply _ _ _ _ g v

/-- Quotienting by the exact centralizer makes this action faithful. -/
theorem starRepresentation_injective (K R : Subgroup G) :
    Function.Injective (starRepresentation K R) :=
  Representation.NormalElementaryQuotient.representation_injective _ _ _ _

/-- FF-star offenders are FF-offenders, by comparing with the trivial subgroup. -/
theorem IsStarBestOffender.offender [Finite G] {K R : Subgroup G}
    {A : Subgroup (StarQuotient K R)} (h : IsStarBestOffender K R A) :
    IsStarOffender K R A :=
  Representation.BinaryOffender.IsBestOffender.isOffender _ h

/-- The lower bound never needs a classification premise. -/
theorem kernelConclusion_of_upper_reduced {K R : Subgroup G}
    (hu : StarKernelBound K R) (hr : StarReduced K R) : KernelConclusion K R :=
  ⟨core_le_starKernel K R, hu, hr⟩

/-- Source inputs to C.2.7, with all ambient containments and relative
normalizers inherited from the genuine C.2.3 setup. No source conclusion occurs
in this record. The universal source implication is assembled separately once
all eight alternatives have been stated. -/
structure Input (κ : GroupClass.{u}) (H R MH K : Subgroup G) : Prop where
  setup : PushingUpSetup κ H R MH
  component : K ∈ cComponentsIn H
  quasisimple : IsQuasisimple (XiQuotient K)
  fitting : generalizedFitting K = pCore 2 K
  outside : ¬ K ≤ MH
  normalizes : R ≤ normalizer K

/-- All source constructions take place in the local group H. -/
theorem Input.join_le {κ : GroupClass.{u}} {H R MH K : Subgroup G}
    (h : Input κ H R MH K) : K ⊔ R ≤ H :=
  sup_le h.component.1 h.setup.radical_le

/-- The ambient normalizer inequality is precisely R ≤ N_H(K), since
the setup already places R inside H. -/
theorem Input.relativeNormalizer {κ : GroupClass.{u}} {H R MH K : Subgroup G}
    (h : Input κ H R MH K) : R ≤ H ⊓ normalizer K :=
  le_inf h.setup.radical_le h.normalizes

/-- The radical construction supplies exactly the C.2.7 inputs, in the same
ambient group; in particular its normalizer is not an ambient normality claim. -/
theorem input_of_pushingUpComponent [Finite G] {κ : GroupClass.{u}} {p : ℕ}
    {T X P M H₀ K : Subgroup G} (h : PushingUpComponent κ p T X P M H₀ K) :
    Input κ H₀ ((X ⊔ T).pCoreIn 2) (H₀ ⊓ M) K :=
  ⟨h.setup, h.component, h.quasisimple, h.fitting, h.outside, h.radical_normalizes⟩

/-- The local intersection lies in the correct star component. -/
theorem starM_le (K R MH : Subgroup G) : starM K R MH ≤ starImage K R K :=
  map_mono (comap_mono inf_le_right)

end CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
