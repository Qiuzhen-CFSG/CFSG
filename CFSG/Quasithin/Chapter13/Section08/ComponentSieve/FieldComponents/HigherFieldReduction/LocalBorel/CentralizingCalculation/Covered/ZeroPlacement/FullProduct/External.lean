module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.FullProduct
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.DegenerateAction.NaturalKernel
public import Theory.GroupTheory.PResidual.CubicInversion
public import Theory.GroupTheory.PCoreRestriction

/-!
# External centralization through the full product and its actual kernel

Let J = BL₁ = CX with the actual marked X = L₁,+. Retain X normal in H
and an actual element s of T whose image in H/O₂(H) centralizes K* and
inverts X*. The literal lifted commutator [B,⟨s⟩] lies in O₂(H) ∩ J,
hence in P = O₂(J). The genuine star-map kernel of X is O₂(X), so
inversion transfers to X/O₂(X), and then to the cubic quotient J/(CP).
The same s fixes B there; thus B ≤ CP. Separate two-perfectness of B
removes P and gives B ≤ C, which centralizes V by the checked natural
alternating-action centralizer.

The generic quotient argument lives in Theory.GroupTheory.PResidual.CubicInversion.
The source adapters preserve relative normality, the full lifted commutator,
and the possibly nontrivial action of O₂(H) on V. The last entry point
lifts a witness in T* ∩ C(K*) to an actual member of T. Construction of
that witness belongs to the source-alternative assembly: these are
conditional external adapters, not an unconditional external exclusion.
No stronger ZeroPlacement endpoint is used or changed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
the external branch of 13.8.20, p.954/PDF p.971, using the sufficient
full-product calculation and the actual quotient conventions of §13.7.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.FullProduct.External
open CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.LinearThree.Geometry.CoveredProduct.ResidualPlacement
universe u v
variable {G : Type u} [Group G]

/-- Star centralization bounds the entire lifted cyclic commutator by the ambient core. -/
theorem star_centralizer_commutator (H K B : Subgroup G) (hBH : B ≤ H) (hBK : B ≤ K)
    (s : H) (hs : QuotientGroup.mk' (pCore 2 H) s ∈
      centralizer (Source.starImage H K : Set (Source.Hstar H))) :
    ⁅B, zpowers s.val⁆ ≤ H.pCoreIn 2 := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let A := ((centralizer (Source.starImage H K : Set (Source.Hstar H))).comap q).map H.subtype
  have hA : zpowers s.val ≤ A := zpowers_le.mpr ⟨s, hs, rfl⟩
  apply commutator_le.mpr
  intro b hb z hz
  obtain ⟨zH, hzH, rfl⟩ := hA hz
  let bH : H := ⟨b, hBH hb⟩
  refine ⟨⁅bH, zH⁆, ?_, rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change q ⁅bH, zH⁆ = 1
  rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  exact hzH _ ⟨bH, hBK hb, rfl⟩

/-- Restriction of the ambient core is a normal two-subgroup of the full product. -/
theorem ambient_core_intersection_le (H J : Subgroup G) (hJH : J ≤ H) :
    H.pCoreIn 2 ⊓ J ≤ J.pCoreIn 2 := by
  rw [inf_comm]
  exact inf_pCoreIn_le_of_le 2 hJH

variable [Finite G]

/-- Actual relative normality retains the precise star-map kernel when lifting inversion. -/
theorem inversion_of_star_inversion (H X : Subgroup G) (hXH : X ≤ H)
    (hn : (X.subgroupOf H).Normal) (s : H)
    (hinv : ∀ x ∈ Source.starImage H X,
      QuotientGroup.mk' (pCore 2 H) s * x * (QuotientGroup.mk' (pCore 2 H) s)⁻¹ = x⁻¹) :
    InvertsTwoCoreQuotient X s.val := by
  let _ := hn
  have hns : s.val ∈ normalizer (X : Set G) :=
    le_normalizer_of_normal_subgroupOf hXH s.property
  have hnstar : (Source.starImage H X).Normal :=
    hn.map _ (QuotientGroup.mk'_surjective _)
  refine ⟨hns, ?_⟩
  intro x hx
  let xX : X := ⟨x, hx⟩
  let y : X := X.normalizerMonoidHom ⟨s.val, hns⟩ xX * xX
  have hy : y ∈ pCore 2 X := by
    rw [← normal_starMap_ker H X hXH hnstar]
    apply MonoidHom.mem_ker.mpr
    apply Subtype.ext
    let xH : H := inclusion hXH xX
    let q := QuotientGroup.mk' (pCore 2 H)
    change q (s * xH * s⁻¹ * xH) = 1
    simp only [map_mul, map_inv]
    rw [hinv (q xH) ⟨xH, hx, rfl⟩, inv_mul_cancel]
  exact ⟨y, hy, rfl⟩

variable {T : Sylow 2 G} {H K L V V₁ V₂ V₃ M G₁ : Subgroup G}
  [(Source.starImage H K).Normal] {n : ℕ} {unitary four : Bool}
  (d : SourceContext.{u,v} T H K L V V₁ V₂ V₃ M G₁ n unitary four)
  (a : LocalAction.NaturalSetup L (T : Subgroup G) V V₁ V₃)
  (hfactor : one L (T : Subgroup G) V₁ = plus L (T : Subgroup G) V₁ ⊔ zero L)
local notation "D" => one L (T : Subgroup G) V₁
local notation "X" => plus L (T : Subgroup G) V₁
local notation "C" => centralizingResidual d.B D L
local notation "J" => d.B ⊔ D

/-- The source Sylow witness gives the literal commutator bound in O₂(H) ∩ J. -/
theorem source_commutator_le_core_intersection (s : H) (hsT : s.val ∈ (T : Subgroup G))
    (hs : QuotientGroup.mk' (pCore 2 H) s ∈
      centralizer (Source.starImage H K : Set (Source.Hstar H))) :
    ⁅d.B, zpowers s.val⁆ ≤ H.pCoreIn 2 ⊓ J := by
  have hBK := borel_le_component H K (T : Subgroup G) d.component_le d.sylow_H
  exact le_inf (star_centralizer_commutator H K d.B (hBK.trans d.component_le) hBK s hs)
    ((le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr
      (d.borel_normalized (mem_sup_right hsT)))).trans le_sup_left)

include a hfactor in
theorem borel_le_sup_core_of_star_inverter
    (hnX : ((X).subgroupOf H).Normal)
    (s : H) (hsT : s.val ∈ (T : Subgroup G))
    (hs : QuotientGroup.mk' (pCore 2 H) s ∈
      centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hinv : ∀ x ∈ Source.starImage H X,
      QuotientGroup.mk' (pCore 2 H) s * x * (QuotientGroup.mk' (pCore 2 H) s)⁻¹ = x⁻¹) :
    d.B ≤ C ⊔ (J).pCoreIn 2 := by
  have hBJH : J ≤ H := sup_le
    ((borel_le_component _ _ _ _ _).trans d.component_le) d.one_le_H
  have hXH : X ≤ H := (plus_le_one L (T : Subgroup G) V₁ a.line_stable).trans d.one_le_H
  have hsC : s.val ∈ normalizer (C : Set G) :=
    centralizingResidual_normalized _ _ _ (T : Subgroup G) d.product_normalizes_L
      d.T_normalizes_product d.standing.normalizes_L hsT
  exact le_sup_twoCore_of_fixed_inverted_cubic d.B C X J (product_eq d a hfactor).symm
    (product_normalizes_centralizingResidual d) le_sup_left
    (plus_core_le_product_core d a) (cubic_index d a hfactor)
    ⟨s.val, d.T_normalizes_product hsT⟩ hsC
    (inversion_of_star_inversion H X hXH hnX s hinv).2
    ((source_commutator_le_core_intersection d s hsT hs).trans
      (ambient_core_intersection_le H J hBJH))

include a hfactor in
theorem borel_le_centralizingResidual_of_star_inverter
    (hnX : ((X).subgroupOf H).Normal)
    (s : H) (hsT : s.val ∈ (T : Subgroup G))
    (hs : QuotientGroup.mk' (pCore 2 H) s ∈
      centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hinv : ∀ x ∈ Source.starImage H X,
      QuotientGroup.mk' (pCore 2 H) s * x * (QuotientGroup.mk' (pCore 2 H) s)⁻¹ = x⁻¹) :
    d.B ≤ C :=
  le_normal_of_twoPerfect_le_sup_twoCore d.B C J (centralizingResidual_le _ _ _) le_sup_left
    (product_normalizes_centralizingResidual d) (borel_isPPerfect d)
    (borel_le_sup_core_of_star_inverter d a hfactor hnX s hsT hs hinv)

/-- The previously checked natural-action calculation centralizes all of V. -/
theorem centralizingResidual_le_centralizer : C ≤ centralizer (V : Set G) :=
  (residual_le _).trans (DegenerateAction.NaturalKernel.borelCentralizer_le_centralizer d)

include a hfactor in
theorem borel_centralizes_of_star_inverter
    (hnX : ((X).subgroupOf H).Normal)
    (s : H) (hsT : s.val ∈ (T : Subgroup G))
    (hs : QuotientGroup.mk' (pCore 2 H) s ∈
      centralizer (Source.starImage H K : Set (Source.Hstar H)))
    (hinv : ∀ x ∈ Source.starImage H X,
      QuotientGroup.mk' (pCore 2 H) s * x * (QuotientGroup.mk' (pCore 2 H) s)⁻¹ = x⁻¹) :
    d.B ≤ centralizer (V : Set G) :=
  (borel_le_centralizingResidual_of_star_inverter d a hfactor hnX s hsT hs hinv).trans
    (centralizingResidual_le_centralizer d)

include a hfactor in
theorem borel_centralizes_of_Tstar_inverter
    (hnX : ((X).subgroupOf H).Normal)
    (hw : ∃ s ∈ Source.starImage H (T : Subgroup G) ⊓
      centralizer (Source.starImage H K : Set (Source.Hstar H)),
      ∀ x ∈ Source.starImage H X, s * x * s⁻¹ = x⁻¹) :
    d.B ≤ centralizer (V : Set G) := by
  obtain ⟨s, ⟨hsT, hsC⟩, hinv⟩ := hw
  obtain ⟨sH, hsH, rfl⟩ := hsT
  exact borel_centralizes_of_star_inverter d a hfactor hnX sH hsH hsC hinv

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.LocalBorel.CentralizingCalculation.Covered.ZeroPlacement.FullProduct.External
