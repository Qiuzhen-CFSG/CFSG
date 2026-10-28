module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.TransvectionModules.Quotients.FiveSeed.Cover
public import Theory.GroupTheory.CComponent.Basic
/-!
# Literal source seed in the five-dimensional branch

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, printed p.948, Lemma 13.8.6(5).

We construct the coordinate projection from UH/V₁ itself and the actor map
from the actual image K* in H/O₂(H). The source flag of order two is central
in H, and a genuine C-component is two-perfect. The cover calculation then
proves both the seed index and [L₁T,U₁] ≤ V₁. The earlier index-two flag and
13.7.7 noncentrality establish V ∩ UH = V₃. The weight-four marking and L₁ ≤ K
are precise earlier 13.7.6/parabolic inputs; their source applicability is not
asserted by this adapter. We also prove normalization of the L-conjugate span.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed
open BinaryPermutation
variable {G : Type*} [Group G]

/-- The actual projection of K onto its image in H/O₂(H). -/
def starProjection (H K : Subgroup G) (hKH : K ≤ H) : K →* Source.starImage H K :=
  ((QuotientGroup.mk' (pCore 2 H)).comp (inclusion hKH)).codRestrict _
    (fun k => ⟨⟨k, hKH k.property⟩, k.property, rfl⟩)

theorem starProjection_surjective (H K : Subgroup G) (hKH : K ≤ H) :
    Function.Surjective (starProjection H K hKH) := by
  rintro ⟨x, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

/-- The coordinate projection is constructed from the literal section. -/
def coverProjection (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6)) :
    Source.UH H V₃ →* Multiplicative (core (Fin 6)) where
  toFun u := Multiplicative.ofAdd (e (Additive.ofMul (QuotientGroup.mk' _ u)))
  map_one' := by change e (Additive.ofMul (QuotientGroup.mk' _ 1)) = 0; simp
  map_mul' u v := by
    change e (Additive.ofMul (QuotientGroup.mk' _ (u * v))) =
      e (Additive.ofMul (QuotientGroup.mk' _ u)) + e (Additive.ofMul (QuotientGroup.mk' _ v))
    rw [map_mul]
    exact e.map_add _ _

theorem coverProjection_surjective (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6)) :
    Function.Surjective (coverProjection H V₃ V₁ e) := by
  intro x
  obtain ⟨y, hy⟩ := e.surjective x.toAdd
  obtain ⟨u, hu⟩ := QuotientGroup.mk'_surjective (V₁.subgroupOf (Source.UH H V₃)) y.toMul
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  change e (Additive.ofMul (QuotientGroup.mk' _ u)) = x.toAdd
  rw [hu]
  exact hy

theorem coverProjection_kernel (H V₃ V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)]
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6)) (u : Source.UH H V₃) :
    coverProjection H V₃ V₁ e u = 1 ↔ (u : G) ∈ V₁ := by
  change e (Additive.ofMul (QuotientGroup.mk' _ u)) = 0 ↔ _
  rw [e.map_eq_zero_iff]
  exact QuotientGroup.eq_one_iff u

/-- Normalizing a subgroup also normalizes its centralizer. -/
theorem centralizer_normalized (K R : Subgroup G)
    (hRK : R ≤ normalizer (K : Set G)) :
    R ≤ normalizer (centralizer (K : Set G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro r hr x hx y hy
  let f : G ≃* G := MulAut.conj r
  have hfy : f.symm y ∈ K := (hRK hr (f.symm y)).mpr (by
    change f (f.symm y) ∈ K
    rw [f.apply_symm_apply]
    exact hy)
  have he := congrArg f (hx (f.symm y) hfy)
  change y * f x = f x * y
  simpa only [map_mul, f.apply_symm_apply] using he

private theorem normalizer_fixes_two (A : Subgroup G) (hA : Nat.card A = 2) :
    normalizer (A : Set G) ≤ centralizer (A : Set G) := by
  obtain ⟨z, _, hzuniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  intro g hg
  apply mem_centralizer_iff.mpr
  intro x hx
  by_cases hxone : x = 1
  · simp [hxone]
  let xA : A := ⟨x, hx⟩
  let yA : A := ⟨g * x * g⁻¹, (hg x).mp hx⟩
  have hyne : yA ≠ 1 := by
    intro hy
    have hy' : g * x * g⁻¹ = 1 := congrArg Subtype.val hy
    apply hxone
    have h := congrArg (fun a : G => g⁻¹ * a * g) hy'
    simpa [mul_assoc] using h
  have heq : yA = xA := (hzuniq yA hyne).trans (hzuniq xA (by
    intro hx'; exact hxone (congrArg Subtype.val hx'))).symm
  have heq' : g * x * g⁻¹ = x := congrArg Subtype.val heq
  have h := congrArg (fun a : G => a * g) heq'
  simpa [mul_assoc] using h.symm

/-- The order-two standing flag is centralized by every subgroup of H. -/
theorem flag_centralizes_component (H K V₁ : Subgroup G)
    (hKH : K ≤ H) (hHV₁ : H ≤ normalizer (V₁ : Set G)) (hcard : Nat.card V₁ = 2) :
    V₁ ≤ centralizer (K : Set G) :=
  le_centralizer_iff.mpr (hKH.trans (hHV₁.trans (normalizer_fixes_two V₁ hcard)))

/-- The first flag lies in the source conjugate span. -/
theorem flag_le_UH (H V₃ V₁ : Subgroup G) (hflag : V₁ ≤ V₃) :
    V₁ ≤ Source.UH H V₃ := hflag.trans (le_conjugateSpanBy V₃ H)

/-- Normalization of the component makes T normalize the actual seed;
normalization of L then makes LT normalize its L-conjugate span. -/
theorem U0_normalized (L H K T V₃ : Subgroup G)
    (hTH : T ≤ H) (hTK : T ≤ normalizer (K : Set G))
    (hTL : T ≤ normalizer (L : Set G)) :
    L ⊔ T ≤ normalizer (Source.U0 L H K V₃ : Set G) := by
  apply sup_le (le_normalizer_conjugateSpanBy _ L)
  apply normalizes_conjugate_span T (Source.U1 H K V₃) L _ hTL
  exact (le_inf (hTH.trans (le_normalizer_conjugateSpanBy V₃ H))
    (centralizer_normalized K T hTK)).trans inf_normalizer_le_normalizer_inf

private theorem component_twoPerfect [Finite G] (H K : Subgroup G) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) : IsPPerfect 2 K := by
  have : Group.IsPerfect K := by
    let := hK.perfect
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe hKH).toMonoidHom)
      (subgroupOfEquivOfLe hKH).surjective
  intro N hN hp
  let := hN
  have hsub : Subsingleton (K ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (K ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro k _
  exact (QuotientGroup.eq_one_iff k).mp (Subsingleton.elim _ _)

/-- Source seed index and local commutator bound from an actual A₆ image and
an equivariant identification of the literal five-dimensional cover. The
weight-four flag and L₁ ≤ K are the precise earlier parabolic inputs. -/
theorem source_seed_index_and_commutator [Finite G]
    (H K T L₁ V₃ V V₁ : Subgroup G)
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    [IsElementaryAbelian 2 (Source.Utilde H V₃ V₁)] [IsElementaryAbelian 2 V₁]
    (hKH : K ≤ H) (hK : (K.subgroupOf H).IsCComponent)
    (hTH : T ≤ H) (hTK : T ≤ normalizer (K : Set G)) (hL₁K : L₁ ≤ K)
    (hHV₁ : H ≤ normalizer (V₁ : Set G)) (hcard : Nat.card V₁ = 2)
    (hV₃V : V₃ ≤ V) (hindex : V₃.relIndex V = 2)
    (hnoncentral : ¬ ⁅Source.VH H V, H⁆ ≤ Source.UH H V₃) (hV₁V : V₁ ≤ V)
    (eK : Source.starImage H K ≃* alternatingGroup (Fin 6))
    (e : Additive (Source.Utilde H V₃ V₁) ≃ₗ[ZMod 2] core (Fin 6))
    (heq : ∀ (k : K) (u : Source.UH H V₃),
      e (Additive.ofMul (QuotientGroup.mk' _
        ⟨(k : G) * u * (k : G)⁻¹,
          (mem_normalizer_iff.mp
            (le_normalizer_conjugateSpanBy V₃ H (hKH k.property)) u).mp u.property⟩)) =
        alternatingCoreRepresentation (Fin 6) (eK (starProjection H K hKH k))
          (e (Additive.ofMul (QuotientGroup.mk' _ u))))
    (hweight : ∀ u : Source.UH H V₃, (u : G) ∈ V₃ →
      e (Additive.ofMul (QuotientGroup.mk' _ u)) = 0 ∨
        Fintype.card {i : Fin 6 //
          (e (Additive.ofMul (QuotientGroup.mk' _ u))).val i ≠ 0} = 4) :
    V.relIndex (Source.U1 H K V₃) = 2 ∧ ⁅L₁ ⊔ T, Source.U1 H K V₃⁆ ≤ V₁ := by
  let q := coverProjection H V₃ V₁ e
  let α := eK.toMonoidHom.comp (starProjection H K hKH)
  have hα : Function.Surjective α := eK.surjective.comp (starProjection_surjective H K hKH)
  have hKU : K ≤ normalizer (Source.UH H V₃ : Set G) :=
    hKH.trans (le_normalizer_conjugateSpanBy V₃ H)
  have hVU : V ⊓ Source.UH H V₃ = V₃ :=
    (flag_intersection_of_index_two V V₃ (Source.UH H V₃)
      (le_inf hV₃V (le_conjugateSpanBy V₃ H)) hindex
      (seed_not_le_UH_of_noncentral H V V₃ hnoncentral)).symm
  have hc := flag_centralizes_component H K V₁ hKH hHV₁ hcard
  have hp := component_twoPerfect H K hKH hK
  constructor
  · exact centralizer_seed_index _ V₁ K hp hc hKU q
      (coverProjection_kernel H V₃ V₁ e) α hα heq V V₃
      (coverProjection_surjective H V₃ V₁ e) hVU hV₁V hweight
  · have hRH : L₁ ⊔ T ≤ H := sup_le (hL₁K.trans hKH) hTH
    exact centralizer_commutator_le _ V₁ K hp hc hKU q
      (coverProjection_kernel H V₃ V₁ e) α hα heq (L₁ ⊔ T)
      (hRH.trans (le_normalizer_conjugateSpanBy V₃ H)) (hRH.trans hHV₁)
      (centralizer_normalized K _ (sup_le (hL₁K.trans K.le_normalizer) hTK))

end CFSG.Quasithin.Chapter13.Section08.TransvectionQuotients.FiveSeed

end
