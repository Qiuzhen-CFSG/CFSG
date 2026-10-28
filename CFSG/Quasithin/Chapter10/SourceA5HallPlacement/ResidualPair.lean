module
public import CFSG.Quasithin.Chapter10.SourceA5OriginalProductQuotient
public import CFSG.Quasithin.Chapter4.Section04.PerfectCentralizer
public import Theory.GroupTheory.PCoreCoverEquiv
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.CoprimeRank
public import Theory.Alternating.PrimeRank

/-!
# The original fixed residual retains both A₅ factors

The odd actor fixes a perfect residual F covering the original orbit X
modulo O₂(X). The literal inclusion therefore identifies F/O₂(F) with
X/O₂(X). Composing with the original marked product projection gives an
actual surjection F → A₅ × A₅ with kernel O₂(F), and retains its value on
every element of F. Consequently F has rank two at both 3 and 5.

The component-placement consumer transfers these ranks to the actual
component of N_G(B), once the independent placement argument puts F there.
Source: Aschbacher–Smith, 4.4.5 and 4.4.11–12, printed pp.620–622,
as used for the original nonnormal pair in 10.2.3, printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
  (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
include D e hn

/-- The fixed residual maps onto the original marked pair by its literal
inclusion, with its intrinsic two-core as kernel. -/
theorem source_a5_oddActorResidual_product_projection
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) :
    ∃ f : ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype) →*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      Function.Surjective f ∧ f.ker = pCore 2 (((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype)) ∧
      ∀ x : ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype),
        f x = originalA5ProductProjection D e hn ht htn
          ⟨x, ((map_subtype_le (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G))).trans inf_le_left) x.property⟩ := by
  let X := localOrbit T L
  let F := (solvableResidual (X ⊓ centralizer (B : Set G) : Subgroup G)).map
    (X ⊓ centralizer (B : Set G)).subtype
  let := Chapter1.mem_L_isPerfect D.maximal.1
  let : Group.IsPerfect X := isPerfect_iSup_conjugates L (T : Subgroup G)
  have hFX : F ≤ X := (map_subtype_le _).trans inf_le_left
  have hcover : (X : Set G) = (F : Set G) * (X.pCoreIn 2 : Set G) :=
    perfect_centralizer_cover X B hBC hodd
  obtain ⟨a,ha⟩ := exists_pCoreQuotientEquiv_of_cover hFX hcover.subset
  let q := originalA5ProductProjection D e hn ht htn
  let b : (X ⧸ pCore 2 X) ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq
      (originalA5ProductProjection_ker D e hn ht htn).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q
        (originalA5ProductProjection_surjective D e hn ht htn))
  let f := (a.trans b).toMonoidHom.comp (QuotientGroup.mk' (pCore 2 F))
  refine ⟨f,(a.trans b).surjective.comp (QuotientGroup.mk'_surjective _),?_,?_⟩
  · ext x
    change (a.trans b) (QuotientGroup.mk' (pCore 2 F) x) = 1 ↔ x ∈ pCore 2 F
    rw [map_eq_one_iff (a.trans b) (a.trans b).injective]
    exact QuotientGroup.eq_one_iff x
  · intro x
    change b (a (QuotientGroup.mk' (pCore 2 F) x)) = q (inclusion hFX x)
    rw [ha]
    rfl

/-- The original fixed residual has an actual A₅ × A₅ quotient map with
kernel its full intrinsic two-core. -/
theorem source_a5_oddActorResidual_product_quotient
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) :
    ∃ f : ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype) →*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5),
      Function.Surjective f ∧ f.ker = pCore 2 (((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype)) := by
  obtain ⟨t,ht,htn⟩ := Set.not_subset.mp hn
  obtain ⟨f,hf,hk,_⟩ := source_a5_oddActorResidual_product_projection D e hn ht htn B hBC hodd
  exact ⟨f,hf,hk⟩

/-- The quotient marking of the literal fixed residual. -/
theorem source_a5_oddActorResidual_quotient_equiv
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) :
    Nonempty ((((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype) ⧸
      pCore 2 (((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype))) ≃*
        alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
  obtain ⟨f,hf,hk⟩ := source_a5_oddActorResidual_product_quotient D e hn B hBC hodd
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- Both odd prime ranks of the original fixed residual are exactly two. -/
theorem source_a5_oddActorResidual_primeRank
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5) :
    primeRank p (((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype)) = 2 := by
  obtain ⟨a⟩ := source_a5_oddActorResidual_quotient_equiv D e hn B hBC hodd
  have ho : Odd p := by rcases hp with rfl | rfl <;> decide
  rw [←primeRank_quotient_eq_of_isTwoGroup p ho
    (pCore 2 (((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype))) pCore_isPGroup,
    primeRank_congr p a,primeRank_prod_eq_add]
  rcases hp with rfl | rfl <;>
    rw [GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 5 _ (by decide) (by decide)]

/-- Once the source placement puts the fixed residual in the selected
component of N_G(B), that actual component has both required odd ranks. -/
theorem source_a5_oddNormalizer_component_primeRank_of_residual_le
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype) ≤ K.map (normalizer (B : Set G)).subtype)
    {p : ℕ} [Fact p.Prime] (hp : p = 3 ∨ p = 5) : 2 ≤ primeRank p K := by
  have hr := primeRank_mono p hFK
  rw [source_a5_oddActorResidual_primeRank D e hn B hBC hodd hp,
    ←primeRank_congr p (K.equivMapOfInjective
      (normalizer (B : Set G)).subtype (normalizer (B : Set G)).subtype_injective)] at hr
  exact hr

end CFSG.Quasithin.Chapter10
