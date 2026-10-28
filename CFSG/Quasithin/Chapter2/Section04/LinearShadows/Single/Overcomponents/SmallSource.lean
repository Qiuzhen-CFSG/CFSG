module
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.Overcomponents.CenterMark
public import CFSG.Quasithin.Chapter2.Section04.LinearShadows.Single.ModelSource.Geometry
/-!
# Literal original-source small overcomponent tests

The actual mapped block and its original core equality discharge the numerical
model exclusions. The binary Mathieu residue also uses the center order proved
from the original torus, preserving every original quotient and embedding.
Source: Aschbacher–Smith 2.4.11, printed p.532.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter2.LinearShadows.Single
open ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]
variable {M : Subgroup G} (d : MinimalBlockSetup M)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hST : (d.S : Subgroup d.H).map d.H.subtype < (T : Subgroup G))
    (hsingle : d.L0 = d.block) {n : ℕ} (hL : ChapterC.IsL2EvenBlock d.block n)

include hG T hST hsingle hL
lemma source_overcomponent_not_alternating_six
    (K : Subgroup G) (hLK : d.block.map d.H.subtype ≤ K)
    (e : (K ⧸ center K) ≃* alternatingGroup (Fin 6)) : False := by
  have h := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  exact Overcomponents.no_alternating_six h
    (source_block_core_eq_module d hG T hST hsingle) (inclusion hLK)
    (inclusion_injective hLK) e

lemma source_overcomponent_psl_three_four_degree
    (K : Subgroup G) (hLK : d.block.map d.H.subtype ≤ K)
    (e : (K ⧸ center K) ≃* Matrix.PSL3Four.PSL) : n = 2 := by
  have h := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  exact Overcomponents.degree_two_of_psl_three_four h
    (source_block_core_eq_module d hG T hST hsingle) (inclusion hLK)
    (inclusion_injective hLK) e

lemma source_overcomponent_not_binary_m22
    (hM : IsMaximalTwoLocal M) (hTM : (T : Subgroup G) ≤ M)
    (hunique : ∀ J : Subgroup G, IsMaximalTwoLocal J → (T : Subgroup G) ≤ J → J = M)
    (hZ : center (d.block.map d.H.subtype) ≠ ⊥)
    (K : Subgroup G) (hLK : d.block.map d.H.subtype ≤ K)
    (hcard : Nat.card (pCore 2 K) = 2)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.Mathieu.M22) : False := by
  obtain ⟨_,D,_,_,_,x,_,_,_,hz⟩ :=
    source_center_torus_and_splitting d hG T hST hsingle hL hM hTM hunique
  have hzcard := (hz.resolve_left hZ).1
  have h := hL.of_mulEquiv (equivMapOfInjective d.block d.H.subtype d.H.subtype_injective)
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact Overcomponents.no_binary_m22 h
    (source_block_core_eq_module d hG T hST hsingle) hzcard (inclusion hLK)
    (inclusion_injective hLK) q (by rw [hq,hcard])
end CFSG.Quasithin.Chapter2.LinearShadows.Single
