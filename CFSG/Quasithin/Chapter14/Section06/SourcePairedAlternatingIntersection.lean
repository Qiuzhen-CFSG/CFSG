module
public import CFSG.Quasithin.Chapter14.Section06.SourceParabolicNaturalBlockExclusion
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.AlternatingPairIntersection

/-!
# The paired-A₅ intersection from the original 14.6.9 hypotheses

The natural-block exclusion leaves the actual two-block C.5 orbit. Its
marked pair constructs one conjugator with all invariant-family conclusions
and the rank-four intersection formula. We retain its membership in the
chosen index-two extension inside T, the literal residual core of order 256,
and its intersection of order 16 with its conjugate.

Source: Aschbacher--Smith, 14.6.9(k)--(l), printed p.1027,
using C.5.6(7)(iii).
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterC ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (hU3 : Mc ⊓ normalizer (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u : Set G) =
        (T : Subgroup G))
    (hlocal : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (H ⊓ centralizer ({u} : Set G)))

include hG hempty hM hunique hmany hcard e hab H hH hu hindex hmove hproduct hU3 hlocal


/-- The source paired alternative retains the same conjugator for its
invariant family and its rank-four residual-core intersection. -/
theorem source_characteristicTwo_paired_intersection_or_factorization
    (hcoreIndex : 4 < (H.pCoreIn 2).relIndex (T : Subgroup G))
    (hrank : 4 ≤ Nat.log 2 ((centralizer (H.pCoreIn 2 : Set G)).relIndex
      (conjugateSpanBy (localModule T M) H)))
    (I : Subgroup G) (hf : generalizedFitting I = pCore 2 I)
    (hI : I ∈ IMin (T : Subgroup G) (outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)) :
    (let R := (T : Subgroup G) ⊓ I
     let K := (pResidual 2 I).map I.subtype
     (∃ Λ : Subgroup G, Λ ≤ (T : Subgroup G) ∧ R.relIndex Λ = 2 ∧
       ∃ c : OriginalHypotheses I Λ K R R,
       ∃ hP : ChapterB.IsMinimalParabolicOver c.sylow ⊤,
       ChapterB.minimalParabolicMax c.sylow hP = (I ⊓ Mc).subgroupOf I ∧
       ∃ b : OrbitDecomposition (c.sylow : Subgroup I) (R.subgroupOf I) (pResidual 2 I),
       ∃ i j : Fin b.size, i ≠ j ∧ b.size = 2 ∧
       IsAlternatingBlock ((b.block i).map I.subtype) 5 ∧
       ∃ x ∈ Λ, x ∈ (T : Subgroup G) ∧ x ∉ R ∧
       let D := R ⊓ centralizer (K : Set G)
       let Q := I.pCoreIn 2
       (frattini D).map D.subtype = ⊥ ∧
       D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
       Q = K.pCoreIn 2 ⊔ D ∧
       Q ∈ elementaryAbelianMaxSubgroups R ∧
       ChapterB.baumann R = elementaryAbelianMaxJ R ∧
       {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} =
         {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} ∧
       K.pCoreIn 2 ⊓ (K.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom =
         ⁅K.pCoreIn 2, (K.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom⁆ ∧
       Nat.card (K.pCoreIn 2 ⊓ (K.pCoreIn 2).map
         (MulAut.conj x⁻¹).toMonoidHom : Subgroup G) = 16 ∧
       Nat.card (K.pCoreIn 2) = 256)) ∨
    (let L := sourceResidual M Mc
     let LI := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (LI : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (LI : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_characteristicTwo_paired_or_factorization hG T hempty hM hunique hmany
    hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hf hI with
    ⟨Λ,hΛ,hi,c,hP,hmax,b,i,j,hij,hs,h5,_⟩ | hfactor
  · obtain ⟨x,hx,hout,hgeom⟩ := c.alternating_pair_family_intersection b i j hij hs h5 hi
    exact Or.inl ⟨Λ,hΛ,hi,c,hP,hmax,b,i,j,hij,hs,h5,x,hx,hΛ hx,hout,hgeom⟩
  · exact Or.inr hfactor

end CFSG.Quasithin.Chapter14.Section06
