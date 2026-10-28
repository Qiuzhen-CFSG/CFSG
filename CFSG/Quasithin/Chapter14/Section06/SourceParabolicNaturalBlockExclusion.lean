module
public import CFSG.Quasithin.Chapter14.Section06.SourceCharacteristicTwoBlocks
public import CFSG.Quasithin.Chapter14.Section06.SourceIntersection
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.NaturalCentrality

/-!
# Excluding the natural-block branch of original14.6.9

The involution supplied by14.6.7 centralizes the marked unique maximal
Sylow overgroup I∩Mc. If the original C.5 orbit contained a natural block,
its center-rigidity theorem would make this involution central in I.
The original outside-family condition I≰Mc contradicts this conclusion.

Applying this exclusion to the constructed characteristic-two source orbit
leaves the paired A₅ core and invariant elementary-subgroup family, or the
literal L/LT factorization. The original rank and index conditions remain;
no block choice, odd actor, center-rigidity or model callback is assumed.
The later paired A₅ contradiction remains a separate source obligation.

Source: Aschbacher--Smith14.6.9, printed pp.1025--1027.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterC ChapterC.Section05.BlockAnalysis
variable {G : Type*} [Group G] [Finite G]

/-- The actual marked involution excludes every natural block of the
original residual orbit, including its literal ambient subgroup image. -/
theorem source_parabolic_natural_block_exclusion
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (I : Subgroup G) (hf : generalizedFitting I = pCore 2 I)
    (hI : I ∈ outsideOvergroups (Chapter1.H G)
      ((T : Subgroup G) ⊓ centralizer ({u} : Set G)) Mc M)
    (S : Sylow 2 I) (hS : (S : Subgroup I).map I.subtype = (T : Subgroup G) ⊓ I)
    (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (hmax : ChapterB.minimalParabolicMax S hP = (I ⊓ Mc).subgroupOf I)
    {R : Subgroup I} (b : OrbitDecomposition (S : Subgroup I) R (pResidual 2 I))
    (i : Fin b.size) {n : ℕ} (hnat : IsL2EvenBlock ((b.block i).map I.subtype) n) : False := by
  obtain ⟨⟨z,hz,h115⟩,_,_⟩ := source_lemma_14_6_7_initial hG T hempty hM
    hunique hmany hcard e hab H hH u hu I hI S hS
  have hzI : z ∈ I := (map_subtype_le (S : Subgroup I)) h115.mem_sylow
  let zi : I := ⟨z,hzI⟩
  have hzi2 : zi^2=1 := by
    apply Subtype.ext
    exact h115.involution ▸ pow_orderOf_eq_one z
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  have hMc := (plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ).2.2.1
  have hziB : zi ∈ centralizer (ChapterB.minimalParabolicMax S hP : Set I) := by
    intro a ha
    rw [hmax] at ha
    exact Subtype.ext ((hMc ▸ ha.2) z hz).symm
  have hnint : IsL2EvenBlock (b.block i) n :=
    hnat.of_mulEquiv (equivMapOfInjective (b.block i) I.subtype I.subtype_injective).symm
  have hzcenter := b.natural_central_involution S hP hf i hnint zi hzi2 hziB
  apply hI.2.2.1
  intro x hx
  apply h115.centralizer_le
  apply mem_centralizer_singleton_iff.mpr
  exact congrArg I.subtype (mem_center_iff.mp hzcenter ⟨x,hx⟩)

open Stellmacher
open scoped Pointwise

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


/-- The characteristic-two branch of original14.6.9 has the actual paired
A₅ geometry or the claimed factorization. The natural alternative is discharged. -/
theorem source_characteristicTwo_paired_or_factorization
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
       ∃ x ∈ (T : Subgroup G), x ∉ R ∧
       let D := R ⊓ centralizer (K : Set G)
       let Q := I.pCoreIn 2
       (frattini D).map D.subtype = ⊥ ∧
       D ⊓ D.map (MulAut.conj x⁻¹).toMonoidHom = ⊥ ∧
       Q = K.pCoreIn 2 ⊔ D ∧
       Q ∈ elementaryAbelianMaxSubgroups R ∧
       ChapterB.baumann R = elementaryAbelianMaxJ R ∧
       {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} =
         {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom})) ∨
    (let L := sourceResidual M Mc
     let LI := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
     (L : Set G) = (LI : Set G) * (L.pCoreIn 2 : Set G) ∧
       (L ⊔ (T : Subgroup G) : Subgroup G) =
         (LI : Set G) * ((T : Subgroup G) ⊓ I : Subgroup G) *
           ((L ⊔ (T : Subgroup G)).pCoreIn 2 : Set G)) := by
  rcases source_characteristicTwo_natural_or_paired_or_factorization hG T hempty hM hunique
    hmany hcard e hab H hH u hu hindex hmove hproduct hU3 hlocal hcoreIndex hrank I hf hI with
    ⟨Λ,hΛ,hi,c,hP,hmax,b,hn | hp⟩ | hfactor
  · obtain ⟨i,n,hnat⟩ := hn
    exact (source_parabolic_natural_block_exclusion hG T hempty hM hunique hmany hcard e
      hab H hH u hu I hf hI.1.1 c.sylow c.sylow_image hP hmax b i hnat).elim
  · exact Or.inl ⟨Λ,hΛ,hi,c,hP,hmax,b,hp⟩
  · exact Or.inr hfactor

end CFSG.Quasithin.Chapter14.Section06
