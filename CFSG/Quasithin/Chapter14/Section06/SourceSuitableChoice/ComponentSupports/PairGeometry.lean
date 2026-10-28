module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry
public import Theory.GroupTheory.PairNormalizerIndex

/-!
# The index and separated supports from a two-member orbit

If T permutes two K-invariant supports and moves the first, its literal
normalizer N_T(W) has index two. Each element outside this normalizer sends
W to the second support, including for the inverse-conjugation convention
used in the source. Their intersection bound supplies separation.

The last theorem applies this to the terminal suitable-vector construction.
The pair, its intersection bound and N_Mc(N_T(W))=T remain explicit source
inputs; they must be derived from the original component modules. In a
covered-module branch, directness after quotienting by fixed points alone
must not be substituted for the displayed intersection bound modulo Z.

Source: Aschbacher--Smith, 14.6.22 and the proof of 14.6.24(1), pp.1038--1039.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Representation Representation.OneCohomology
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- A moved pair of supports gives the literal normalizer, its index two,
and all the separated conjugates in the right-conjugation source convention. -/
theorem geometry_of_pair
    (T : Sylow 2 G) (Mc U K W W' : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ U) (hZW : centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hKW' : K ≤ normalizer (W' : Set G))
    (hsep : W ⊓ W' ≤ centralInvolutions T)
    (hpair : ∀ t ∈ (T : Subgroup G), W.map (MulAut.conj t).toMonoidHom = W ∨
      W.map (MulAut.conj t).toMonoidHom = W')
    (x : G) (hx : x ∈ (T : Subgroup G))
    (hmove : W.map (MulAut.conj x).toMonoidHom ≠ W)
    (hlocal : Mc ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (W : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G)) :
    Geometry T Mc U K W ((T : Subgroup G) ⊓ normalizer (W : Set G)) := by
  refine ⟨hK,hWU,hZW,hKW,inf_le_left,?_,hlocal,?_⟩
  · rw [inf_relIndex_left]
    exact normalizer_relIndex_eq_two_of_pair (T : Subgroup G) W W' hpair x hx hmove
  · intro t ht htS
    have hn : W.map (MulAut.conj t⁻¹).toMonoidHom ≠ W := by
      intro he
      have hi : t⁻¹ ∈ normalizer (W : Set G) := mem_normalizer_iff_map_conj_eq.mpr he
      have htN : t ∈ normalizer (W : Set G) := by
        simpa only [inv_inv] using (normalizer (W : Set G)).inv_mem hi
      exact htS ⟨ht,htN⟩
    have he := (hpair t⁻¹ ((T : Subgroup G).inv_mem ht)).resolve_left hn
    rw [he]
    exact ⟨hsep,hKW'⟩

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

/-- The pair geometry supplies the index and separated-support premises of
the actual suitable-vector consumer, with S equal to N_T(W). -/
theorem source_exists_of_pair_section_vector
    (K W W' A : Subgroup G)
    (hK : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc)
    (hWU : W ≤ conjugateSpanBy (localModule T M) Mc)
    (hZW : centralInvolutions T ≤ W)
    (hKW : K ≤ normalizer (W : Set G))
    (hKW' : K ≤ normalizer (W' : Set G))
    (hsep : W ⊓ W' ≤ centralInvolutions T)
    (hpair : ∀ t ∈ (T : Subgroup G), W.map (MulAut.conj t).toMonoidHom = W ∨
      W.map (MulAut.conj t).toMonoidHom = W')
    (x : G) (hx : x ∈ (T : Subgroup G))
    (hmove : W.map (MulAut.conj x).toMonoidHom ≠ W)
    (hlocal : Mc ⊓ normalizer (((T : Subgroup G) ⊓ normalizer (W : Set G) : Subgroup G) : Set G) =
      (T : Subgroup G))
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) A V)
    (c : BinaryConjugationSection A W (centralInvolutions T) τ)
    (hSA : (T : Subgroup G) ⊓ normalizer (W : Set G) ≤ A) (v : V)
    (hfixed : ∀ (s : G) (hs : s ∈ (T : Subgroup G) ⊓ normalizer (W : Set G)),
      τ ⟨s,hSA hs⟩ v = v)
    (hmoved : v ∉ fixed (τ.comp (K.subgroupOf A).subtype)) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧
      suitableQuotientCentralizer h u = (T : Subgroup G) ⊓ normalizer (W : Set G) ∧
      Suitable h Mc u := by
  apply source_exists_of_section_vector hG T hempty hM hunique hmany hcard e hab
    K W ((T : Subgroup G) ⊓ normalizer (W : Set G)) A _ τ c hSA v hfixed hmoved
  exact geometry_of_pair T Mc _ K W W' hK hWU hZW hKW hKW' hsep hpair x hx hmove hlocal
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
