module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice
public import Theory.Representation.BinaryConjugationSection.FixedMoving

/-!
# Component supports and their original-action vector consumer

The terminal group is the original Mc. The geometry below records the
separated-support input still to be constructed by 14.6.20--23. It is a
conditional interface, not an assertion of those source lemmas.

A fixed-moving vector in a literal binary section lifts through its exact
central-line kernel. Applying the separated-support argument then proves
(U0)--(U3) for that same element and that same terminal group. In particular,
the vector input permits the nonzero fixed kernel of the five-dimensional
A6 cover. Its producer must use I.2.3, rather than a fixed-free assertion.

Source: Aschbacher--Smith, 14.6.20--24, printed pp.1037--1039;
(U0)--(U3), printed p.1021.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Representation Representation.OneCohomology
variable {G : Type*} [Group G] [Finite G]

/-- The common geometric input of the natural and covered component branches.
The branch producer must identify W and S with the literal source supports
and their normalizers; this record alone asserts no component classification. -/
structure Geometry (T : Sylow 2 G) (Mc U K W S : Subgroup G) : Prop where
  fitting : K ≤ ChapterA.Section04.twoGeneralizedFittingPreimage Mc
  support_le : W ≤ U
  point_le : centralInvolutions T ≤ W
  normalized : K ≤ normalizer (W : Set G)
  sylow_le : S ≤ (T : Subgroup G)
  index : S.relIndex (T : Subgroup G) = 2
  local_normalizer : Mc ⊓ normalizer (S : Set G) = (T : Subgroup G)
  separated : ∀ t ∈ (T : Subgroup G), t ∉ S →
    W ⊓ W.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralInvolutions T ∧
    K ≤ normalizer (W.map (MulAut.conj t⁻¹).toMonoidHom : Set G)

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))

include hG hempty hM hunique hmany hcard e

/-- The terminal source group really is an outside overgroup of the original T. -/
theorem terminal_outside : Mc ∈ Chapter1.HOutside G (T : Set G) (M : Set G) := by
  have hZ : Nat.card (centralInvolutions T) = 2 :=
    plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,hne,hMc,_⟩ :=
    plane_ordering_and_overgroups hG T hempty hM hunique hmany hcard hZ
  have hmax : IsMaximalTwoLocal Mc :=
    (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).1
  have hTMc : (T : Subgroup G) ≤ Mc := by
    rw [hMc]
    exact le_centralizer_iff.mp (centralInvolutions_le_centralizer_sylow T)
  exact ⟨⟨Chapter1.mem_H_of_isTwoLocal hmax.1,hTMc⟩,
    fun hh => hne (hmax.eq_of_le hM.1.1.1 hh).symm⟩

include hab in
/-- F.9 on the terminal H=Mc, with no replacement of the original ambient action. -/
theorem terminal_hypothesis : ChapterF.Section09.Setup.Hypothesis
    { T := T, L := sourceResidual M Mc, V := localModule T M,
      Vplus := localModule T M, V₁ := centralInvolutions T, H := Mc } :=
  source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab Mc
    (terminal_outside hG T hempty hM hunique hmany hcard e)

/-- The original (U0)--(U3), before the later 14.6.24 classification clauses. -/
@[expose] def Suitable {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    (Mc : Subgroup G) (u : G) : Prop :=
  u ∈ D.UH ∧
    Chapter1.IsSylowIn 2 ((D.T : Subgroup G) ⊓ centralizer ({u} : Set G))
      (D.H ⊓ centralizer ({u} : Set G)) ∧
    (suitableQuotientCentralizer h u).relIndex (D.T : Subgroup G) = 2 ∧
    ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G) ∧
    (∀ t ∈ (D.T : Subgroup G), t ∉ suitableQuotientCentralizer h u →
      ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G)) ∧
    Mc ⊓ normalizer (suitableQuotientCentralizer h u : Set G) = (D.T : Subgroup G)

/-- A vector in the actual covering section supplies all suitability clauses.
The actor A may be the support normalizer, so W need not be Mc-invariant. -/
theorem source_exists_of_section_vector
    (K W S A : Subgroup G)
    (d : Geometry T Mc (conjugateSpanBy (localModule T M) Mc) K W S)
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) A V)
    (c : BinaryConjugationSection A W (centralInvolutions T) τ)
    (hSA : S ≤ A) (v : V)
    (hfixed : ∀ (s : G) (hs : s ∈ S), τ ⟨s,hSA hs⟩ v = v)
    (hmoved : v ∉ fixed (τ.comp (K.subgroupOf A).subtype)) :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    ∃ u ∈ W, u ^ 2 = 1 ∧ u ≠ 1 ∧ suitableQuotientCentralizer h u = S ∧
      Suitable h Mc u := by
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  obtain ⟨u,hu,huf,hum⟩ := c.exists_fixed_moving_lift K S hSA v hfixed hmoved
  obtain ⟨heq,hm,hp,hl⟩ := source_suitable_of_separated_support
    hG T hempty hM hunique hmany hcard e hab Mc
      (terminal_outside hG T hempty hM hunique hmany hcard e)
      K W S d.fitting d.support_le d.point_le d.normalized
      d.sylow_le d.index d.local_normalizer d.separated u hu huf hum
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  have hu2 : u ^ 2 = 1 :=
    elemPow_eq_one_of_isElementaryAbelian (p := 2) u (d.support_le hu)
  have hune : u ≠ 1 := by
    rintro rfl
    obtain ⟨k,_,hk⟩ := hum
    exact hk (by simp)
  refine ⟨u,hu,hu2,hune,heq,d.support_le hu,hl,?_,hm,hp,?_⟩
  · change (suitableQuotientCentralizer h u).relIndex (T : Subgroup G) = 2
    rw [show suitableQuotientCentralizer h u = S from heq]
    exact d.index
  · change Mc ⊓ normalizer (suitableQuotientCentralizer h u : Set G) = _
    rw [show suitableQuotientCentralizer h u = S from heq]
    exact d.local_normalizer

end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
