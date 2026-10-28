module

public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.Model
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.Screen
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.Escape
public import CFSG.Quasithin.ChapterE.Section01.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit.MonomialWitness

/-!
# Resolving the apparent five-prime source obstruction

The erroneous diagnostic inference identified two order-192 Sylow overgroups
without establishing that they were conjugate. The weak-closure normalizer is
not a maximal subgroup in the permutation model: it lies in the order-960
involution centralizer. A different order-192 subgroup, the actual split
monomial subgroup with inverse transpose, supplies escaping E1-members for
conjugates of the original actor. Reproducible GAP evidence is recorded in
`FiveSourceAudit/source/README.md`; it is not a Lean certificate.

The checked screen proves the intrinsic kernel tests and the precise E0
consequence. More decisively, every original actor is killed by the two-core
of the weak-closure normalizer. Hence an E1-member of the same order as that
normalizer escapes it; equality of the orders cannot identify them.

The concrete matrix, solvability and Sylow inputs are now discharged by
`MonomialWitness`. Solvable generation inside that actual overgroup supplies
an E1-member which escapes the ambient weak-closure normalizer. Conjugacy
transports the construction to every ambient Sylow, retaining the original
full actor family and the exact E0 intersection and E1 quotient conditions.
`diagnostic_resolved` also certifies the actor's order eight, rank three and
inner intersection of order four, and the intrinsic quotient kernel of order
four. There are no remaining model premises in this concrete result.

This resolves the specified five-prime diagnostic; the general positioned-eight
branch and the full E.1.14(7) theorem remain separate source obligations.

Source: Aschbacher--Smith E.1.1--5, E.1.8, E.1.13 and E.1.14(7), pp.209--214;
A.2.3(2), p.33. The book cites Aschbacher (1982), Lemma 4.11; the original
lemma was not accessible during this audit. The error resolved here is in
the finite-screen inference, not an asserted correction to that lemma.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit

/-- Conditional consumer of the literal monomial geometry, retained for reuse. The resulting actor
is an actual ambient conjugate; its quotient rank and E0 are supplied by the
checked solvable E-generation theorem, not substituted by its inner part. -/
theorem conjugate_escape_of_monomial_motion (T : Sylow 2 Model)
    (hsolv : Group.IsSolvable monomialOvergroup)
    (hTH : (T : Subgroup Model) ≤ monomialOvergroup)
    (hmove : ¬ monomialOvergroup ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model)) :
    ∃ g : Model, actor.map (MulAut.conj g).toMonoidHom ≤ (T : Subgroup Model) ∧
      ∃ K : Subgroup Model,
        IsEMemberAt 1 (T : Subgroup Model) (actor.map (MulAut.conj g).toMonoidHom) K ∧
        ¬ K ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  let := hsolv
  obtain ⟨B, ⟨g, rfl⟩, hBT, K, hK, hKM⟩ :=
    exists_escape_of_solvable_overgroup T family family_elementary monomialOvergroup hTH hmove
  exact ⟨g, hBT, K, hK, hKM⟩


local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- Extract inside the solvable overgroup before applying E.1.8. This retains
containment in that overgroup, so the component branch is impossible. -/
private theorem solvable_overgroup_escape {G : Type*} [Group G] [Finite G]
    (T : Sylow 2 G) (Ω : Set (Subgroup G)) (hΩ : IsElementaryFamily Ω)
    (H : Subgroup G) [Group.IsSolvable H] (hTH : (T : Subgroup G) ≤ H)
    (hmove : ¬ H ≤ normalizer (weakClosure (T : Subgroup G) Ω : Set G)) :
    ∃ A ∈ Ω, A ≤ (T : Subgroup G) ∧ ∃ K : Subgroup G,
      K ≤ H ∧ IsEMemberAt 1 (T : Subgroup G) A K ∧ ECaseOdd A K ∧
      ¬ K ≤ normalizer (weakClosure (T : Subgroup G) Ω : Set G) := by
  let M := normalizer (weakClosure (T : Subgroup G) Ω : Set G)
  have hM : M.subgroupOf H ≠ ⊤ := by
    intro he
    apply hmove
    intro x hx
    exact (show (⟨x, hx⟩ : H) ∈ M.subgroupOf H from he.symm ▸ mem_top _)
  have hn : normalizer
      (weakClosure ((T : Subgroup G).subgroupOf H) (ChiefOrbit.restrictedFamily H Ω) : Set H) ≤
      M.subgroupOf H := by
    apply map_le_iff_le_comap.mp
    have hm := le_normalizer_map H.subtype
      (H := weakClosure ((T : Subgroup G).subgroupOf H) (ChiefOrbit.restrictedFamily H Ω))
    rwa [ChiefOrbit.map_weakClosure_restrictedFamily (T : Subgroup G) H hTH Ω] at hm
  obtain ⟨B, hB, hBT, K, hK, hKM⟩ :=
    (isEGenerated_one_of_solvable (T.subtype hTH)).exists_member_not_le
      (ChiefOrbit.restrictedFamily H Ω) (ChiefOrbit.restrictedFamily_elementary H hΩ)
      (M.subgroupOf H) hM hn
  let A := B.map H.subtype
  have hA : A ∈ Ω := hB
  have hAT : A ≤ (T : Subgroup G) := map_le_iff_le_comap.mpr hBT
  have he : A.subgroupOf H = B := comap_map_eq_self (by rw [H.ker_subtype]; exact bot_le)
  let _ := hΩ.1 A hA
  have hk : IsEMemberAt 1 (T : Subgroup G) A (K.map H.subtype) :=
    IsEMemberAt.inherit T A H hAT ((tau_le _ _).trans hTH) (he.symm ▸ hK)
  have hs : Group.IsSolvable (K.map H.subtype) :=
    Group.isSolvable_of_surjective (H.subtype.subgroupMap_surjective K)
  have ho : ECaseOdd A (K.map H.subtype) :=
    hk.1.2.2.2.2.2.resolve_right (fun hc => componentCase_not_isSolvable hc hs)
  exact ⟨A, hA, hAT, K.map H.subtype, map_subtype_le _, hk, ho,
    fun h => hKM (map_le_iff_le_comap.mp h)⟩

/-- The certified monomial geometry supplies a genuine E1-member inside the
literal monomial overgroup for an actual conjugate of the original actor. -/
theorem exists_monomial_E1_escape :
    ∃ T : Sylow 2 Model, actor ≤ (T : Subgroup Model) ∧
      ∃ A ∈ family, A ≤ (T : Subgroup Model) ∧ ∃ K : Subgroup Model,
        K ≤ monomialOvergroup ∧ IsEMemberAt 1 (T : Subgroup Model) A K ∧
        ECaseOdd A K ∧
        ¬ K ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  let _ := monomialOvergroup_solvable
  obtain ⟨T, hAT, hTK, hmove⟩ := exists_monomial_sylow_motion
  exact ⟨T, hAT, solvable_overgroup_escape T family family_elementary
    monomialOvergroup hTK hmove⟩

/-- The full original conjugacy family has an escaping E1-member at every
ambient Sylow. Conjugation transports the exact E0 and quotient-rank clauses. -/
theorem family_E1_escape (T : Sylow 2 Model) :
    ∃ A ∈ family, A ≤ (T : Subgroup Model) ∧ ∃ K : Subgroup Model,
      IsEMemberAt 1 (T : Subgroup Model) A K ∧ ECaseOdd A K ∧
      ¬ K ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  obtain ⟨S, _, A, hA, _, K, _, hK, ho, hKM⟩ := exists_monomial_E1_escape
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Model S T
  let e := MulAut.conj g
  have hST : (S : Subgroup Model).map e.toMonoidHom = (T : Subgroup Model) :=
    congrArg (fun P : Sylow 2 Model => (P : Subgroup Model)) hg
  have hf : {B : Subgroup Model | B.map e.toMonoidHom ∈ family} = family := by
    ext B
    constructor
    · intro hB
      have hb := family_elementary.2 g⁻¹ _ hB
      have he : (MulAut.conj g⁻¹).toMonoidHom.comp e.toMonoidHom = MonoidHom.id Model := by
        ext x
        simp [e, MulAut.conj_apply, mul_assoc]
      simpa only [map_map, he, map_id] using hb
    · exact family_elementary.2 g B
  have hw : (weakClosure (S : Subgroup Model) family).map e.toMonoidHom =
      weakClosure (T : Subgroup Model) family := by
    simpa only [hf, hST] using map_weakClosure_equiv e (S : Subgroup Model) family
  have hk := hK.map_equiv e
  rw [hST] at hk
  have hs : Group.IsSolvable (K.map e.toMonoidHom) := by
    let _ := oddCase_isSolvable ho
    exact Group.isSolvable_of_surjective (e.toMonoidHom.subgroupMap_surjective K)
  refine ⟨A.map e.toMonoidHom, family_elementary.2 g A hA, hk.1.2.1,
    K.map e.toMonoidHom, hk,
    hk.1.2.2.2.2.2.resolve_right (fun hc => componentCase_not_isSolvable hc hs), ?_⟩
  intro hle
  apply hKM
  have hn := (weakClosure (S : Subgroup Model) family).map_normalizer_eq_of_bijective
    (f := e.toMonoidHom) e.bijective
  rw [hw] at hn
  rw [← hn] at hle
  exact (map_le_map_iff_of_injective e.injective).mp hle

/-- Every original-family actor has order eight, inner intersection of order
four, and is genuinely outside the marked inner subgroup. -/
theorem family_actor_orders {A : Subgroup Model} (hA : A ∈ family) :
    Nat.card A = 8 ∧ Nat.card (A ⊓ inner : Subgroup Model) = 4 ∧ ¬ A ≤ inner := by
  obtain ⟨g, rfl⟩ := hA
  let _ : inner.Normal := inferInstanceAs
    (Matrix.PSL3.OddPrimeGraphExtension.GraphLargeStructure.innerPart (ZMod 5)).Normal
  have hc : Nat.card (actor.map (MulAut.conj g).toMonoidHom) = 8 := by
    rw [card_map_of_injective (MulAut.conj g).injective, card_actor]
  have hn : inner.map (MulAut.conj g).toMonoidHom = inner := Normal.map_conj_eq inner g
  have hi : Nat.card (actor.map (MulAut.conj g).toMonoidHom ⊓ inner : Subgroup Model) = 4 := by
    rw [← hn,
      ← map_inf actor inner (MulAut.conj g).toMonoidHom (MulAut.conj g).injective,
      card_map_of_injective (MulAut.conj g).injective, card_actor_inf_inner]
  refine ⟨hc, hi, ?_⟩
  intro hle
  rw [inf_eq_left.mpr hle, hc] at hi
  omega

/-- The actors themselves, rather than their inner intersections, have rank three. -/
theorem family_actor_rank {A : Subgroup Model} (hA : A ∈ family) : Group.rank A = 3 := by
  let _ := family_elementary.1 A hA
  let _ : CommGroup A := IsMulCommutative.instCommGroup
  have hc := (family_actor_orders hA).1
  apply le_antisymm
  · exact IsElementaryAbelian.rank_le_of_card_le (p := 2) A (by omega)
  · have hd := card_dvd_exponent_pow_rank' A
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
        (IsElementaryAbelian.exponent_dvd_p 2 A))
    have hbound : 2 ^ 3 ≤ 2 ^ Group.rank A := by
      simpa only [hc, show (2 : ℕ) ^ 3 = 8 from by decide] using
        Nat.le_of_dvd (by positivity) hd
    exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hbound

/-- Resolution of the concrete five-prime diagnostic, with the source E0/E1
conditions and the literal intrinsic quotient image and kernel retained.
The family is the full ambient conjugacy class of the specified diagonal-and-graph
actor. No subgroup census, model witness or E-generation hypothesis is assumed. -/
theorem diagnostic_resolved (T : Sylow 2 Model) :
    ∃ A ∈ family, A ≤ (T : Subgroup Model) ∧ Nat.card A = 8 ∧
      Nat.card (A ⊓ inner : Subgroup Model) = 4 ∧ Group.rank A = 3 ∧ ¬ A ≤ inner ∧
      ∃ K : Subgroup Model, IsEMemberAt 1 (T : Subgroup Model) A K ∧ ECaseOdd A K ∧
        Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = 1 ∧
        Nat.card (A.subgroupOf K ⊓ pCore 2 K : Subgroup K) = 4 ∧
        ¬ K ≤ normalizer (weakClosure (T : Subgroup Model) family : Set Model) := by
  obtain ⟨A, hA, hAT, K, hK, ho, hKM⟩ := family_E1_escape T
  obtain ⟨h8, h4, hout⟩ := family_actor_orders hA
  let _ := family_elementary.1 A hA
  have hr : Group.rank ((A.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) = 1 := by
    obtain ⟨_, _, _, _, _, _, hr⟩ := ho
    exact hr
  exact ⟨A, hA, hAT, h8, h4, family_actor_rank hA, hout, K, hK, ho, hr,
    oddCase_kernel_card hK.1.2.2.1 h8 ho, hKM⟩


end CFSG.Quasithin.ChapterE.ValuesOdd.PSLThreeGeneration.ProperExtension.GraphLarge.OuterFamilies.EightActors.FiveSourceAudit
