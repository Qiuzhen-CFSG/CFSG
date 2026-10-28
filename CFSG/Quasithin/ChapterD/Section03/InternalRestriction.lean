module

public import CFSG.Quasithin.ChapterD.Section03.InternalSetup
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# Restricting the internal actor alternatives

Both alternatives of D.3.2 survive passage to an intermediate overgroup
containing the actor and the Sylow subgroup. C-components restrict, and
the intrinsic quasisimple two-core quotient is preserved by the canonical
subgroup isomorphism. For the odd-prime alternative, that isomorphism
preserves the two-core and the Frattini preimage. Its induced quotient
map intertwines the literal conjugation actions on representatives, so
irreducibility is preserved. Ambient isomorphism transport supplies the
same statement between actual nested subgroup copies.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Hypothesis D.3.2 and Lemma 3.2.2, printed pp.193 and 579.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterD.Section03
variable {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]

omit [Finite G] in
private theorem coreFrattiniAction_mk' (T X : Subgroup G)
    (hTX : T ≤ normalizer (X : Set G)) (t : T) (x : X) :
    coreFrattiniAction T X hTX t (QuotientGroup.mk' (coreFrattiniIn X) x) =
      QuotientGroup.mk' (coreFrattiniIn X)
        (X.normalizerMonoidHom ⟨t, hTX t.property⟩ x) := by
  change quotientAut (coreFrattiniIn X) (X.normalizerMonoidHom (inclusion hTX t))
    (QuotientGroup.mk' (coreFrattiniIn X) x) = _
  rw [quotientAut_apply_mk]
  rfl

private theorem coreFrattiniIrreducible_transfer
    (T X : Subgroup G) (S Y : Subgroup H)
    (hTX : T ≤ normalizer (X : Set G)) (hSY : S ≤ normalizer (Y : Set H))
    (e : Y ≃* X) (a : S →* T) (ha : Function.Surjective a)
    (he : ∀ s : S, ∀ y : Y,
      e (Y.normalizerMonoidHom ⟨s, hSY s.property⟩ y) =
      X.normalizerMonoidHom ⟨a s, hTX (a s).property⟩ (e y))
    (hI : CoreFrattiniIrreducible T X hTX) : CoreFrattiniIrreducible S Y hSY := by
  have hphi : (coreFrattiniIn X).comap e.toMonoidHom = coreFrattiniIn Y :=
    e.toMonoidHom.comap_frattini_pCore_of_pKernel e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
  let q := QuotientGroup.equivOfSurjectiveComap e.toMonoidHom e.surjective
    (coreFrattiniIn Y) (coreFrattiniIn X) hphi
  have hq (s : S) (v : Y ⧸ coreFrattiniIn Y) :
      q (coreFrattiniAction S Y hSY s v) =
        coreFrattiniAction T X hTX (a s) (q v) := by
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (coreFrattiniIn Y) v
    rw [coreFrattiniAction_mk']
    change QuotientGroup.mk' (coreFrattiniIn X)
      (e (Y.normalizerMonoidHom ⟨s, hSY s.property⟩ y)) =
      coreFrattiniAction T X hTX (a s) (QuotientGroup.mk' (coreFrattiniIn X) (e y))
    rw [coreFrattiniAction_mk', he]
  intro A hA
  have hi : ∀ t : T, ∀ v ∈ A.map q.toMonoidHom,
      coreFrattiniAction T X hTX t v ∈ A.map q.toMonoidHom := by
    intro t v hv
    obtain ⟨s, rfl⟩ := ha t
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨coreFrattiniAction S Y hSY s y, hA s y hy, hq s y⟩
  rcases hI (A.map q.toMonoidHom) hi with hb | ht
  · left
    apply map_injective (f := q.toMonoidHom) q.injective
    simpa only [Subgroup.map_bot] using hb
  · right
    apply map_injective (f := q.toMonoidHom) q.injective
    rw [map_top_of_surjective q.toMonoidHom q.surjective]
    exact ht

/-- Restrict the literal core–Frattini action to an intermediate overgroup. -/
theorem CoreFrattiniIrreducible.subgroupOf {T X : Subgroup G}
    {hTX : T ≤ normalizer (X : Set G)} (hI : CoreFrattiniIrreducible T X hTX)
    (A : Subgroup G) (hTA : T ≤ A) (hXA : X ≤ A)
    (hbar : T.subgroupOf A ≤ normalizer (X.subgroupOf A : Set A)) :
    CoreFrattiniIrreducible (T.subgroupOf A) (X.subgroupOf A) hbar := by
  apply coreFrattiniIrreducible_transfer T X (T.subgroupOf A) (X.subgroupOf A)
    hTX hbar (subgroupOfEquivOfLe hXA) (subgroupOfEquivOfLe hTA).toMonoidHom
    (subgroupOfEquivOfLe hTA).surjective ?_ hI
  intro t x
  rfl

/-- Transport preserves the literal core–Frattini conjugation action. -/
theorem CoreFrattiniIrreducible.map_equiv {T X : Subgroup G}
    {hTX : T ≤ normalizer (X : Set G)} (hI : CoreFrattiniIrreducible T X hTX)
    (e : G ≃* H)
    (hbar : T.map e.toMonoidHom ≤ normalizer (X.map e.toMonoidHom : Set H)) :
    CoreFrattiniIrreducible (T.map e.toMonoidHom) (X.map e.toMonoidHom) hbar := by
  apply coreFrattiniIrreducible_transfer T X _ _ hTX hbar
    (e.subgroupMap X).symm (e.subgroupMap T).symm.toMonoidHom
    (e.subgroupMap T).symm.surjective ?_ hI
  intro t x
  apply Subtype.ext
  change e.symm ((t : H) * (x : H) * (t : H)⁻¹) =
    e.symm t * e.symm x * (e.symm t)⁻¹
  simp only [map_mul, map_inv]

/-- Both internal actor alternatives restrict to every overgroup of X T. -/
theorem InternalActorCases.subgroupOf {T : Sylow 2 G} {X : Subgroup G}
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)}
    (hc : InternalActorCases T X hTX) (A : Subgroup G)
    (hTA : (T : Subgroup G) ≤ A) (hXA : X ≤ A)
    (hbar : ((T.subtype hTA : Sylow 2 A) : Subgroup A) ≤
      normalizer (X.subgroupOf A : Set A)) :
    InternalActorCases (T.subtype hTA) (X.subgroupOf A) hbar := by
  rcases hc with ⟨L, hL, hq, hX⟩ | ⟨p, hp, ho, hP, hi⟩
  · have hLA : L ≤ A := (le_componentOrbit L T).trans (hX ▸ hXA)
    let e := subgroupOfEquivOfLe hLA
    let q := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
    let := hq
    refine Or.inl ⟨L.subgroupOf A, hL.subgroupOf hLA,
      IsQuasisimple.of_mulEquiv q.symm, ?_⟩
    apply map_injective A.subtype_injective
    rw [map_subgroupOf_eq_of_le hXA, map_componentOrbit, map_subgroupOf_eq_of_le hLA]
    change X = componentOrbit L (((T : Subgroup G).subgroupOf A).map A.subtype)
    rw [map_subgroupOf_eq_of_le hTA]
    exact hX
  · let e := subgroupOfEquivOfLe hXA
    let q := e.toMonoidHom.pCoreQuotientEquiv (p := 2) e.surjective
      (by rw [e.toMonoidHom.ker_eq_bot e.injective]; exact IsPGroup.of_bot)
    exact Or.inr ⟨p, hp, ho, hP.of_equiv q.symm,
      hi.subgroupOf A hTA hXA hbar⟩

/-- Both alternatives are preserved under a literal ambient isomorphism. -/
theorem InternalActorCases.map_equiv {T : Sylow 2 G} {X : Subgroup G}
    {hTX : (T : Subgroup G) ≤ normalizer (X : Set G)}
    (hc : InternalActorCases T X hTX) (e : G ≃* H)
    (hbar : ((T.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 H) : Subgroup H) ≤
      normalizer (X.map e.toMonoidHom : Set H)) :
    InternalActorCases (T.mapSurjective (f := e.toMonoidHom) e.surjective) (X.map e.toMonoidHom) hbar := by
  rcases hc with ⟨L, hL, hq, hX⟩ | ⟨p, hp, ho, hP, hi⟩
  · let a := e.subgroupMap L
    let q := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
      (by rw [a.toMonoidHom.ker_eq_bot a.injective]; exact IsPGroup.of_bot)
    let := hq
    refine Or.inl ⟨L.map e.toMonoidHom, hL.map_equiv e,
      IsQuasisimple.of_mulEquiv q, ?_⟩
    rw [hX, map_componentOrbit]
    rfl
  · let a := e.subgroupMap X
    let q := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
      (by rw [a.toMonoidHom.ker_eq_bot a.injective]; exact IsPGroup.of_bot)
    exact Or.inr ⟨p, hp, ho, hP.of_equiv q, hi.map_equiv e hbar⟩
end CFSG.Quasithin.ChapterD.Section03

