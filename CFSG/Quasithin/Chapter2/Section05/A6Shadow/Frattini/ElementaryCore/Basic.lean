module

public import CFSG.Quasithin.Chapter2.Section05.A6Shadow.Frattini.Transport
public import Theory.Frattini.OmegaProducts

/-!
# Actual lifts for the elementary-core branches

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, proof of
Lemma 2.5.24, printed p.568. The action identifies `S ∩ K` with the inner
part of the actual Sylow image in Aut(A₆): its kernel intersects K trivially.
This gives actual subgroups Y, E₁ and E₂ upstairs, retaining their cyclic
and four-group structures. None of the extension geometry follows merely
from the corresponding quotient subgroup.

The source input from 2.5.22(1) is kept explicit. The local core in the orbit
contract is the genuine O₂(N_H(E)). These definitions contain no assumption
about Frattini nontriviality or maximal elementary subgroups.
-/

@[expose] public section

open Subgroup AlternatingSix.ShadowLocal
namespace CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}}

/-- The permitted independent source input 2.5.22(1), with the actual action. -/
def ZConjugateActions (d : EarlierSetup κ G) : Prop :=
  ∀ (g : G) (ha : g⁻¹ * d.z * g ∈ d.S),
    d.K = ⁅d.K, zpowers (g⁻¹ * d.z * g)⁆ ∧
      d.action ⟨g⁻¹ * d.z * g, d.s_le_h ha⟩ ∈ natural

/-- The ambient image of the Frattini subgroup of an actual subgroup. -/
def phi (A : Subgroup G) : Subgroup G := (frattini A).map A.subtype

/-- The source subgroup Φ_C. -/
def phiC (d : EarlierSetup κ G) : Subgroup G := phi d.S ⊓ d.SC

/-- The source subgroup S₊ = Ω₁(C_S(Φ(S))). -/
def plus (d : EarlierSetup κ G) : Subgroup G :=
  omegaOneAmbient (d.S ⊓ centralizer (phi d.S : Set G))

/-- The full preimage of the marked transposition line in the actual S-action.
This is S₀ in the omega calculation; no splitting of this preimage is asserted. -/
noncomputable def transpositionPreimage (d : EarlierSetup κ G) : Subgroup G :=
  ((SylowGeometry.transpositionSubgroup d.imageSylow).comap d.toImageSylow).map d.S.subtype

/-- Elementary abelian subgroups of largest order, the source family A(S).
For elementary abelian two-groups, largest order is equivalent to largest rank. -/
def largestElementary (S : Subgroup G) : Set (Subgroup G) :=
  {E | E ≤ S ∧ IsElementaryAbelian 2 E ∧
    ∀ F : Subgroup G, F ≤ S → IsElementaryAbelian 2 F → Nat.card F ≤ Nat.card E}

/-- The actual O₂(N_H(E)), with normality relative to the indicated local group. -/
def localCore (d : EarlierSetup κ G) (E : Subgroup G) : Subgroup G :=
  twoCore (d.H ⊓ normalizer (E : Set G))

/-- Precisely the elementary-core orbit consumed by the parent Frattini argument. -/
def HasNormalizerOrbit (d : EarlierSetup κ G) : Prop :=
  ∃ E : Subgroup G, E ≤ d.S ⊓ d.K ∧ IsKleinFour E ∧
    ∃ s ∈ d.S, rightConjugate d.x (localCore d E) = rightConjugate s (localCore d E)

variable (d : EarlierSetup κ G)

theorem toImageSylow_surjective : Function.Surjective d.toImageSylow := by
  intro a
  have ha : (a : AutA6) ∈ d.sylowAction.range := d.imageSylow_eq_range ▸ a.property
  obtain ⟨s, hs⟩ := ha
  exact ⟨s, Subtype.ext hs⟩

/-- Restrict the actual compatible action to the inner Sylow factor. -/
def innerAction : (d.S ⊓ d.K : Subgroup G) →* sylowInner d.imageSylow :=
  (d.toImageSylow.comp (inclusion inf_le_left)).codRestrict _ (by
    intro k
    change d.skAction k ∈ AlternatingSix.ShadowLocal.inner
    rw [show d.skAction k = MulAut.conj (d.modelK ⟨k, k.property.2⟩) from
      d.action_on_K ⟨k, k.property.2⟩]
    exact ⟨_, rfl⟩)

theorem innerAction_injective : Function.Injective (innerAction d) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  apply bot_unique
  intro k hk
  have hkact : d.skAction k = 1 := congrArg (fun a : sylowInner d.imageSylow =>
    ((a : d.imageSylow) : AutA6)) hk
  have hker : (⟨k, k.property.1⟩ : d.S) ∈ d.sylowAction.ker := hkact
  rw [d.sylowAction_kernel] at hker
  exact Subtype.ext (disjoint_def.mp d.disjoint_k_sc k.property.2 hker)

theorem innerAction_surjective : Function.Surjective (innerAction d) := by
  intro a
  have ha : ((a : d.imageSylow) : AutA6) ∈ d.skAction.range := by
    rw [d.skAction_range]
    exact ⟨a.val.property, a.property⟩
  obtain ⟨k, hk⟩ := ha
  exact ⟨k, Subtype.ext (Subtype.ext hk)⟩

/-- An isomorphism, not just a quotient identification: K meets the kernel trivially. -/
noncomputable def innerEquiv : (d.S ⊓ d.K : Subgroup G) ≃* sylowInner d.imageSylow :=
  MulEquiv.ofBijective (innerAction d) ⟨innerAction_injective d, innerAction_surjective d⟩

/-- Inverse of the inner action, followed by the actual inclusion in G. -/
noncomputable def innerLift : sylowInner d.imageSylow →* G :=
  (d.S ⊓ d.K).subtype.comp (innerEquiv d).symm.toMonoidHom

theorem innerLift_injective : Function.Injective (innerLift d) :=
  (d.S ⊓ d.K).subtype_injective.comp (innerEquiv d).symm.injective

/-- Lift a subgroup of the actual Sylow image inside S ∩ K. -/
noncomputable def liftInner (E : Subgroup d.imageSylow) : Subgroup G :=
  (E.subgroupOf (sylowInner d.imageSylow)).map (innerLift d)

theorem liftInner_le (E : Subgroup d.imageSylow) : liftInner d E ≤ d.S ⊓ d.K := by
  rintro _ ⟨a, _, rfl⟩
  exact ((innerEquiv d).symm a).property

noncomputable def liftInnerEquiv (E : Subgroup d.imageSylow)
    (hE : E ≤ sylowInner d.imageSylow) : liftInner d E ≃* E :=
  ((E.subgroupOf (sylowInner d.imageSylow)).equivMapOfInjective
    (innerLift d) (innerLift_injective d)).symm.trans (subgroupOfEquivOfLe hE)

/-- Membership in the lift is tested by the faithful inner action. -/
theorem mem_liftInner (E : Subgroup d.imageSylow) (k : (d.S ⊓ d.K : Subgroup G)) :
    (k : G) ∈ liftInner d E ↔ (innerEquiv d k : d.imageSylow) ∈ E := by
  constructor
  · rintro ⟨a, ha, hk⟩
    have he : a = innerEquiv d k := by
      apply (innerEquiv d).symm.injective
      exact (Subtype.ext hk).trans ((innerEquiv d).symm_apply_apply k).symm
    exact he ▸ ha
  · intro hk
    refine ⟨innerEquiv d k, hk, ?_⟩
    exact congrArg Subtype.val ((innerEquiv d).symm_apply_apply k)

/-- The actual image of an inner subgroup, viewed in the Sylow image. -/
noncomputable def imageInner (U : Subgroup G) : Subgroup d.imageSylow :=
  ((U.subgroupOf (d.S ⊓ d.K)).map (innerEquiv d).toMonoidHom).map
    (sylowInner d.imageSylow).subtype

theorem imageInner_le (U : Subgroup G) : imageInner d U ≤ sylowInner d.imageSylow :=
  (map_le_range _ _).trans_eq (sylowInner d.imageSylow).range_subtype

noncomputable def imageInnerEquiv (U : Subgroup G) (hU : U ≤ d.S ⊓ d.K) :
    U ≃* imageInner d U :=
  (subgroupOfEquivOfLe hU).symm.trans
    (((innerEquiv d).subgroupMap (U.subgroupOf (d.S ⊓ d.K))).trans
      (((U.subgroupOf (d.S ⊓ d.K)).map (innerEquiv d).toMonoidHom).equivMapOfInjective
        (sylowInner d.imageSylow).subtype (sylowInner d.imageSylow).subtype_injective))

theorem liftInner_imageInner (U : Subgroup G) (hU : U ≤ d.S ⊓ d.K) :
    liftInner d (imageInner d U) = U := by
  ext a
  constructor
  · intro ha
    have haD := liftInner_le d _ ha
    have hm := (mem_liftInner d _ ⟨a, haD⟩).mp ha
    obtain ⟨b, hb, he⟩ := hm
    have he' : b = innerEquiv d ⟨a, haD⟩ := Subtype.ext he
    rw [he'] at hb
    have h := (mem_map_equiv.mp hb)
    simpa only [MulEquiv.symm_apply_apply, mem_subgroupOf] using h
  · intro ha
    apply (mem_liftInner d _ ⟨a, hU ha⟩).mpr
    exact ⟨innerEquiv d ⟨a, hU ha⟩, ⟨⟨a, hU ha⟩, ha, rfl⟩, rfl⟩

theorem imageInner_liftInner (E : Subgroup d.imageSylow)
    (hE : E ≤ sylowInner d.imageSylow) : imageInner d (liftInner d E) = E := by
  ext a
  constructor
  · rintro ⟨b, ⟨k, hk, rfl⟩, rfl⟩
    exact (mem_liftInner d E k).mp hk
  · intro ha
    let k := (innerEquiv d).symm ⟨a, hE ha⟩
    have hk : (k : G) ∈ liftInner d E := by
      apply (mem_liftInner d E k).mpr
      simpa only [k, MulEquiv.apply_symm_apply] using ha
    exact ⟨innerEquiv d k, ⟨k, hk, rfl⟩,
      congrArg Subtype.val ((innerEquiv d).apply_symm_apply ⟨a, hE ha⟩)⟩

/-- The cyclic order-four subgroup of the inner dihedral factor, lifted into G. -/
noncomputable def cyclic (d : EarlierSetup κ G) : Subgroup G :=
  liftInner d (SylowGeometry.cyclicFour d.imageSylow)

/-- The first actual four-subgroup of S ∩ K. -/
noncomputable def fourZero (d : EarlierSetup κ G) : Subgroup G :=
  liftInner d (SylowGeometry.kleinZero d.imageSylow)

/-- The second actual four-subgroup of S ∩ K. -/
noncomputable def fourOne (d : EarlierSetup κ G) : Subgroup G :=
  liftInner d (SylowGeometry.kleinOne d.imageSylow)

theorem cyclic_le : cyclic d ≤ d.S ⊓ d.K := liftInner_le d _
theorem fourZero_le : fourZero d ≤ d.S ⊓ d.K := liftInner_le d _
theorem fourOne_le : fourOne d ≤ d.S ⊓ d.K := liftInner_le d _

noncomputable def cyclicEquiv : cyclic d ≃* Multiplicative (ZMod 4) :=
  (liftInnerEquiv d _ (SylowGeometry.cyclicFour_le_inner d.imageSylow)).trans
    (SylowGeometry.cyclicFourEquiv d.imageSylow)

instance cyclic_isCyclic : IsCyclic (cyclic d) :=
  (cyclicEquiv d).isCyclic.mpr inferInstance

theorem cyclic_card : Nat.card (cyclic d) = 4 := by
  rw [Nat.card_congr (cyclicEquiv d).toEquiv]
  simp

private theorem kleinFour_of_equiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) [IsKleinFour B] : IsKleinFour A where
  card_four := (Nat.card_congr e.toEquiv).trans IsKleinFour.card_four
  exponent_two := (Monoid.exponent_eq_of_mulEquiv e).trans IsKleinFour.exponent_two

instance fourZero_isKleinFour : IsKleinFour (fourZero d) :=
  kleinFour_of_equiv (liftInnerEquiv d _ (SylowGeometry.kleinZero_le_inner d.imageSylow))

instance fourOne_isKleinFour : IsKleinFour (fourOne d) :=
  kleinFour_of_equiv (liftInnerEquiv d _ (SylowGeometry.kleinOne_le_inner d.imageSylow))

theorem fourZero_ne_fourOne : fourZero d ≠ fourOne d := by
  intro h
  have he := congrArg (imageInner d) h
  change imageInner d (liftInner d _) = imageInner d (liftInner d _) at he
  rw [imageInner_liftInner d _ (SylowGeometry.kleinZero_le_inner d.imageSylow),
    imageInner_liftInner d _ (SylowGeometry.kleinOne_le_inner d.imageSylow)] at he
  exact SylowGeometry.kleinZero_ne_kleinOne d.imageSylow he

/-- Exhaustiveness upstairs follows from the faithful action on S ∩ K. -/
theorem four_subgroups (E : Subgroup G) (hE : E ≤ d.S ⊓ d.K) [IsKleinFour E] :
    E = fourZero d ∨ E = fourOne d := by
  let : IsKleinFour (imageInner d E) := kleinFour_of_equiv (imageInnerEquiv d E hE).symm
  rcases SylowGeometry.kleinFour_subgroups_inner d.imageSylow (imageInner d E)
      (imageInner_le d E) with h | h
  · exact Or.inl ((liftInner_imageInner d E hE).symm.trans (congrArg (liftInner d) h))
  · exact Or.inr ((liftInner_imageInner d E hE).symm.trans (congrArg (liftInner d) h))

end CFSG.Quasithin.Chapter2.A6Shadow.Frattini.ElementaryCore
