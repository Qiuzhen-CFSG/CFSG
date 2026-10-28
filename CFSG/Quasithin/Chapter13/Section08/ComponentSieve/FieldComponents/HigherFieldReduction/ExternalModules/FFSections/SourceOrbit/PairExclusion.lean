module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.WeakClosureBounds.GenerationOne.RepresentationReduction.SourceRestrictions.Cases.Sections
public import Mathlib.LinearAlgebra.Projection

/-!
# Isomorphism of the two hatted constituents

A commuting S₃ action with fixed-point-free cubic element cannot preserve a
sum of two nonisomorphic irreducible K-modules. Schur's lemma makes the
off-diagonal projections zero, so both summands would be S₃-invariant. The
inverter-fixed decomposition would then split either irreducible summand.

The exported theorem applies this argument to the literal image of the
H-orbit in V/C_V(K), using normality in H to construct its ambient action.
The maps I/C_I(K) → V/C_V(K) prove irreducibility of the actual hatted
images. No identification with a chosen inverter-fixed constituent is used.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), proof of
13.8.20, printed p.954, and F.9.18(4iii), printed p.325.
-/

@[expose] public noncomputable section

open Representation Representation.BinaryOffender InvertedCubicTensor

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
variable {K V : Type*} [Group K] [AddCommGroup V] [Module (ZMod 2) V]
  (κ : Representation (ZMod 2) K V)

private theorem projection_equivariant (I J : Subrepresentation κ)
    (hc : IsCompl I.toSubmodule J.toSubmodule) (k : K) (v : V) :
    I.toSubmodule.projectionOnto J.toSubmodule hc (κ k v) =
      I.toRepresentation k (I.toSubmodule.projectionOnto J.toSubmodule hc v) := by
  obtain ⟨⟨i,j⟩, rfl⟩ := (I.toSubmodule.prodEquivOfIsCompl J.toSubmodule hc).surjective v
  change I.toSubmodule.projectionOnto J.toSubmodule hc (κ k ((i : V) + j)) =
    I.toRepresentation k (I.toSubmodule.projectionOnto J.toSubmodule hc ((i : V) + j))
  rw [map_add, map_add, map_add, Submodule.projectionOnto_apply_left,
    Submodule.projectionOnto_apply_right, add_zero]
  have hi : κ k (i : V) ∈ I.toSubmodule := I.apply_mem_toSubmodule k i.property
  have hj : κ k (j : V) ∈ J.toSubmodule := J.apply_mem_toSubmodule k j.property
  rw [Submodule.projectionOnto_apply_of_mem_left hc hi,
    Submodule.projectionOnto_apply_of_mem_right hc hj, add_zero]
  rfl

private theorem commuting_preserves_left (I J : Subrepresentation κ)
    [IsIrreducible I.toRepresentation] [IsIrreducible J.toRepresentation]
    (hc : IsCompl I.toSubmodule J.toSubmodule)
    (hne : ¬ Nonempty (I.toRepresentation.Equiv J.toRepresentation))
    (a : V →ₗ[ZMod 2] V) (ha : ∀ k v, a (κ k v) = κ k (a v)) :
    ∀ v ∈ I.toSubmodule, a v ∈ I.toSubmodule := by
  let b : IntertwiningMap I.toRepresentation J.toRepresentation :=
    ((J.toSubmodule.projectionOnto I.toSubmodule hc.symm).comp
      (a.comp I.toSubmodule.subtype)).intertwiningMap_of_isIntertwiningMap _ _ (by
        intro k v
        change J.toSubmodule.projectionOnto I.toSubmodule hc.symm (a (κ k v)) = _
        rw [ha, projection_equivariant]
        rfl)
  have hb : b = 0 := (IsIrreducible.bijective_or_eq_zero b).resolve_left
    (fun h => hne ⟨b.ofBijective h⟩)
  intro v hv
  apply (Submodule.projectionOnto_apply_eq_zero_iff hc.symm).mp
  exact congrArg (fun f : IntertwiningMap I.toRepresentation J.toRepresentation =>
    f ⟨v,hv⟩) hb

private theorem commuting_not_irreducible
    (σ : Representation (ZMod 2) S₃ V)
    (hc : ∀ k g v, κ k (σ g v) = σ g (κ k v))
    (h : ∀ v, σ cubic v = v → v = 0) : ¬ IsIrreducible κ := by
  intro hi
  let := hi
  let := Subrepresentation.irreducible_module_nontrivial κ
  let I : Subrepresentation κ :=
    { toSubmodule := multiplicitySpace σ
      apply_mem_toSubmodule k v hv := by
        rw [mem_multiplicitySpace] at hv ⊢
        rw [← hc, hv] }
  have hz : ∀ a : multiplicitySpace σ, a = 0 := by
    rcases eq_bot_or_eq_top I with hb | ht
    · intro a
      apply Subtype.ext
      have ha : a.val ∈ I.toSubmodule := a.property
      rw [hb] at ha
      exact ha
    · intro a
      have ha : σ cubic a.val ∈ I.toSubmodule := by rw [ht]; trivial
      let b : multiplicitySpace σ := ⟨_, ha⟩
      have he : pairEquiv σ h (b,0) = pairEquiv σ h (0,a) := by
        simp only [pairEquiv_apply, Submodule.coe_zero, map_zero, zero_add, add_zero]
        rfl
      exact (congrArg Prod.snd ((pairEquiv σ h).injective he)).symm
  have hv : ∀ v : V, v = 0 := by
    intro v
    obtain ⟨⟨a,b⟩, rfl⟩ := (pairEquiv σ h).surjective v
    rw [hz a, hz b]
    exact map_zero (pairEquiv σ h)
  obtain ⟨v, hvne⟩ := exists_ne (0 : V)
  exact hvne (hv v)

/-- A pair of irreducible summands in a commuting fixed-free cubic action is isomorphic. -/
private theorem pair_isomorphic (σ : Representation (ZMod 2) S₃ V)
    (hc : ∀ k g v, κ k (σ g v) = σ g (κ k v))
    (h : ∀ v, σ cubic v = v → v = 0)
    (I J : Subrepresentation κ)
    [IsIrreducible I.toRepresentation] [IsIrreducible J.toRepresentation]
    (hIJ : IsCompl I.toSubmodule J.toSubmodule) :
    Nonempty (I.toRepresentation.Equiv J.toRepresentation) := by
  by_contra hne
  have hstable : ∀ g v, v ∈ I.toSubmodule → σ g v ∈ I.toSubmodule := fun g =>
    commuting_preserves_left κ I J hIJ hne (σ g) (fun k v => (hc k g v).symm)
  let S : Subrepresentation σ := ⟨I.toSubmodule, fun g _ hv => hstable g _ hv⟩
  apply commuting_not_irreducible I.toRepresentation S.toRepresentation
    (fun k g v => Subtype.ext (hc k g v)) _ inferInstance
  intro v hv
  apply Subtype.ext
  exact h v (congrArg Subtype.val hv)
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
variable {K V W : Type*} [Group K]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

private theorem irreducible_of_equiv
    {κ : Representation (ZMod 2) K V} {τ : Representation (ZMod 2) K W}
    (E : V ≃ₗ[ZMod 2] W) (hE : ∀ g v, E (κ g v) = τ g (E v))
    [IsIrreducible τ] : IsIrreducible κ := by
  let : Nontrivial W := Subrepresentation.irreducible_module_nontrivial τ
  let : Nontrivial V := Function.Surjective.nontrivial E.surjective
  rw [Representation.IsIrreducible, isSimpleOrder_iff]
  refine ⟨inferInstance, ?_⟩
  intro S
  let T : Subrepresentation τ := ⟨S.toSubmodule.map E.toLinearMap, by
    intro g w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨κ g v, S.apply_mem_toSubmodule g hv, hE g v⟩⟩
  rcases eq_bot_or_eq_top T with hb | ht
  · left
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.map_injective_of_injective E.injective
    change T.toSubmodule = Submodule.map E.toLinearMap ⊥
    rw [hb, Submodule.map_bot]
    rfl
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.map_injective_of_injective E.injective
    change T.toSubmodule = Submodule.map E.toLinearMap ⊤
    rw [ht, Submodule.map_top, LinearMap.range_eq_top.mpr E.surjective]
    rfl

variable {G : Type*} [Group G] (ρ : Representation (ZMod 2) G V)
  (f : K →* G) (s : S₃ →* G) (hs : ∀ k g, Commute (f k) (s g))

include hs in
/-- The conclusion holds in an actual invariant upper space, not just in the whole module. -/
private theorem pair_isomorphic_in (D : Subrepresentation ρ)
    (h : ∀ v, ρ (s cubic) v = v → v = 0)
    (I J : Subrepresentation (ρ.comp f))
    [IsIrreducible I.toRepresentation] [IsIrreducible J.toRepresentation]
    (hI : I.toSubmodule ≤ D.toSubmodule) (hJ : J.toSubmodule ≤ D.toSubmodule)
    (hd : Disjoint I.toSubmodule J.toSubmodule)
    (hIJ : I.toSubmodule ⊔ J.toSubmodule = D.toSubmodule) :
    Nonempty (I.toRepresentation.Equiv J.toRepresentation) := by
  let A : Subrepresentation (D.toRepresentation.comp f) :=
    ⟨I.toSubmodule.comap D.toSubmodule.subtype,
      fun k _ hv => I.apply_mem_toSubmodule k hv⟩
  let B : Subrepresentation (D.toRepresentation.comp f) :=
    ⟨J.toSubmodule.comap D.toSubmodule.subtype,
      fun k _ hv => J.apply_mem_toSubmodule k hv⟩
  let eA : A.toRepresentation.Equiv I.toRepresentation :=
    { toLinearEquiv := Submodule.comapSubtypeEquivOfLe hI
      isIntertwining' := fun _ => by ext; rfl }
  let eB : B.toRepresentation.Equiv J.toRepresentation :=
    { toLinearEquiv := Submodule.comapSubtypeEquivOfLe hJ
      isIntertwining' := fun _ => by ext; rfl }
  let : IsIrreducible A.toRepresentation := irreducible_of_equiv (τ := I.toRepresentation) eA.toLinearEquiv
    (fun _ _ => rfl)
  let : IsIrreducible B.toRepresentation := irreducible_of_equiv (τ := J.toRepresentation) eB.toLinearEquiv
    (fun _ _ => rfl)
  have hab : IsCompl A.toSubmodule B.toSubmodule := by
    apply isCompl_iff.mpr
    constructor
    · apply disjoint_iff.mpr
      apply eq_bot_iff.mpr
      intro v hv
      apply Subtype.ext
      exact (disjoint_iff.mp hd).le ⟨hv.1,hv.2⟩
    · apply codisjoint_iff.mpr
      apply top_unique
      intro v _
      have hv : (v : V) ∈ I.toSubmodule ⊔ J.toSubmodule := hIJ.symm ▸ v.property
      obtain ⟨i, hi, j, hj, he⟩ := Submodule.mem_sup.mp hv
      exact Submodule.mem_sup.mpr ⟨⟨i, hI hi⟩, hi, ⟨j,hJ hj⟩, hj, Subtype.ext he⟩
  obtain ⟨e⟩ := pair_isomorphic (D.toRepresentation.comp f) (D.toRepresentation.comp s)
    (fun k g v => Subtype.ext (ambient_commute ρ f s hs k g v))
    (fun v hv => Subtype.ext (h v (congrArg Subtype.val hv))) A B hab
  exact ⟨eA.symm.trans (e.trans eB)⟩
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
  (s : S₃ →* G) (hs : ∀ (k : L) g, Commute (k : G) (s g))

omit [L.Normal] in
private theorem quotientImage_irreducible (I : Submodule (ZMod 2) V)
    (hI : IsIrrPlus ρ L I) :
    IsIrreducible (quotientImage ρ L I hI.choose).toRepresentation := by
  let := hI.choose_spec.2
  let e := centralQuotientImageEquiv ρ L I
  apply irreducible_of_equiv (τ := centralQuotientRepresentation ρ L I hI.choose) e.symm
  intro k v
  apply e.injective
  rw [e.apply_symm_apply, centralQuotientImageEquiv_equivariant, e.apply_symm_apply]
  rfl

include hs in
/-- In the literal hatted orbit, two disjoint irreducible central images are isomorphic. -/
theorem hatted_pair_isomorphic
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤)
    (I J : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I) (hJ : IsIrrPlus ρ L J)
    (hd : Disjoint (I.map (fixedSpace ρ L).mkQ) (J.map (fixedSpace ρ L).mkQ))
    (hpair : (orbitSpan ρ ⊤ I).map (fixedSpace ρ L).mkQ =
      I.map (fixedSpace ρ L).mkQ ⊔ J.map (fixedSpace ρ L).mkQ) :
    SameModule (quotientImage ρ L I hI.choose) (quotientImage ρ L J hJ.choose) := by
  let C : Subrepresentation ρ :=
    ⟨fixedSpace ρ L, fun g v hv =>
      (fixedSpace_stable_of_normal ρ L (Subgroup.mem_top g) v).mpr hv⟩
  let D : Subrepresentation ρ :=
    ⟨orbitSpan ρ ⊤ I, fun g v hv =>
      (orbitSpan_invariant ρ ⊤ I (Subgroup.mem_top g) v).mpr hv⟩
  let Q := C.quotientImage D
  let A : Subrepresentation (C.quotientRepresentation.comp L.subtype) :=
    ⟨I.map (fixedSpace ρ L).mkQ, fun k v hv => by
      obtain ⟨i,hi,rfl⟩ := hv
      exact ⟨ρ k i, (hI.choose k.property i).mpr hi, rfl⟩⟩
  let B : Subrepresentation (C.quotientRepresentation.comp L.subtype) :=
    ⟨J.map (fixedSpace ρ L).mkQ, fun k v hv => by
      obtain ⟨j,hj,rfl⟩ := hv
      exact ⟨ρ k j, (hJ.choose k.property j).mpr hj, rfl⟩⟩
  have heA : A.toRepresentation = (quotientImage ρ L I hI.choose).toRepresentation := by
    apply MonoidHom.ext
    intro k
    apply LinearMap.ext
    rintro ⟨v,i,hi,rfl⟩
    rfl
  have heB : B.toRepresentation = (quotientImage ρ L J hJ.choose).toRepresentation := by
    apply MonoidHom.ext
    intro k
    apply LinearMap.ext
    rintro ⟨v,j,hj,rfl⟩
    rfl
  let : IsIrreducible A.toRepresentation := heA.symm ▸ quotientImage_irreducible ρ L I hI
  let : IsIrreducible B.toRepresentation := heB.symm ▸ quotientImage_irreducible ρ L J hJ
  have hfree : ∀ v, C.quotientRepresentation (s cubic) v = v → v = 0 :=
    fixedFree_of_surjective (ρ.comp s) (C.quotientRepresentation.comp s)
      C.toSubmodule.mkQ C.toSubmodule.mkQ_surjective (fun _ => rfl)
      (ambient_fixedFree_of_commutator ρ s hgen)
  obtain ⟨e⟩ := pair_isomorphic_in C.quotientRepresentation L.subtype s hs Q hfree A B
    (show A.toSubmodule ≤ Q.toSubmodule by
      change I.map (fixedSpace ρ L).mkQ ≤ (orbitSpan ρ ⊤ I).map (fixedSpace ρ L).mkQ
      rw [hpair]; exact le_sup_left)
    (show B.toSubmodule ≤ Q.toSubmodule by
      change J.map (fixedSpace ρ L).mkQ ≤ (orbitSpan ρ ⊤ I).map (fixedSpace ρ L).mkQ
      rw [hpair]; exact le_sup_right)
    hd hpair.symm
  refine ⟨e.toLinearEquiv, ?_⟩
  intro k v
  rw [← heA, ← heB]
  exact e.toIntertwiningMap.isIntertwining _ _ k v
end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit
