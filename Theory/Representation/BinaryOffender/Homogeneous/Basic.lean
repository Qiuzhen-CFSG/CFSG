module

public import Theory.Representation.BinaryOffender.FixedQuotientKernel
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration

/-!
# Literal homogeneous irreducible sections

This lower-layer form of Definition A.1.40 uses the original fixed-space
quotient and actual equivariant linear equivalences. An Irr⁺ member is
homogeneous when its central image is the full isotypic component of that
image in the span of its conjugates. The quotient comparison lemma removes
central error terms using full commutator generation.

The definitions and elementary transport proofs agree definitionally with the
existing Chapter 15 `SourceRestrictions.Cases.Sections` interface. They are
reproduced here to make homogeneous selection independent of that consumer;
no existence theorem is assumed by the definitions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Definition A.1.40 and Lemma A.1.42, printed pp.31–32.
-/

@[expose] public section

open Representation Representation.BinaryOffender Subgroup
namespace Representation.BinaryOffender.Homogeneous
variable {D V : Type*} [Group D] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) D V)

noncomputable def orbitSpan (T : Subgroup D) (I : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V := ⨆ t : T, I.map (ρ t)

theorem le_orbitSpan (T : Subgroup D) (I : Submodule (ZMod 2) V) :
    I ≤ orbitSpan ρ T I := by
  intro v hv
  apply le_iSup (fun t : T => I.map (ρ t)) (1 : T)
  exact ⟨v, hv, by simp⟩

theorem orbitSpan_invariant (T : Subgroup D) (I : Submodule (ZMod 2) V) :
    T ≤ subspaceStabilizer ρ (orbitSpan ρ T I) := by
  apply le_subspaceStabilizer
  intro t ht v hv
  change v ∈ ⨆ s : T, I.map (ρ s) at hv
  refine Submodule.iSup_induction (fun s : T => I.map (ρ s))
    (motive := fun w => ρ t w ∈ orbitSpan ρ T I) hv ?_ ?_ ?_
  · intro s x hx
    obtain ⟨i, hi, rfl⟩ := hx
    apply (le_iSup (fun s : T => I.map (ρ s)) (⟨t, ht⟩ * s))
    exact ⟨i, hi, by simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · simp
  · intro x y hx hy
    simpa only [map_add] using (orbitSpan ρ T I).add_mem hx hy

theorem orbitSpan_le {T : Subgroup D} {I J : Submodule (ZMod 2) V}
    (hIJ : I ≤ J) (hJ : T ≤ subspaceStabilizer ρ J) : orbitSpan ρ T I ≤ J := by
  apply iSup_le
  rintro t _ ⟨v, hv, rfl⟩
  exact (hJ t.property v).2 (hIJ hv)

theorem orbitSpan_eq_self {T : Subgroup D} {I : Submodule (ZMod 2) V}
    (hI : T ≤ subspaceStabilizer ρ I) : orbitSpan ρ T I = I :=
  le_antisymm (orbitSpan_le ρ le_rfl hI) (le_orbitSpan ρ T I)

theorem orbitSpan_component_invariant {K T : Subgroup D}
    (hTK : T ≤ normalizer (K : Set D)) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ K I) : K ≤ subspaceStabilizer ρ (orbitSpan ρ T I) := by
  apply le_subspaceStabilizer
  intro k hk v hv
  change v ∈ ⨆ t : T, I.map (ρ t) at hv
  refine Submodule.iSup_induction (fun t : T => I.map (ρ t))
    (motive := fun w => ρ k w ∈ orbitSpan ρ T I) hv ?_ ?_ ?_
  · intro t v hv
    exact (le_iSup (fun t : T => I.map (ρ t)) t)
        (((hI.map_normalizer ρ (hTK t.property)).choose hk v).2 hv)
  · simp
  · intro x y hx hy
    simpa only [map_add] using (orbitSpan ρ T I).add_mem hx hy

theorem orbitSpan_full_commutator {K T : Subgroup D}
    (hTK : T ≤ normalizer (K : Set D)) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ K I) :
    subspaceCommutator ρ (orbitSpan ρ T I) K = orbitSpan ρ T I := by
  apply le_antisymm (subspaceCommutator_le_of_invariant ρ
    (orbitSpan_component_invariant ρ hTK hI))
  apply iSup_le
  intro t
  rw [← (hI.map_normalizer ρ (hTK t.property)).choose_spec.1]
  exact subspaceCommutator_mono_left ρ (le_iSup (fun t : T => I.map (ρ t)) t) K

theorem orbitSpan_ne_bot {K T : Subgroup D} {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ K I) : orbitSpan ρ T I ≠ ⊥ := by
  intro h
  exact hI.ne_bot ρ (le_bot_iff.mp (h ▸ le_orbitSpan ρ T I))

/-- If K and T generate the actor, the orbit span is an actual subrepresentation. -/
noncomputable def orbitSubrepresentation {K T : Subgroup D}
    (hTK : T ≤ normalizer (K : Set D)) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ K I) (hgen : K ⊔ T = ⊤) : Subrepresentation ρ where
  toSubmodule := orbitSpan ρ T I
  apply_mem_toSubmodule g v hv := by
    have hstab : K ⊔ T ≤ subspaceStabilizer ρ (orbitSpan ρ T I) :=
      sup_le (orbitSpan_component_invariant ρ hTK hI) (orbitSpan_invariant ρ T I)
    rw [hgen] at hstab
    exact (hstab (Subgroup.mem_top g) v).2 hv

/-- The source uses right conjugates: v^t is the action of t⁻¹. -/
def rightConjugate (I : Submodule (ZMod 2) V) (t : D) : Submodule (ZMod 2) V :=
  I.map (ρ t⁻¹)

theorem rightConjugate_le_orbitSpan (T : Subgroup D) (I : Submodule (ZMod 2) V)
    {t : D} (ht : t ∈ T) : rightConjugate ρ I t ≤ orbitSpan ρ T I :=
  le_iSup (fun t : T => I.map (ρ t)) (⟨t⁻¹, T.inv_mem ht⟩ : T)

theorem orbitSpan_eq_iSup_rightConjugate (T : Subgroup D) (I : Submodule (ZMod 2) V) :
    orbitSpan ρ T I = ⨆ t : T, rightConjugate ρ I t := by
  apply le_antisymm
  · apply iSup_le
    intro t
    simpa only [rightConjugate, Subgroup.coe_inv, inv_inv] using
      (le_iSup (fun t : T => rightConjugate ρ I t) t⁻¹)
  · exact iSup_le fun t => rightConjugate_le_orbitSpan ρ T I t.property

noncomputable def quotientImage (K : Subgroup D) (I : Submodule (ZMod 2) V)
    (hI : K ≤ subspaceStabilizer ρ I) : Subrepresentation (fixedQuotientRepresentation ρ K) where
  toSubmodule := I.map (fixedSpace ρ K).mkQ
  apply_mem_toSubmodule k v hv := by
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨ρ k w, (hI k.property w).2 hw, rfl⟩

def SameModule {E W : Type*} [Group E] [AddCommGroup W] [Module (ZMod 2) W]
    {σ : Representation (ZMod 2) E W} (I J : Subrepresentation σ) : Prop :=
  ∃ e : I.toSubmodule ≃ₗ[ZMod 2] J.toSubmodule,
    ∀ g v, e (I.toRepresentation g v) = J.toRepresentation g (e v)

/-- The actual map induced by I → V/C_V(K). -/
noncomputable def centralQuotientToImage (K : Subgroup D)
    (I : Submodule (ZMod 2) V) :
    centralQuotient ρ K I →ₗ[ZMod 2] I.map (fixedSpace ρ K).mkQ :=
  ((fixedSpace ρ K).comap I.subtype).liftQ
    (((fixedSpace ρ K).mkQ.comp I.subtype).codRestrict _
      (fun v => ⟨v, v.property, rfl⟩)) (by
        intro v hv
        apply Subtype.ext
        exact (Submodule.Quotient.mk_eq_zero _).mpr hv)

theorem centralQuotientToImage_bijective (K : Subgroup D)
    (I : Submodule (ZMod 2) V) : Function.Bijective (centralQuotientToImage ρ K I) := by
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro q hq
    induction q using Submodule.Quotient.induction_on with
    | _ v =>
      apply (Submodule.Quotient.mk_eq_zero _).mpr
      change (v : V) ∈ fixedSpace ρ K
      exact (Submodule.Quotient.mk_eq_zero (fixedSpace ρ K)).mp (congrArg Subtype.val hq)
  · rintro ⟨q, v, hv, rfl⟩
    exact ⟨Submodule.Quotient.mk (⟨v, hv⟩ : I), rfl⟩

/-- I/C_I(K) is the image of I in V/C_V(K), by a specified linear map. -/
noncomputable def centralQuotientImageEquiv (K : Subgroup D)
    (I : Submodule (ZMod 2) V) :
    centralQuotient ρ K I ≃ₗ[ZMod 2] I.map (fixedSpace ρ K).mkQ :=
  LinearEquiv.ofBijective _ (centralQuotientToImage_bijective ρ K I)

theorem centralQuotientImageEquiv_equivariant (K : Subgroup D)
    (I : Submodule (ZMod 2) V) (hI : K ≤ subspaceStabilizer ρ I)
    (g : K) (v : centralQuotient ρ K I) :
    centralQuotientImageEquiv ρ K I (centralQuotientRepresentation ρ K I hI g v) =
      (quotientImage ρ K I hI).toRepresentation g (centralQuotientImageEquiv ρ K I v) := by
  induction v using Submodule.Quotient.induction_on with
  | _ v => rfl

/-- Full commutator subspaces can be compared through their central images. -/
theorem le_of_quotientImage_le {K : Subgroup D} {I J : Submodule (ZMod 2) V}
    (hI : subspaceCommutator ρ I K = I) (hJ : K ≤ subspaceStabilizer ρ J)
    (h : I.map (fixedSpace ρ K).mkQ ≤ J.map (fixedSpace ρ K).mkQ) : I ≤ J := by
  rw [← hI]
  apply subspaceCommutator_le_of_le_sup_fixedSpace ρ hJ
  intro v hv
  obtain ⟨j, hj, he⟩ := h ⟨v, hv, rfl⟩
  have hz : v - j ∈ fixedSpace ρ K := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change (fixedSpace ρ K).mkQ (v - j) = 0
    rw [map_sub, he, sub_self]
  exact Submodule.mem_sup.mpr ⟨j, hj, v - j, hz, by abel⟩

/-- A two-summand identity modulo C_V(K) lifts to the literal I_T=I+I^t.
Full commutator generation removes the apparent central error term. -/
theorem orbitSpan_eq_sup_of_quotientImage_eq {K T : Subgroup D}
    (hTK : T ≤ normalizer (K : Set D)) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ K I) {t : D} (ht : t ∈ T)
    (h : (orbitSpan ρ T I).map (fixedSpace ρ K).mkQ =
      (I ⊔ rightConjugate ρ I t).map (fixedSpace ρ K).mkQ) :
    orbitSpan ρ T I = I ⊔ rightConjugate ρ I t := by
  apply le_antisymm
  · exact le_of_quotientImage_le ρ (orbitSpan_full_commutator ρ hTK hI)
      (subspaceStabilizer_sup ρ hI.choose
        (hI.map_normalizer ρ (hTK (T.inv_mem ht))).choose) h.le
  · exact sup_le (le_orbitSpan ρ T I) (rightConjugate_le_orbitSpan ρ T I ht)

noncomputable def homogeneousPart {E W : Type*} [Group E] [AddCommGroup W]
    [Module (ZMod 2) W] {σ : Representation (ZMod 2) E W}
    (I : Subrepresentation σ) (W₀ : Submodule (ZMod 2) W) : Submodule (ZMod 2) W :=
  ⨆ (J : Subrepresentation σ) (_ : J.toSubmodule ≤ W₀ ∧ SameModule I J), J.toSubmodule

/-- Literal A.1.40: the image of I in V/C_V(K) is its K-homogeneous
component inside the image of its T-orbit span. -/
structure IsIrrPlusWith (K T : Subgroup D) (I : Submodule (ZMod 2) V) : Prop where
  normalizes : T ≤ normalizer (K : Set D)
  invariant : K ≤ subspaceStabilizer ρ I
  isIrrPlus : IsIrrPlus ρ K I
  homogeneous : homogeneousPart (quotientImage ρ K I invariant)
      ((orbitSpan ρ T I).map (fixedSpace ρ K).mkQ) = I.map (fixedSpace ρ K).mkQ

theorem quotientImage_le_homogeneousPart {K T : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : K ≤ subspaceStabilizer ρ I) :
    I.map (fixedSpace ρ K).mkQ ≤ homogeneousPart (quotientImage ρ K I hI)
      ((orbitSpan ρ T I).map (fixedSpace ρ K).mkQ) := by
  apply le_iSup_of_le (quotientImage ρ K I hI)
  apply le_iSup_of_le
    (show (quotientImage ρ K I hI).toSubmodule ≤
        (orbitSpan ρ T I).map (fixedSpace ρ K).mkQ ∧
      SameModule (quotientImage ρ K I hI) (quotientImage ρ K I hI) from
      ⟨Submodule.map_mono (le_orbitSpan ρ T I), ⟨LinearEquiv.refl _ _, fun _ _ => rfl⟩⟩)
  exact le_rfl

/-- Homogeneity says every isomorphic K-submodule of the orbit image is
already in the chosen image. This quantifies over actual equivariant maps. -/
theorem IsIrrPlusWith.contains_isomorphic {K T : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K T I)
    (J : Subrepresentation (fixedQuotientRepresentation ρ K))
    (hJ : J.toSubmodule ≤ (orbitSpan ρ T I).map (fixedSpace ρ K).mkQ)
    (he : SameModule (quotientImage ρ K I hI.invariant) J) :
    J.toSubmodule ≤ I.map (fixedSpace ρ K).mkQ := by
  rw [← hI.homogeneous]
  exact le_iSup_of_le J (le_iSup_of_le ⟨hJ, he⟩ le_rfl)

/-- In the homogeneous family, isomorphic conjugate central images force
equality of the original sections, rather than equality only modulo the centre. -/
theorem IsIrrPlusWith.eq_of_isomorphic_conjugate {K T : Subgroup D}
    {I : Submodule (ZMod 2) V} (hI : IsIrrPlusWith ρ K T I) (t : T)
    (he : SameModule (quotientImage ρ K I hI.invariant)
      (quotientImage ρ K (I.map (ρ t))
        (hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)).choose)) :
    I.map (ρ t) = I := by
  have ht := hI.isIrrPlus.map_normalizer ρ (hI.normalizes t.property)
  apply ht.eq_of_le ρ hI.isIrrPlus
  apply le_of_quotientImage_le ρ ht.choose_spec.1 hI.invariant
  exact hI.contains_isomorphic ρ _
    (Submodule.map_mono (le_iSup (fun t : T => I.map (ρ t)) t)) he

end Representation.BinaryOffender.Homogeneous
