module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SectionCoordinates
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit.Selection
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.SeedAction

/-!
# The literal two-conjugate cubic orbit

The cubic norm vanishes on the source module, so the X-orbit of any
subspace is the sum of that subspace and its right conjugate by the
inverse cubic generator. If K, X and P generate the actor, normality of
X and P-invariance of the selected constituent make that sum invariant
under the whole group. The commuting inverted cubic action excludes a
single invariant Irr⁺ constituent and separates its two central images.

Group generation remains explicit in the abstract result. The source
H = KL₁T-to-KXP deduction is handled by CubicOrbit.GroupGeneration.
Source: Aschbacher–Smith, proof of 13.8.20(a), printed p.954, and
A.1.40–42, printed pp.31–32 (combined manuscript, 1 March 2004).
-/

@[expose] public noncomputable section

open Subgroup Representation Representation.BinaryOffender InvertedCubicTensor
open scoped TensorProduct IsMulCommutative
open CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.GenerationOne.RepresentationReduction.SourceRestrictions.Cases

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V) (L : Subgroup G) [L.Normal]
  (s : S₃ →* G) (hs : ∀ (k : L) g, Commute (k : G) (s g))


private theorem cubic_square (hgen : subspaceCommutator ρ ⊤
    ((alternatingGroup (Fin 3)).map s) = ⊤) (v : V) :
    ρ (s cubic) (ρ (s cubic) v) = v + ρ (s cubic) v := by
  have h3 (w : V) : ρ (s cubic) (ρ (s cubic) (ρ (s cubic) w)) = w := by
    change (ρ (s cubic) * ρ (s cubic) * ρ (s cubic)) w = w
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, cubic_cube, map_one,
      map_one, Module.End.one_apply]
  have hz : v + ρ (s cubic) v + ρ (s cubic) (ρ (s cubic) v) = 0 := by
    apply ambient_fixedFree_of_commutator ρ s hgen
    change ρ (s cubic) _ = _
    simp only [map_add, h3]
    abel
  have hneg (w : V) : -w = w := by
    apply neg_eq_iff_add_eq_zero.mpr
    simpa only [show (1 : ZMod 2) + 1 = 0 by decide, zero_smul, one_smul] using
      (add_smul (1 : ZMod 2) 1 w).symm
  simpa only [neg_add, hneg] using eq_neg_of_add_eq_zero_right hz

/-- The norm identity makes the literal cubic orbit a sum of two right
conjugates, using the inverse of the marked cubic generator. -/
theorem cubic_orbitSpan_eq_sup (I : Submodule (ZMod 2) V)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    orbitSpan ρ ((alternatingGroup (Fin 3)).map s) I =
      I ⊔ rightConjugate ρ I (s cubic)⁻¹ := by
  have hx : s cubic ∈ (alternatingGroup (Fin 3)).map s :=
    ⟨cubic, by change cubic ∈ alternatingGroup (Fin 3); exact Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel), rfl⟩
  apply le_antisymm
  · apply iSup_le
    rintro ⟨_,a,ha,rfl⟩ v ⟨i,hi,rfl⟩
    have hwords : a = 1 ∨ a = cubic ∨ a = cubic * cubic := by
      have h : ∀ a : S₃, Equiv.Perm.sign a = 1 →
          a = 1 ∨ a = cubic ∨ a = cubic * cubic := by decide +kernel
      exact h a (Equiv.Perm.mem_alternatingGroup.mp ha)
    rcases hwords with rfl | rfl | rfl
    · simpa using (show i ∈ I ⊔ rightConjugate ρ I (s cubic)⁻¹ from Submodule.mem_sup_left hi)
    · exact Submodule.mem_sup_right ⟨i,hi,by simp only [inv_inv]⟩
    · simp only [map_mul, Module.End.mul_apply, cubic_square ρ s hgen]
      exact Submodule.mem_sup.mpr ⟨i,hi,ρ (s cubic) i,
        ⟨i,hi,by simp only [inv_inv]⟩,rfl⟩
  · exact sup_le (le_orbitSpan ρ _ I)
      (rightConjugate_le_orbitSpan ρ _ I
        (((alternatingGroup (Fin 3)).map s).inv_mem hx))

private theorem orbitSpan_normalizer_stable (A B : Subgroup G)
    (hBA : B ≤ normalizer (A : Set G)) (I : Submodule (ZMod 2) V)
    (hBI : B ≤ subspaceStabilizer ρ I) :
    B ≤ subspaceStabilizer ρ (orbitSpan ρ A I) := by
  apply le_subspaceStabilizer
  intro b hb v hv
  change v ∈ ⨆ a : A, I.map (ρ a) at hv
  refine Submodule.iSup_induction (fun a : A => I.map (ρ a))
    (motive := fun w => ρ b w ∈ orbitSpan ρ A I) hv ?_ ?_ ?_
  · intro a v hv
    obtain ⟨i,hi,rfl⟩ := hv
    let a' : A := ⟨b * a * b⁻¹,
      le_normalizer_iff.mp hBA b hb a a.property⟩
    apply (le_iSup (fun a : A => I.map (ρ a)) a')
    refine ⟨ρ b i,(hBI hb i).mpr hi, ?_⟩
    change (ρ (b * a * b⁻¹) * ρ b) i = (ρ b * ρ a) i
    simp only [← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  · simp
  · intro x y hx hy
    simpa only [map_add] using (orbitSpan ρ A I).add_mem hx hy

include hs in
/-- Linear orbit calculation once the component, normal cubic group and
Sylow subgroup generate the actor. Deriving this group generation from the
source H = KL₁T setup is a separate obligation. -/
theorem selected_cubic_orbit_of_generation
    (P : Subgroup G) (I : Submodule (ZMod 2) V) (hI : IsIrrPlus ρ L I)
    (hIP : P ≤ subspaceStabilizer ρ I)
    (hX : ((alternatingGroup (Fin 3)).map s).Normal)
    (hactor : L ⊔ ((alternatingGroup (Fin 3)).map s ⊔ P) = ⊤)
    (hinj : Function.Injective s)
    (hgen : subspaceCommutator ρ ⊤ ((alternatingGroup (Fin 3)).map s) = ⊤) :
    (s cubic)⁻¹ ∈ (alternatingGroup (Fin 3)).map s ∧ (s cubic)⁻¹ ≠ 1 ∧
      rightConjugate ρ I (s cubic)⁻¹ ≠ I ∧
      I ≤ orbitSpan ρ ⊤ I ∧
      rightConjugate ρ I (s cubic)⁻¹ ≤ orbitSpan ρ ⊤ I ∧
      orbitSpan ρ ⊤ I = I ⊔ rightConjugate ρ I (s cubic)⁻¹ ∧
      Disjoint (I.map (fixedSpace ρ L).mkQ)
        ((rightConjugate ρ I (s cubic)⁻¹).map (fixedSpace ρ L).mkQ) := by
  let X := (alternatingGroup (Fin 3)).map s
  let _ : X.Normal := hX
  have hnorm : X ≤ normalizer (L : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hPnorm : P ≤ normalizer (X : Set G) := by
    rw [Subgroup.normalizer_eq_top]; exact le_top
  have hstable : (⊤ : Subgroup G) ≤ subspaceStabilizer ρ (orbitSpan ρ X I) := by
    rw [← hactor]
    exact sup_le (orbitSpan_component_invariant ρ hnorm hI)
      (sup_le (orbitSpan_invariant ρ X I)
        (orbitSpan_normalizer_stable ρ X P hPnorm I hIP))
  have horbit : orbitSpan ρ ⊤ I = I ⊔ rightConjugate ρ I (s cubic)⁻¹ := by
    apply le_antisymm
    · rw [← cubic_orbitSpan_eq_sup ρ s I hgen]
      exact orbitSpan_le ρ (le_orbitSpan ρ X I) hstable
    · exact sup_le (le_orbitSpan ρ ⊤ I)
        (rightConjugate_le_orbitSpan ρ ⊤ I (Subgroup.mem_top _))
  have hne : rightConjugate ρ I (s cubic)⁻¹ ≠ I := by
    intro he
    have hself : orbitSpan ρ ⊤ I = I := by rw [horbit, he, sup_idem]
    apply irrPlus_not_invariant ρ s L hs hgen I hI
    rw [← hself]
    exact orbitSpan_invariant ρ ⊤ I
  have hIt : IsIrrPlus ρ L (rightConjugate ρ I (s cubic)⁻¹) := by
    apply hI.map_normalizer ρ
    rw [Subgroup.normalizer_eq_top]
    trivial
  refine ⟨?_, ?_, hne, le_orbitSpan ρ ⊤ I,
    rightConjugate_le_orbitSpan ρ ⊤ I (Subgroup.mem_top _), horbit,
    hI.disjoint_quotientImages ρ hIt hne.symm⟩
  · apply ((alternatingGroup (Fin 3)).map s).inv_mem
    exact ⟨cubic, by change cubic ∈ alternatingGroup (Fin 3); exact Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel), rfl⟩
  · intro he
    have h : s cubic = s 1 := (inv_eq_one.mp he).trans s.map_one.symm
    exact (by decide +kernel : cubic ≠ 1) (hinj h)


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.HigherFieldReduction.ExternalModules.FFSections.SourceOrbit

end
