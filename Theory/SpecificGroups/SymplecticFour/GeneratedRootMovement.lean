module
public import Theory.SpecificGroups.SymplecticFour.QuadraticPlane
public import Theory.SpecificGroups.SymplecticFour.RootDisplacement

/-!
# A generated symplectic root cannot be fixed by the quadratic mover

A quadratic subgroup of order larger than the field has a self-orthogonal
plane as both its displacement and fixed space. If a second actor's
displacement lies in that plane, it fixes the whole plane. Adding an actor
whose displacement has dimension at most one still leaves a nonzero fixed
vector, so these three subgroups cannot generate the full symplectic group.

The conjugation formula keeps the exact natural action when the last actor
is a conjugate of a full root. The source application is the selected pair
in MS93 (5.6)--(5.11), pp.917--924, via
Sp4Four.SourceComparison.OriginalGeneratedRootMovement.
-/

public noncomputable section
open Matrix Subgroup Representation
open Representation.OneCohomology.SymplecticFour
namespace Theory.SpecificGroups.SymplecticFour
open TwoLocalCover
variable {F : Type*} [Field F]

theorem displacementSpace_conjugate (A : Subgroup (Sp F)) (g : Sp F) :
    displacementSpace (A.map (MulAut.conj g).toMonoidHom) =
      (displacementSpace A).map (toLinear g).toLinearMap := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨y,v⟩,rfl⟩
    obtain ⟨a,ha,he⟩ := y.property
    change y.val • v-v ∈ _
    rw [←he]
    refine ⟨a • (g⁻¹ • v) - g⁻¹ • v,
      Coinvariants.sub_mem_ker (ρ := (symplecticNatural 2).comp A.subtype) ⟨a,ha⟩ _,?_⟩
    change g • (a • (g⁻¹ • v) - g⁻¹ • v) = (g*a*g⁻¹) • v-v
    rw [smul_sub,smul_inv_smul,mul_smul,mul_smul]
  · apply Submodule.map_le_iff_le_comap.mpr
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨a,v⟩,rfl⟩
    change toLinear g (a.val • v-v) ∈ displacementSpace (A.map (MulAut.conj g).toMonoidHom)
    rw [toLinear_apply]
    have h := Coinvariants.sub_mem_ker
      (ρ := (symplecticNatural 2).comp (A.map (MulAut.conj g).toMonoidHom).subtype)
      ⟨g*a.val*g⁻¹,mem_map_of_mem (MulAut.conj g).toMonoidHom a.property⟩ (g • v)
    change (g*a.val*g⁻¹) • (g • v)-g • v ∈ displacementSpace (A.map (MulAut.conj g).toMonoidHom) at h
    simpa only [smul_sub,mul_smul,inv_smul_smul] using h

private theorem fixedSpace_top_zero (v : Vector F)
    (hv : ∀ g : Sp F, g • v = v) : v = 0 := by
  have h0 := congrFun (hv (rootElement 0 1)) (.inl 0)
  have h2 := congrFun (hv (rootElement 2 1)) (.inl 1)
  have h1 := congrFun (hv (rootElement 1 1)) (.inr 0)
  have h3 := congrFun (hv (rootElement 3 1)) (.inr 1)
  simp [rootElement,rootMatrix,Matrix.mulVec,dotProduct,
    Fintype.sum_sum_type,Fin.sum_univ_two,Matrix.single,Matrix.fromBlocks] at h0 h2 h1 h3
  ext i
  rcases i with i | i <;> fin_cases i
  · exact h1
  · exact h3
  · exact h0
  · exact h2

variable [Finite F]
/-- A large quadratic actor and two roots cannot generate the symplectic
group if the first root's displacement is fixed by that actor. -/
theorem generated_root_displacement_not_fixed
    (E A B : Subgroup (Sp F))
    (hE : ∀ x ∈ E, ∀ y ∈ E, ∀ v : Vector F, x • (y • v-v)=y • v-v)
    (hlarge : Nat.card F < Nat.card E)
    (hB : Module.finrank F (displacementSpace B) ≤ 1)
    (hgen : (E ⊔ A) ⊔ B = ⊤) :
    ¬ displacementSpace A ≤ fixedSpace E := by
  intro hA
  let P := displacementSpace E
  have hself : (form F).orthogonal P = P :=
    large_quadratic_displacement_self_orthogonal E hE hlarge
  have hPE : P = fixedSpace E := hself.symm.trans (orthogonal_displacementSpace E)
  have hPA : P ≤ fixedSpace A := by
    rw [←orthogonal_displacementSpace]
    intro v hv w hw
    have hwP : w ∈ P := hPE.symm ▸ hA hw
    exact (hself.symm ▸ hv) w hwP
  have hdimP : Module.finrank F P = 2 := by
    have h := LinearMap.BilinForm.finrank_orthogonal (B := form F) form_nondegenerate P
    rw [hself] at h
    have hV : Module.finrank F (Vector F) = 4 := by simp [Vector]
    rw [hV] at h
    omega
  have hdimB : 3 ≤ Module.finrank F (fixedSpace B) := by
    rw [←orthogonal_displacementSpace,
      LinearMap.BilinForm.finrank_orthogonal form_nondegenerate]
    have hV : Module.finrank F (Vector F) = 4 := by simp [Vector]
    rw [hV]
    omega
  have hne : P ⊓ fixedSpace B ≠ ⊥ := by
    intro hz
    have h := Submodule.finrank_sup_add_finrank_inf_eq P (fixedSpace B)
    rw [hz,finrank_bot] at h
    have hu := (P ⊔ fixedSpace B).finrank_le
    have hV : Module.finrank F (Vector F) = 4 := by simp [Vector]
    rw [hV] at hu
    omega
  obtain ⟨v,hv,hvne⟩ := (P ⊓ fixedSpace B).ne_bot_iff.mp hne
  have hfix : (E ⊔ A) ⊔ B ≤ MulAction.stabilizer (Sp F) v := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro g hg
      exact (hPE ▸ hv.1) g hg
    · intro g hg
      exact hPA hv.1 g hg
    · intro g hg
      exact hv.2 g hg
  rw [hgen] at hfix
  exact hvne (fixedSpace_top_zero v (fun g => hfix (mem_top g)))

end Theory.SpecificGroups.SymplecticFour
