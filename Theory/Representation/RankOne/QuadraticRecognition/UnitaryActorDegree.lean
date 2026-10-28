module
public import Theory.Representation.RankOne.QuadraticRecognition.UnitaryGeneration
public import Theory.Representation.RankOne.QuadraticRecognition.QuadraticPairs
public import Theory.Representation.BinaryOffender.SectionLinear
public import Theory.Representation.BinaryOffender.SubgroupConjugateDimension
public import Theory.Representation.SU3.BinaryDegree

/-!
# Field-square bounds for small unitary root actors

Three conjugates of a central-root actor of order at least four generate the
actual unitary group. Quotienting by global fixed vectors preserves a
nontrivial action because the group is perfect. The quotient has no new fixed
vectors, so its dimension is at most three times the actor's fixed
codimension. The established binary minimum degree 6n gives fixed codimension
at least 2n, and hence |V/C_V(A)|≥q².

Neither irreducibility, faithfulness, quadraticity nor fixed-space generation
is needed beyond nontriviality of the original action. Both actual SU₃ and
PSU₃ carriers are covered, including q=8. This is the small-actor generation
estimate used in DGS85 (5.10)(b), printed p.112. UnitaryTorus applies it to the
individual-element bound; CriticalUnitaryTorus retains the original quotient.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
open BenderSuzuki.MatrixGroups
open HermitianForm.BorelTorus.EvenCenterAction
open Representation.SU3.CubicDegree.InnerActors.ThreeRoots
namespace Representation.RankOne.QuadraticRecognition
variable {F : Type*} [Field F] [Finite F] [CharP F 2]
variable (J : HermitianForm 3 F) (hJ : J.form=!![0,0,1;0,1,0;1,0,0])

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

private theorem quotient_nontrivial_of_perfect [Group.IsPerfect G]
    (ρ : Representation (ZMod 2) G V) (hnt : ∃ g, ρ g≠1) :
    ∃ g, globalFixedQuotient ρ g≠1 := by
  by_contra! he
  have hc : subspaceCommutator ρ ⊤ ⊤ ≤ fixedSpace ρ ⊤ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g,_,v,_,rfl⟩
    exact (Submodule.Quotient.eq _).mp
      (LinearMap.congr_fun (he g) ((fixedSpace ρ ⊤).mkQ v))
  have hf := le_fixedSpace_of_commutator_le_fixedSpace ρ (⊤ : Subgroup G) ⊤
    (le_subspaceStabilizer ρ ⊤ (by intros; trivial)) hc
  obtain ⟨g,hg⟩ := hnt
  apply hg
  ext v
  exact hf Submodule.mem_top ⟨g,mem_top g⟩

private theorem degree_le_three [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G)
    (hfix : fixedSpace ρ ⊤=⊥) (g h : G)
    (hgen : A ⊔ A.map (MulAut.conj g).toMonoidHom ⊔ A.map (MulAut.conj h).toMonoidHom=⊤) :
    Module.finrank (ZMod 2) V≤3*fixedCodim ρ A := by
  let c : Fin 3 → G := ![1,g,h]
  have hc : (⊤ : Subgroup G) ≤ ⨆ i, A.map (MulAut.conj (c i)).toMonoidHom := by
    rw [←hgen]
    refine sup_le (sup_le ?_ ?_) ?_
    · have he : (MulAut.conj (c 0)).toMonoidHom=MonoidHom.id G := by ext x; simp [c]
      simpa only [he,Subgroup.map_id] using le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) 0
    · exact le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) 1
    · exact le_iSup (fun i => A.map (MulAut.conj (c i)).toMonoidHom) 2
  simpa only [Fintype.card_fin] using
    finrank_le_card_mul_fixedCodim_of_subgroup_conjugates ρ ⊤ A hfix c hc

/-- Every central-root actor of order at least four moves two full field
 degrees in every nontrivial SU₃ representation. -/
theorem su3_root_actor_fixedCodim_lower
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (hnt : ∃ g, ρ g≠1)
    (A : Subgroup J.specialSubgroup) (hA : A≤central J hJ) (hAc : 4≤Nat.card A) :
    2*n≤fixedCodim ρ A := by
  let : Group.IsPerfect J.specialSubgroup := SU3.BinaryDegree.isPerfect_specialSubgroup J hn hcard hconj
  let σ := globalFixedQuotient ρ
  have hσ := quotient_nontrivial_of_perfect ρ hnt
  have hσfix := globalFixedQuotient_fixed_eq_bot ρ
  obtain ⟨g,h,hgen⟩ := su3_root_three_conjugates J hJ hn hcard hconj A hA hAc
  have hu := degree_le_three σ A hσfix g h hgen
  have hl := SU3.BinaryDegree.finrank_ge J hn hcard hconj σ hσ
  have hd := fixedCodim_quotient_add_subrepresentation_le ρ (globalFixedSubrepresentation ρ) A
  change fixedCodim σ A + _≤fixedCodim ρ A at hd
  omega

/-- The identical bound on the actual projective carrier preserves all
 scalar-quotient conventions. -/
theorem psu3_root_actor_fixedCodim_lower
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n))
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hnt : ∃ g, ρ g≠1)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A≤centralImage J hJ) (hAc : 4≤Nat.card A) :
    2*n≤fixedCodim ρ A := by
  let : Group.IsPerfect J.specialSubgroup := SU3.BinaryDegree.isPerfect_specialSubgroup J hn hcard hconj
  let : Group.IsPerfect (ProjectiveSpecialUnitaryMatrixGroup J) :=
    Group.IsPerfect.ofSurjective J.specialToProjective_surjective
  let σ := globalFixedQuotient ρ
  have hσ := quotient_nontrivial_of_perfect ρ hnt
  have hσfix := globalFixedQuotient_fixed_eq_bot ρ
  obtain ⟨g,h,hgen⟩ := psu3_root_three_conjugates J hJ hn hcard hconj A hA hAc
  have hu := degree_le_three σ A hσfix g h hgen
  have hnt' : ∃ g, (σ.comp J.specialToProjective) g≠1 := by
    obtain ⟨g,hg⟩ := hσ
    obtain ⟨x,rfl⟩ := J.specialToProjective_surjective g
    exact ⟨x,hg⟩
  have hl := SU3.BinaryDegree.finrank_ge J hn hcard hconj (σ.comp J.specialToProjective) hnt'
  have hd := fixedCodim_quotient_add_subrepresentation_le ρ (globalFixedSubrepresentation ρ) A
  change fixedCodim σ A + _≤fixedCodim ρ A at hd
  omega

/-- The source field-order estimate for a special unitary actor. -/
theorem su3_root_actor_field_index
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n)) [Finite V]
    (ρ : Representation (ZMod 2) J.specialSubgroup V) (hnt : ∃ g, ρ g≠1)
    (A : Subgroup J.specialSubgroup) (hA : A≤central J hJ) (hAc : 4≤Nat.card A) :
    2^(2*n)≤Nat.card (V ⧸ fixedSpace ρ A) := by
  have hd := su3_root_actor_fixedCodim_lower J hJ hn hcard hconj ρ hnt A hA hAc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hd

/-- The same field-order estimate for the projective actor. -/
theorem psu3_root_actor_field_index
    {n : ℕ} (hn : 2≤n) (hcard : Nat.card F=(2^n)^2)
    (hconj : ∀ x, J.conj x=x^(2^n)) [Finite V]
    (ρ : Representation (ZMod 2) (ProjectiveSpecialUnitaryMatrixGroup J) V)
    (hnt : ∃ g, ρ g≠1)
    (A : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J))
    (hA : A≤centralImage J hJ) (hAc : 4≤Nat.card A) :
    2^(2*n)≤Nat.card (V ⧸ fixedSpace ρ A) := by
  have hd := psu3_root_actor_fixedCodim_lower J hJ hn hcard hconj ρ hnt A hA hAc
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod]
  exact Nat.pow_le_pow_right (by decide) hd

end Representation.RankOne.QuadraticRecognition
