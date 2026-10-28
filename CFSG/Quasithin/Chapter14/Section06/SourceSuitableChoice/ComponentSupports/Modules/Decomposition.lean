module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.ComponentSupports.Geometry
public import Theory.Representation.BinaryConjugationSection.GaschutzDecomposition
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Theory.GroupTheory.PlaneConjugateSpan
public import Theory.GroupTheory.CentralOverlapSupportMovement
public import Theory.Representation.BinaryConjugationSection.ConjugationCoordinates
public import Theory.Representation.BinaryConjugationSection.CommutatorImage
public import Theory.Representation.BinaryOffender.ComponentSum

/-!
# The fixed-part decomposition on the terminal source section

The original plane has order four and its central line has order two, so
the literal Sylow fixes its image. Gaschütz and generation by its conjugates
then decompose U/Z into its H-commutator image plus its H-fixed part. The
remaining component-module recognition must identify this commutator image
with the component contributions in 14.6.23(3).

Perfectness also identifies the preimage of component-fixed points modulo Z
with the actual component centralizer. Both statements use H=Mc and
U=conjugateSpanBy (localModule T M) Mc, with the original central kernel.
Source: Aschbacher--Smith, printed p.1038.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.OneCohomology
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06.ComponentSupports
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))


include hG hempty hM hunique hmany hcard e hab

/-- Gaschütz gives the fixed-part sum on the literal terminal quotient.
No component decomposition or module classification is assumed. -/
theorem source_commutator_sup_fixed
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) Mc X)
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) ρ) :
    c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc, Mc⁆ ⊔ fixed ρ = ⊤ := by
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  have hcomm := plane_line_commutator (localModule T M) (centralInvolutions T)
    (T : Subgroup G) h.point_lt.le hcard h.point_card h.T_normalizes_V h.normalizes_point
  apply c.sup_fixed_eq_top_of_sylow_fixed_seed (localModule T M)
    (le_conjugateSpanBy _ _) rfl (T.subtype h.T_le_H)
  · intro v s
    exact (c.fixed_coordinate_iff_commutator_mem s.val
      (inclusion (le_conjugateSpanBy _ _) v)).mpr
        (hcomm (commutator_mem_commutator v.property s.property))
  · intro a x
    apply c.displacement_range_le_imageSpace_of_commutator_le Mc
      ⁅conjugateSpanBy (localModule T M) Mc,Mc⁆
      (by rw [commutator_comm]) a a.property
    exact ⟨x,rfl⟩

/-- Component-fixed points in U/Z lift precisely to C_U(K), since the
component is perfect and the original kernel Z centralizes Mc. -/
theorem source_component_fixed_preimage
    (K : Subgroup G) [Group.IsPerfect K] (hKM : K ≤ Mc) :
    commutatorPreimage (conjugateSpanBy (localModule T M) Mc) K (centralInvolutions T) =
      conjugateSpanBy (localModule T M) Mc ⊓ centralizer (K : Set G) := by
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  exact commutatorPreimage_eq_inf_centralizer_of_perfect K _ _
    (h.UH_le_H.trans (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _)))
    (le_centralizer_iff.mpr (hKM.trans h.H_centralizes))

/-- The preceding decomposition has canonical coordinates on the actual U/Z.
There is no additional module-identification assumption. -/
theorem source_canonical_commutator_decomposition :
    let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
    let _ : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
      h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
    let U := conjugateSpanBy (localModule T M) Mc
    let Z := centralInvolutions T
    ∃ ρ : Representation (ZMod 2) Mc (Additive (U ⧸ Z.subgroupOf U)),
      ∃ c : BinaryConjugationSection Mc U Z ρ,
        c.imageSpace ⁅U, Mc⁆ ⊔ fixed ρ = ⊤ := by
  dsimp only
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  let : IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) Mc) :=
    h.UH_elementary_of_V_le_QH ((le_conjugateSpanBy _ _).trans h.UH_le_QH)
  obtain ⟨ρ,⟨c⟩⟩ := BinaryConjugationSection.exists_conjugation_coordinates Mc
    (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T) h.UH_le_H
    (le_normalizer_conjugateSpanBy _ _) (h.point_lt.le.trans (le_conjugateSpanBy _ _))
    (h.H_centralizes.trans (Subgroup.centralizer_le_normalizer _))
  exact ⟨ρ,c,source_commutator_sup_fixed hG T hempty hM hunique hmany hcard e hab ρ c⟩
/-- The source factorization H=(join of its components)T gives the sum in
14.6.23(3), on the literal U/Z coordinates. The hsplit premise is discharged
by 14.6.21 and 14.6.23(1), owned by the component-alternatives producer.
Directness of the component contributions remains a module-recognition step. -/
theorem source_component_sum_sup_fixed
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (ρ : Representation (ZMod 2) Mc X)
    (c : BinaryConjugationSection Mc (conjugateSpanBy (localModule T M) Mc)
      (centralInvolutions T) ρ)
    {ι : Type*} (K : ι → Subgroup G) (hKM : ∀ i, K i ≤ Mc)
    (hsplit : ∀ m : Mc, ∃ j ∈ (⨆ i, (K i).subgroupOf Mc),
      ∃ s : Mc, (s : G) ∈ (T : Subgroup G) ∧ j * s = m) :
    (⨆ i, c.imageSpace ⁅conjugateSpanBy (localModule T M) Mc, K i⁆) ⊔ fixed ρ = ⊤ := by
  let h := terminal_hypothesis hG T hempty hM hunique hmany hcard e hab
  have hcomm := plane_line_commutator (localModule T M) (centralInvolutions T)
    (T : Subgroup G) h.point_lt.le hcard h.point_card h.T_normalizes_V h.normalizes_point
  have htop : c.imageSpace (conjugateSpanBy (localModule T M) Mc) = ⊤ := by
    apply top_unique
    intro v _
    obtain ⟨u,hu⟩ := c.onto (Multiplicative.ofAdd v)
    exact (c.mem_imageSpace_iff _ _).mpr ⟨u,u.property,hu⟩
  apply c.sup_fixed_eq_top_of_sylow_supplement (localModule T M)
    (le_conjugateSpanBy _ _) rfl (T.subtype h.T_le_H)
  · intro v s
    exact (c.fixed_coordinate_iff_commutator_mem s.val
      (inclusion (le_conjugateSpanBy _ _) v)).mpr
        (hcomm (commutator_mem_commutator v.property s.property))
  · intro m
    obtain ⟨j,hj,s,hs,he⟩ := hsplit m
    exact ⟨j,hj,s,hs,he⟩
  · intro j hj x
    have hn : ρ j x - x ∈ BinaryOffender.subspaceCommutator ρ ⊤
        (⨆ i, (K i).subgroupOf Mc) :=
      Submodule.subset_span ⟨j,hj,x,Submodule.mem_top,rfl⟩
    rw [BinaryOffender.subspaceCommutator_iSup_family] at hn
    convert hn using 1
    congr 1
    funext i
    rw [commutator_comm, c.imageSpace_commutator (K i) _ (hKM i) le_rfl, htop]
end CFSG.Quasithin.Chapter14.Section06.ComponentSupports
