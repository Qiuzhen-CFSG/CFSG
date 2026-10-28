module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.Kernel
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.OddConfinement
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenExceptional.ReeFour.LowerObstruction.ComponentConfinement

/-!
# Assembly of the positive Ree lower obstruction

The long-root family is constructed from actual root matrices. Its weak
closure has a proper normalizer after transferring the source simplicity,
and both intrinsic quotient-rank conditions force a nontrivial intersection
with the appropriate local kernel. The two actual parabolic rank calculations
exclude E1, while long-root saturation and parabolic two-core containment
exclude E2 at the predecessor rank. These prove confinement in that normalizer.

This module transports the literal family, weak closure, normalizer and
ranked E-members to the source group using the proved positive-parameter
ambient equivalence and Sylow conjugacy. `exists_source_obstruction` discharges
both geometric premises of the retained conditional assembly and constructs
all predecessor-bound inputs at rank 2*m, with no additional SQTK premise.
The upper bound and the minimum giving the full value in E.1.14(1) are separate.

Source: Aschbacher--Smith, `refs/quasithin.pdf`, printed p.214 / PDF p.225,
citing Aschbacher, *GF(2)-representations of finite groups* (1982), Lemma 4.7,
DOI 10.2307/2374202. The E1 and E2 predicates used here have the corrected
local tau orbit and intrinsic quotient-rank conventions of E.1.2 and E.1.5.
-/

public section
namespace CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
open Subgroup ReeF4 ReeF4.Parabolics

/-- Apply the concrete rank-to-kernel calculation to both geometric branches.
This conditional reduction is instantiated by `confined_member` below. -/
theorem confined_member_of_kernel_confinement {m : ℕ} (hm : 0 < m)
    (hodd : ∀ A K : Subgroup (Model m), A ∈ rootFamily m →
      IsEMember (unipotent m) A K → ECaseOdd A K →
      A.subgroupOf K ⊓ pCore 2 K ≠ ⊥ → K ≤ modelNormalizer m)
    (hcomponent : ∀ A K : Subgroup (Model m), A ∈ rootFamily m →
      IsEMember (unipotent m) A K → ECaseComponent (unipotent m) A K →
      A.subgroupOf K ⊓ solvableRadical K ≠ ⊥ → K ≤ modelNormalizer m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMemberAt (2 * m) (unipotent m) A K) : K ≤ modelNormalizer m := by
  rcases member_kernel_alternatives hm hA hK with ho | hc
  · exact hodd A K hA hK.1 ho.1 ho.2
  · exact hcomponent A K hA hK.1 hc.1 hc.2

/-- Both proved parabolic calculations confine every predecessor-rank member
for the actual long-root family. The kernel-intersection premises are supplied
by the literal intrinsic quotient ranks, and no geometric premise remains. -/
theorem confined_member {m : ℕ} (hm : 0 < m)
    {A K : Subgroup (Model m)} (hA : A ∈ rootFamily m)
    (hK : IsEMemberAt (2 * m) (unipotent m) A K) : K ≤ modelNormalizer m :=
  confined_member_of_kernel_confinement hm
    (fun _ _ hB hJ ho hi => odd_member_le_modelNormalizer_of_kernel_meets_root
      hm hB hJ ho hi)
    (fun _ _ hB hJ hc hi => component_confined hm hB hJ hc hi) hA hK

variable {G : Type*} [Group G] [Finite G]

/-- Transport the literal E-member and its confinement through an aligned
whole-group equivalence, preserving the local tau and both quotient maps. -/
theorem confined_source_member {m : ℕ} (T : Sylow 2 G) (a : G ≃* Model m)
    (ha : (T : Subgroup G).map a.toMonoidHom = unipotent m)
    (hmodel : ∀ A K : Subgroup (Model m), A ∈ rootFamily m →
      IsEMemberAt (2 * m) (unipotent m) A K → K ≤ modelNormalizer m)
    {A K : Subgroup G} (hA : A ∈ family a)
    (hK : IsEMemberAt (2 * m) (T : Subgroup G) A K) : K ≤ overgroup a := by
  apply map_le_iff_le_comap.mp
  have hmap := hK.map_equiv a
  rw [ha] at hmap
  exact hmodel (A.map a.toMonoidHom) (K.map a.toMonoidHom) hA hmap

/-- The actual predecessor-obstruction inputs for the original ambient group,
conditional only on the two model confinement implications. The family and
proper overgroup are constructed here, not assumed as witnesses or supplied
through a non-generation statement. -/
theorem exists_source_obstruction_of_kernel_confinement
    (T : Sylow 2 G) (L : Subgroup G) [IsSimpleGroup L]
    (hL : L = Theory.GroupTheory.generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ} (hm : 0 < m)
    (e : L ≃* commutator (Model m))
    (hodd : ∀ A K : Subgroup (Model m), A ∈ rootFamily m →
      IsEMember (unipotent m) A K → ECaseOdd A K →
      A.subgroupOf K ⊓ pCore 2 K ≠ ⊥ → K ≤ modelNormalizer m)
    (hcomponent : ∀ A K : Subgroup (Model m), A ∈ rootFamily m →
      IsEMember (unipotent m) A K → ECaseComponent (unipotent m) A K →
      A.subgroupOf K ⊓ solvableRadical K ≠ ⊥ → K ≤ modelNormalizer m) :
    ∃ (Ω : Set (Subgroup G)) (M : Subgroup G),
      IsElementaryFamily Ω ∧ M ≠ ⊤ ∧
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M ∧
      ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
        ∀ K : Subgroup G, IsEMemberAt (2 * m) (T : Subgroup G) A K → K ≤ M := by
  obtain ⟨a, ha, hfamily, hproper, hnormalizer⟩ := exists_source_family T L hL hgen hm e
  refine ⟨family a, overgroup a, hfamily, hproper, hnormalizer.le, ?_⟩
  intro A hA _ K hK
  exact confined_source_member T a ha
    (fun _ _ hB hJ => confined_member_of_kernel_confinement hm hodd hcomponent hB hJ) hA hK

/-- The positive Ree predecessor obstruction in the original source group.
The family consists of transported full long-root groups, and the proper
overgroup is exactly their weak-closure normalizer. Both E1 and E2 confinement
premises are discharged by the actual model geometry. -/
theorem exists_source_obstruction
    (T : Sylow 2 G) (L : Subgroup G) [IsSimpleGroup L]
    (hL : L = Theory.GroupTheory.generalizedFitting G)
    (hgen : L ⊔ (T : Subgroup G) = ⊤) {m : ℕ} (hm : 0 < m)
    (e : L ≃* commutator (Model m)) :
    ∃ (Ω : Set (Subgroup G)) (M : Subgroup G),
      IsElementaryFamily Ω ∧ M ≠ ⊤ ∧
      normalizer (weakClosure (T : Subgroup G) Ω : Set G) ≤ M ∧
      ∀ A : Subgroup G, A ∈ Ω → A ≤ (T : Subgroup G) →
        ∀ K : Subgroup G, IsEMemberAt (2 * m) (T : Subgroup G) A K → K ≤ M := by
  obtain ⟨a, ha, hfamily, hproper, hnormalizer⟩ := exists_source_family T L hL hgen hm e
  refine ⟨family a, overgroup a, hfamily, hproper, hnormalizer.le, ?_⟩
  intro A hA _ K hK
  exact confined_source_member T a ha (fun _ _ hB hJ => confined_member hm hB hJ) hA hK

end CFSG.Quasithin.ChapterE.ExceptionalValues.ReeFour.LowerObstruction
