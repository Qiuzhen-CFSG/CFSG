module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.NaturalCentrality
public import CFSG.Quasithin.ChapterC.Section05.BlockAnalysis.NaturalBorelPlacement

/-!
# Central involutions in the natural residual block orbit

A natural block supplies a nontrivial odd actor in the unique maximal
Sylow overgroup. An involution centralizing that overgroup therefore fixes
the block, by the odd-orbit argument in the center of the ambient two-core.
Transitivity of the original Sylow orbit gives fixation of every block;
residual-Sylow generation makes the involution central in the whole group.
All placements concern the original block orbit and marked maximal subgroup.

Source: Aschbacher--Smith14.6.9, natural-block exclusion, printed p.1025.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
variable {A : Type*} [Group A] [Finite A]

/-- The actual unique maximal Sylow overgroup detects central involutions
when the transitive residual orbit contains a natural block. -/
theorem OrbitDecomposition.natural_central_involution
    (S : Sylow 2 A) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (hf : generalizedFitting A = pCore 2 A)
    {R : Subgroup A} (b : OrbitDecomposition (S : Subgroup A) R (pResidual 2 A))
    (i : Fin b.size) {n : ℕ} (hnat : IsL2EvenBlock (b.block i) n)
    (z : A) (hz2 : z^2=1)
    (hzB : z ∈ centralizer (ChapterB.minimalParabolicMax S hP : Set A)) :
    z ∈ center A := by
  have hzS : z ∈ centralizer (S : Set A) :=
    centralizer_le (ChapterB.minimalParabolicMax_spec S hP).2 hzB
  obtain ⟨D,hDK,hDB,hodd,hD⟩ := b.exists_natural_odd_actor S hP i hnat
  have hzK := hnat.centralizes_of_sylow_and_odd_fixed S hf (b.block i) (b.type i).1
    D hDK hodd hD z hz2 hzS (centralizer_le hDB hzB)
  have hzc (j : Fin b.size) : b.block j ≤ centralizer ({z} : Set A) := by
    obtain ⟨s,hs,he⟩ := b.transitive i j
    rw [he]
    rintro x ⟨k,hk,rfl⟩
    apply mem_centralizer_singleton_iff.mpr
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply,inv_inv]
    have hsZ := hzS s hs
    have hkZ := hzK k hk
    have hsiZ := hzS s⁻¹ ((S : Subgroup A).inv_mem hs)
    calc
      s⁻¹*k*s*z = s⁻¹*k*(s*z) := by group
      _ = s⁻¹*k*(z*s) := by rw [hsZ]
      _ = s⁻¹*(k*z)*s := by group
      _ = s⁻¹*(z*k)*s := by rw [hkZ]
      _ = (s⁻¹*z)*k*s := by group
      _ = (z*s⁻¹)*k*s := by rw [hsiZ]
      _ = z*(s⁻¹*k*s) := by group
  have hres : pResidual 2 A ≤ centralizer ({z} : Set A) := by
    rw [←b.generate]
    exact iSup_le hzc
  have hs : (S : Subgroup A) ≤ centralizer ({z} : Set A) := by
    intro s hs
    exact mem_centralizer_singleton_iff.mpr (hzS s hs)
  have ht : (⊤ : Subgroup A) ≤ centralizer ({z} : Set A) := by
    rw [←pResidual_sup_sylow_eq_top S]
    exact sup_le hres hs
  exact mem_center_iff.mpr (fun a => mem_centralizer_singleton_iff.mp (ht (mem_top a)))

end CFSG.Quasithin.ChapterC.Section05.BlockAnalysis
