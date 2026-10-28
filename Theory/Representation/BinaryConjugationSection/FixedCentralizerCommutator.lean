module
public import Theory.Representation.QuadraticDuality
public import Theory.Representation.BinaryConjugationSection.CommutatorFixedExtension
public import Theory.Representation.BinaryConjugationSection.ConjugateSpan
public import Theory.Representation.BinaryConjugationSection.InvariantImages
/-!
# Fixed spaces and centralizers under a literal dual pairing

Suppose two binary conjugation sections are identified by a commutator
pairing, and a subgroup B represents the A-fixed space of the first section.
The annihilator of that fixed space is the commutator space of the dual
section. Taking preimages through the original coordinates gives
[P,A] C = C_P(B), where C is the full coordinate kernel. No kernel is erased.

The source application is the equality in Aschbacher–Smith 14.7.20(4),
printed p.1049, with P = O₂(K), C = C_P(U), A = Q and B = V.
-/
public noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace Representation.BinaryConjugationSection
open Representation.BinaryOffender
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z P C : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- The dual commutator modulo its original kernel is the centralizer of the
literal subgroup representing the fixed space of the primal action. -/
theorem commutator_sup_kernel_eq_centralizer_of_dual_pairing
    (sU : BinaryConjugationSection H U Z ρ)
    (sP : BinaryConjugationSection H P C ρ.dual)
    (hpair : ∀ (p : P) (u : U),
      (sP.coordinates p).toAdd (sU.coordinates u).toAdd = 0 ↔ ⁅(p : G),(u : G)⁆ = 1)
    (A B : Subgroup G) (hAH : A ≤ H) (hBU : B ≤ U)
    (hfixed : invariants (ρ.comp (A.subgroupOf H).subtype) = sU.imageSpace B) :
    ⁅P,A⁆ ⊔ C = P ⊓ centralizer (B : Set G) := by
  let : Finite W := Finite.of_surjective (fun u : U => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  have hAP : ⁅P,A⁆ ≤ P := le_normalizer_iff_commutator_le_left.mp (hAH.trans sP.normalized)
  have hcoin : subspaceCommutator ρ.dual ⊤ (A.subgroupOf H) =
      Coinvariants.ker (ρ.dual.comp (A.subgroupOf H).subtype) := by
    unfold subspaceCommutator Coinvariants.ker
    congr 1
    ext v
    constructor
    · rintro ⟨a,ha,w,_,rfl⟩
      exact ⟨(⟨a,ha⟩,w),rfl⟩
    · rintro ⟨⟨a,w⟩,rfl⟩
      exact ⟨a,a.property,w,Submodule.mem_top,rfl⟩
  have him : sP.imageSpace (⁅P,A⁆ ⊔ C) = (sU.imageSpace B).dualAnnihilator := by
    rw [sP.imageSpace_sup_kernel _ hAP,commutator_comm P A,
      sP.imageSpace_commutator A P hAH le_rfl,sP.imageSpace_self,hcoin]
    have hdual : ρ.dual.comp (A.subgroupOf H).subtype =
        Representation.dual (ρ.comp (A.subgroupOf H).subtype) := rfl
    rw [hdual,←dualAnnihilator_invariants,hfixed]
  have hmem (p : P) : (sP.coordinates p).toAdd ∈ (sU.imageSpace B).dualAnnihilator ↔
      (p : G) ∈ centralizer (B : Set G) := by
    rw [Submodule.mem_dualAnnihilator]
    constructor
    · intro hf b hb
      have hz := hf _ ((sU.mem_imageSpace_iff B _).mpr ⟨⟨b,hBU hb⟩,hb,rfl⟩)
      exact (commutatorElement_eq_one_iff_mul_comm.mp ((hpair p ⟨b,hBU hb⟩).mp hz)).symm
    · intro hp v hv
      obtain ⟨u,hu,rfl⟩ := (sU.mem_imageSpace_iff B v).mp hv
      exact (hpair p u).mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hp u hu).symm)
  apply le_antisymm
  · intro p hp
    have hpP : p ∈ P := sup_le hAP sP.kernel_le hp
    refine ⟨hpP,?_⟩
    apply (hmem ⟨p,hpP⟩).mp
    rw [←him]
    exact (sP.mem_imageSpace_iff _ _).mpr ⟨⟨p,hpP⟩,hp,rfl⟩
  · intro p hp
    apply (sP.coordinates_mem_imageSpace_iff_of_kernel_le _ le_sup_right ⟨p,hp.1⟩).mp
    rw [him]
    exact (hmem ⟨p,hp.1⟩).mpr hp.2
end Representation.BinaryConjugationSection
