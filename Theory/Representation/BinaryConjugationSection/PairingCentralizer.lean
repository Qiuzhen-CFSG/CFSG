module

public import Theory.Representation.BinaryConjugationSection.CentralDuality
public import Theory.Representation.BinaryConjugationSection.QuadraticPair
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.FieldTheory.Finiteness

/-!
# Centralizer indices from the actual binary commutator pairing

A perfect pairing between two literal conjugation sections identifies the
second with the dual of the first. Restricting its functionals to the image
of any subgroup computes the index of that subgroup's actual centralizer.
A subgroup supplementing the coordinate kernel has the same quotient
section, with the coordinate map obtained by the original inclusion.

These two transports retain the functional kernels and the original group
maps in the core duality of Aschbacher–Smith 14.7.20(1),(4), printed p.1049,
using the central commutator pairing of F.9.7, printed p.321.
-/

public noncomputable section
open Subgroup Representation
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [Finite G]
  [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z Q C : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- Restricting the actual commutator functionals to a subgroup image computes its centralizer index. -/
theorem centralizer_index_of_dual_pairing
    (sU : BinaryConjugationSection H U Z ρ)
    (sQ : BinaryConjugationSection H Q C ρ.dual)
    (hpair : ∀ (q : Q) (u : U),
      (sQ.coordinates q).toAdd (sU.coordinates u).toAdd = 0 ↔ ⁅(q : G),(u : G)⁆ = 1)
    (B : Subgroup G) (hBU : B ≤ U) :
    (centralizer (B : Set G)).relIndex Q = Nat.card (sU.imageSpace B) := by
  let : Finite W := Finite.of_surjective (fun u : U => (sU.coordinates u).toAdd)
    (Multiplicative.toAdd.surjective.comp sU.onto)
  let S := sU.imageSpace B
  let f : Q →* Multiplicative (Module.Dual (ZMod 2) S) :=
    (AddMonoidHom.toMultiplicative S.dualRestrict.toAddMonoidHom).comp sQ.coordinates
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨v,hv⟩ := Subspace.dualRestrict_surjective (W := S) w.toAdd
    obtain ⟨q,hq⟩ := sQ.onto (Multiplicative.ofAdd v)
    refine ⟨q,?_⟩
    apply Multiplicative.toAdd.injective
    change S.dualRestrict (sQ.coordinates q).toAdd = w.toAdd
    rw [hq]
    exact hv
  have hk : f.ker = (centralizer (B : Set G)).subgroupOf Q := by
    ext q
    change S.dualRestrict (sQ.coordinates q).toAdd = 0 ↔ (q : G) ∈ centralizer (B : Set G)
    constructor
    · intro he b hb
      let u : U := ⟨b,hBU hb⟩
      have hw : (sU.coordinates u).toAdd ∈ S :=
        (sU.mem_imageSpace_iff B _).mpr ⟨u,hb,rfl⟩
      have hz := LinearMap.congr_fun he ⟨(sU.coordinates u).toAdd,hw⟩
      have hc := (hpair q u).mp hz
      exact (commutatorElement_eq_one_iff_mul_comm.mp hc).symm
    · intro hc
      ext w
      obtain ⟨u,hu,he⟩ := (sU.mem_imageSpace_iff B w.val).mp w.property
      change (sQ.coordinates q).toAdd w.val = 0
      rw [←he]
      exact (hpair q u).mpr (commutatorElement_eq_one_iff_mul_comm.mpr (hc u hu).symm)
  change ((centralizer (B : Set G)).subgroupOf Q).index = _
  rw [←hk,index_ker,f.range_eq_top_of_surjective hf,card_top]
  change Nat.card (Module.Dual (ZMod 2) S) = Nat.card S
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) S),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := S),Subspace.dual_finrank_eq]

end Representation.BinaryConjugationSection

public noncomputable section
open Subgroup Representation
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H Q C : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- A subgroup supplementing the actual coordinate kernel has the same section and coordinates. -/
theorem restrict_of_sup_kernel
    (s : BinaryConjugationSection H Q C ρ)
    (P : Subgroup G) (hPQ : P ≤ Q) (hP : H ≤ normalizer (P : Set G))
    (hsup : P ⊔ C = Q) :
    ∃ t : BinaryConjugationSection H P (P ⊓ C) ρ,
      ∀ p : P, t.coordinates p = s.coordinates (inclusion hPQ p) := by
  let f := s.coordinates.comp (inclusion hPQ)
  have hf : Function.Surjective f := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp,inclusion_range]
    have hm := congrArg (fun A : Subgroup G => (A.subgroupOf Q).map s.coordinates) hsup
    have hk : s.coordinates.ker.map s.coordinates = ⊥ := (Subgroup.map_eq_bot_iff _).mpr le_rfl
    rw [subgroupOf_sup hPQ s.kernel_le,Subgroup.map_sup,subgroupOf_self,
      map_top_of_surjective _ s.onto,←s.kernel_eq,hk,sup_bot_eq] at hm
    exact hm
  refine ⟨{ section_le := hPQ.trans s.section_le
            kernel_le := inf_le_left
            normalized := hP
            coordinates := f
            onto := hf
            kernel_eq := ?_
            equivariant := ?_ },fun _ => rfl⟩
  · ext p
    change s.coordinates (inclusion hPQ p) = 1 ↔ _
    rw [s.coordinates_eq_one_iff]
    exact ⟨fun hp => ⟨p.property,hp⟩,fun hp => hp.2⟩
  · intro h p
    exact s.equivariant h (inclusion hPQ p)
end Representation.BinaryConjugationSection