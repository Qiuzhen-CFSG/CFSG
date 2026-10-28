module
public import Theory.Representation.BinaryConjugationSection
public import Theory.GroupTheory.Commutator.Basic

/-!
# Detecting the actor kernel from trivial action on a section

An ambient normalizer which acts trivially on a marked group section
centralizes the section's faithful actor modulo its original kernel. This
retains both the subgroup coordinates and the original actor homomorphism.
The proof compares conjugation before and after the coordinate map.

Source application: DGS, *Groups and Graphs* (1985), 9.10(4), p.148.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G J W : Type*} [Group G] [Group J] [AddCommGroup W] [Module (ZMod 2) W]

/-- An ambient normalizer acting trivially on a faithful marked section
centralizes its original actor modulo the actor kernel. -/
theorem commutator_le_actor_kernel_of_displacement
    (H A Z P : Subgroup G) (q : H →* J)
    (ρ : Representation (ZMod 2) J W) (hf : Function.Injective ρ)
    (c : BinaryConjugationSection H A Z (ρ.comp q))
    (hnH : P ≤ normalizer (H : Set G)) (hnA : P ≤ normalizer (A : Set G))
    (hm : ⁅P,A⁆ ≤ Z) : ⁅P,H⁆ ≤ q.ker.map H.subtype := by
  have hc (p : P) (a : A) :
      c.coordinates ⟨(p:G)*a*(p:G)⁻¹,
        (mem_normalizer_iff.mp (hnA p.property) a).mp a.property⟩ = c.coordinates a := by
    let z : A := ⟨(p:G)*a*(p:G)⁻¹,
      (mem_normalizer_iff.mp (hnA p.property) a).mp a.property⟩
    have hz : c.coordinates (z*a⁻¹) = 1 :=
      (c.coordinates_eq_one_iff _).mpr (hm (commutator_mem_commutator p.property a.property))
    rw [map_mul,map_inv,mul_inv_eq_one] at hz
    exact hz
  apply commutator_le.mpr
  intro p hp h hh
  let hH : H := ⟨h,hh⟩
  let pP : P := ⟨p,hp⟩
  let k : H := ⟨p*h*p⁻¹,(mem_normalizer_iff.mp (hnH hp) h).mp hh⟩
  have he : q k = q hH := by
    apply hf
    apply LinearMap.ext
    intro v
    obtain ⟨a,rfl⟩ := c.onto (Multiplicative.ofAdd v)
    let b : A := ⟨p⁻¹*a*(p⁻¹)⁻¹,
      (mem_normalizer_iff.mp (hnA (P.inv_mem hp)) a).mp a.property⟩
    let d : A := ⟨h*b*h⁻¹,(mem_normalizer_iff.mp (c.normalized hh) b).mp b.property⟩
    have ha : c.coordinates b = c.coordinates a := hc pP⁻¹ a
    have hpd := hc pP d
    have hkey :
        (⟨p*d*p⁻¹,(mem_normalizer_iff.mp (hnA hp) d).mp d.property⟩ : A) =
        ⟨(k:G)*a*(k:G)⁻¹,(mem_normalizer_iff.mp (c.normalized k.property) a).mp a.property⟩ := by
      apply Subtype.ext
      change p*(h*(p⁻¹*a*(p⁻¹)⁻¹)*h⁻¹)*p⁻¹ = (p*h*p⁻¹)*a*(p*h*p⁻¹)⁻¹
      group
    have heq := congrArg Multiplicative.toAdd hpd
    rw [hkey,c.equivariant k a] at heq
    change ρ (q k) (c.coordinates a).toAdd = (c.coordinates d).toAdd at heq
    rw [c.equivariant hH b,ha] at heq
    exact heq
  have hk : k*hH⁻¹ ∈ q.ker := by
    change q (k*hH⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  exact ⟨k*hH⁻¹,hk,rfl⟩
end Representation.BinaryConjugationSection
