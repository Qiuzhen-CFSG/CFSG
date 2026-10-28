module

public import Theory.ElementaryAbelian.BinaryQuotientRank
public import Theory.Representation.BinaryOffender.SmallRank

/-!
# Rank comparisons after quotienting by the source line

A linear map with kernel contained in D induces an actual linear equivalence
I/(I ∩ D) ≃ f(I)/(f(I) ∩ f(D)). Consequently the ranks are unchanged when
passing modulo the source line V₁, provided V₁ ≤ D. The parallel subgroup
statement uses relative indices, so does not impose ambient normality on D.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
manuscript of 1 March 2004, 13.8.25, printed pp.961–962. These transport lemmas
retain the denominator containment as an explicit source obligation.
-/

public section

open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure

variable {U V : Type*} [AddCommGroup U] [Module (ZMod 2) U]
  [AddCommGroup V] [Module (ZMod 2) V]

noncomputable def imageSectionEquiv (f : U →ₗ[ZMod 2] V)
    (I D : Submodule (ZMod 2) U) (hker : LinearMap.ker f ≤ D) :
    (I ⧸ D.comap I.subtype) ≃ₗ[ZMod 2]
      (I.map f ⧸ (D.map f).comap (I.map f).subtype) := by
  let fI : I →ₗ[ZMod 2] I.map f :=
    (f.domRestrict I).codRestrict (I.map f) (fun x => ⟨x, x.property, rfl⟩)
  let q := ((D.map f).comap (I.map f).subtype).mkQ.comp fI
  have hsurj : Function.Surjective q := by
    intro v
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective ((D.map f).comap (I.map f).subtype) v
    obtain ⟨u, hu, he⟩ := v.property
    refine ⟨⟨u, hu⟩, ?_⟩
    change ((D.map f).comap (I.map f).subtype).mkQ (fI ⟨u, hu⟩) = _
    congr 1
    exact Subtype.ext he
  have hqker : LinearMap.ker q = D.comap I.subtype := by
    ext u
    change q u = 0 ↔ (u : U) ∈ D
    change ((D.map f).comap (I.map f).subtype).mkQ (fI u) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    change f u ∈ D.map f ↔ (u : U) ∈ D
    constructor
    · rintro ⟨d, hd, he⟩
      have hz : (u : U) - d ∈ LinearMap.ker f := by
        change f ((u : U) - d) = 0
        rw [map_sub, he, sub_self]
      have hm := D.add_mem (hker hz) hd
      simpa using hm
    · intro hu
      exact ⟨u, hu, rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hqker.symm).trans
    (q.quotKerEquivOfSurjective hsurj)

theorem section_finrank_eq_image [FiniteDimensional (ZMod 2) U]
    (f : U →ₗ[ZMod 2] V) (I D : Submodule (ZMod 2) U)
    (hker : LinearMap.ker f ≤ D) :
    Module.finrank (ZMod 2) (I ⧸ D.comap I.subtype) =
      Module.finrank (ZMod 2) (I.map f ⧸ (D.map f).comap (I.map f).subtype) :=
  (imageSectionEquiv f I D hker).finrank_eq

theorem section_finrank_eq_mod_central [FiniteDimensional (ZMod 2) U]
    (Z I D : Submodule (ZMod 2) U) (hZD : Z ≤ D) :
    Module.finrank (ZMod 2) (I ⧸ D.comap I.subtype) =
      Module.finrank (ZMod 2)
        (I.map Z.mkQ ⧸ (D.map Z.mkQ).comap (I.map Z.mkQ).subtype) := by
  apply section_finrank_eq_image
  simpa only [Submodule.ker_mkQ] using hZD

/-- Passing a subgroup section through a homomorphism preserves its index when
its kernel is already in the denominator. No normality of that denominator
in the ambient group is required. -/
theorem relIndex_image_of_kernel_le {G J : Type*} [Group G] [Group J]
    (f : G →* J) (I D : Subgroup G) (hker : f.ker ≤ D) :
    (D.map f).relIndex (I.map f) = D.relIndex I := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq, sup_eq_left.mpr hker]

/-- Rank of the actual subgroup section agrees with that of its image modulo
the specified normal subgroup; the latter must lie in the denominator. -/
theorem section_rank_eq_mod_normal {G : Type*} [Group G]
    (Z I D : Subgroup G) [Z.Normal] (hZD : Z ≤ D) :
    Nat.log 2 (D.relIndex I) =
      Nat.log 2 ((D.map (QuotientGroup.mk' Z)).relIndex (I.map (QuotientGroup.mk' Z))) := by
  congr 1
  symm
  apply relIndex_image_of_kernel_le
  simpa only [QuotientGroup.ker_mk'] using hZD

/-- The relative subgroup rank is the vector-space dimension of the image
section whenever that image is elementary abelian. This applies directly to
images modulo V₁, without pretending that quotienting always preserves rank. -/
theorem section_rank_eq_image_finrank {G J : Type*} [Group G] [Group J] [Finite J]
    (f : G →* J) (I D : Subgroup G) [IsElementaryAbelian 2 (I.map f)]
    (hker : f.ker ≤ D) :
    Nat.log 2 (D.relIndex I) = Module.finrank (ZMod 2)
      (Additive (I.map f ⧸ (D.map f).subgroupOf (I.map f))) := by
  rw [← relIndex_image_of_kernel_le f I D hker]
  exact Subgroup.log_relIndex_eq_quotient_finrank (I.map f) (D.map f)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure
