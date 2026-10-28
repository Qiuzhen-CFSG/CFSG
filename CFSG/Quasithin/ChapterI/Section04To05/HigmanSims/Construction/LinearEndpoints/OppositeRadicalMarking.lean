module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.PairedEndpointConstruction
public import Theory.GroupTheory.SplitExtensionGivenComplement
public import Theory.ElementaryAbelian.Quotient
public import Theory.SpecificGroups.SL2.Affine.OppositeRadical

/-!
# Actual endpoint coordinates retain the opposite elementary radical

The original symplectic quotient marking forces the literal opposite radical
to have full upper-root image. Given-complement coordinates retain the same
quotient, full kernel coordinates, and actual complement. The affine square
and commutation calculation then identifies the opposite radical exactly,
without assuming a Borel marking or compatibility of endpoint maps.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix SemidirectProduct
namespace CFSG.Quasithin.HigmanSims
open Representation.SL2FourNatural Representation.SL2FourNatural.BorelFactors
variable {G : Type*} [Group G]

/-- The actual source quotient sends the original opposite radical onto U₀. -/
theorem NaturalEndpointData.opposite_quotient_range {A : Subgroup G}
    [IsElementaryAbelian 2 A] (d : NaturalEndpointData A)
    (B : Subgroup G) (hBP : B≤d.carrier) (hBA : B≤normalizer (A : Set G))
    (hR : U0.map d.embedding = ((d.symplectic_quotient.toMonoidHom.comp
      (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range) :
    (d.quotient.comp (inclusion hBP)).range=U0 := by
  apply le_antisymm
  · rintro _ ⟨b,rfl⟩
    apply (mem_map_iff_mem d.embedding_injective).mp
    rw [MonoidHom.comp_apply,d.quotient_marking,hR]
    exact ⟨b,rfl⟩
  · intro x hx
    have hm : d.embedding x∈U0.map d.embedding := mem_map_of_mem _ hx
    rw [hR] at hm
    obtain ⟨b,hb⟩ := hm
    refine ⟨b,d.embedding_injective ?_⟩
    rw [MonoidHom.comp_apply,d.quotient_marking]
    exact hb

/-- Literal affine coordinates, retaining original quotient, all kernel
coordinates, and the given actual complement. -/
theorem NaturalEndpointData.exists_affine_marking {A : Subgroup G}
    [IsElementaryAbelian 2 A] (d : NaturalEndpointData A) :
    ∃ f : d.carrier ≃* Matrix.SL2.Affine F,
      (∀ g, (f g).right=d.quotient g) ∧
      (∀ a : A, f (inclusion d.kernel_le a)=inl (d.coordinates a)) ∧
      (A.subgroupOf d.carrier).map f.toMonoidHom=Matrix.SL2.translations F ∧
      (d.complement.subgroupOf d.carrier).map f.toMonoidHom=
        (inr : SL →* Matrix.SL2.Affine F).range := by
  let k : d.quotient.ker ≃* A :=
    (MulEquiv.subgroupCongr d.quotient_kernel).trans (subgroupOfEquivOfLe d.kernel_le)
  have hk (g : d.carrier) (v : d.quotient.ker) :
      (k.trans d.coordinates) (MulAut.conjNormal g v)=
        Matrix.SL2.naturalAction F (d.quotient g) ((k.trans d.coordinates) v) := by
    have he : k (MulAut.conjNormal g v)=
        A.normalizerMonoidHom (inclusion d.normalizes g) (k v) := Subtype.ext rfl
    change d.coordinates (k (MulAut.conjNormal g v))=_
    rw [he]
    exact d.action g (k v)
  obtain ⟨f,hfq,hfk,_,hfK⟩ := exists_marked_semidirect_equiv_of_given_complement
    d.quotient d.quotient_surjective (k.trans d.coordinates) (Matrix.SL2.naturalAction F)
    hk (d.complement.subgroupOf d.carrier) (d.quotient_kernel ▸ d.is_complement)
  refine ⟨f,hfq,?_,?_,hfK⟩
  · intro a
    let v : d.quotient.ker := ⟨inclusion d.kernel_le a,d.quotient_kernel ▸ a.property⟩
    exact hfk v
  · ext x
    obtain ⟨g,rfl⟩ := f.surjective x
    change f.toMonoidHom g∈(A.subgroupOf d.carrier).map f.toMonoidHom ↔ _
    rw [mem_map_iff_mem (show Function.Injective f.toMonoidHom from f.injective)]
    change (g : G)∈A ↔ (f g).right=1
    rw [hfq,←MonoidHom.mem_ker,d.quotient_kernel]
    rfl

/-- The original opposite elementary sixteen has its exact native affine
position, in the same coordinates as the full original kernel and quotient. -/
theorem NaturalEndpointData.exists_opposite_radical_marking {A : Subgroup G}
    [IsElementaryAbelian 2 A] (d : NaturalEndpointData A)
    (B : Subgroup G) [IsElementaryAbelian 2 B] (hB16 : Nat.card B=16)
    (hBP : B≤d.carrier) (hBA : B≤normalizer (A : Set G))
    (hR : U0.map d.embedding = ((d.symplectic_quotient.toMonoidHom.comp
      (QuotientGroup.mk' (A.subgroupOf (normalizer (A : Set G))))).comp (inclusion hBA)).range) :
    ∃ f : d.carrier ≃* Matrix.SL2.Affine F,
      (∀ g, (f g).right=d.quotient g) ∧
      (∀ a : A, f (inclusion d.kernel_le a)=inl (d.coordinates a)) ∧
      (A.subgroupOf d.carrier).map f.toMonoidHom=Matrix.SL2.translations F ∧
      (B.subgroupOf d.carrier).map f.toMonoidHom=Matrix.SL2.oppositeRoot ∧
      (d.complement.subgroupOf d.carrier).map f.toMonoidHom=
        (inr : SL →* Matrix.SL2.Affine F).range := by
  obtain ⟨f,hfq,hfk,hfA,hfK⟩ := d.exists_affine_marking
  refine ⟨f,hfq,hfk,hfA,?_,hfK⟩
  let C := (B.subgroupOf d.carrier).map f.toMonoidHom
  let eB : B ≃* C := (subgroupOfEquivOfLe hBP).symm.trans
    ((B.subgroupOf d.carrier).equivMapOfInjective f.toMonoidHom f.injective)
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_surjective eB.toMonoidHom eB.surjective
  apply Matrix.SL2.elementary_oppositeRoot_of_image C
  · exact (Nat.card_congr eB.toEquiv).symm.trans hB16
  · change ((B.subgroupOf d.carrier).map f.toMonoidHom).map rightHom=U0
    rw [Subgroup.map_map]
    have he : (rightHom : Matrix.SL2.Affine F →* SL).comp f.toMonoidHom=d.quotient :=
      MonoidHom.ext hfq
    rw [he]
    have hrange : (B.subgroupOf d.carrier).map d.quotient=
        (d.quotient.comp (inclusion hBP)).range := by
      ext x
      constructor
      · rintro ⟨g,hg,rfl⟩
        exact ⟨⟨g,hg⟩,rfl⟩
      · rintro ⟨b,rfl⟩
        exact ⟨inclusion hBP b,b.property,rfl⟩
    rw [hrange]
    exact d.opposite_quotient_range B hBP hBA hR

end CFSG.Quasithin.HigmanSims
