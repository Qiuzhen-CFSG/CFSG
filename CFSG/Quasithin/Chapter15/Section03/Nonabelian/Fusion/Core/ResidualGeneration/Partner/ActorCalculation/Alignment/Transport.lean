module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.ActorCalculation.Interface
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.FourGroupGeometry


/-!
# Comparing the two quotient coordinate systems

The marked X-action and recognized inner action both transport the same
intersection of nonidentity displacement images. The actual actor quotient,
its projection, and the literal image of V₀ are retained throughout. No
identification of the marked and recognized summands is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(3–5), 15.3.58(3), and 15.3.59, printed pp.1147–1150.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.FourGroupGeometry

variable {G : Type*} [Group G]
variable {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

namespace MarkedAction
variable {V₀ : Subgroup G} {y : G} {hXH : partnerX Z ZS y ≤ centralizerH Z}

theorem actor_equivariant (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (a : actorImage Z (partnerX Z ZS y)) (w : VectorQuotient Z ZS) :
    m.coordinates (faithfulActorAction hkernel a w) =
      modelAction (m.actorEquiv hkernel a) (m.coordinates w) := by
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp
    ((projection_range (hXH := hXH)).symm ▸ a.property :
      (a : ActorQuotient Z) ∈ (projection hXH).range)
  have ha : (⟨projection hXH x,
      projection_range (hXH := hXH) ▸ MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ :
      actorImage Z (partnerX Z ZS y)) = a := Subtype.ext hx
  rw [← ha, actorEquiv_projection]
  apply Multiplicative.toAdd.injective
  exact m.equivariant x w

theorem center_iff_commonDisplacement (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hpoint : modelCenter pointV = pointCenter) (w : VectorQuotient Z ZS) :
    w ∈ vectorImage Z ZS V₀ ↔
      w ∈ commonDisplacement (fun a => faithfulActorAction hkernel a)
        (actorImage Z (partnerX Z ZS y)) := by
  have he := commonDisplacement_subgroupEquiv
    (fun a => faithfulActorAction hkernel a) modelAction
    (m.actorEquiv hkernel) m.coordinates (m.actor_equivariant hkernel) w
  change m.coordinates w ∈ modelCenter pointV ↔ _ at he
  rw [hpoint] at he
  exact (m.center_image w).trans he

theorem actor_square (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (a : ActorQuotient Z) (ha : a ∈ actorImage Z (partnerX Z ZS y)) : a ^ 2 = 1 := by
  have hh : (⟨a, ha⟩ : actorImage Z (partnerX Z ZS y)) ^ 2 = 1 := by
    apply (m.actorEquiv hkernel).injective
    rw [map_pow, map_one]
    apply Subtype.ext
    exact pointV_square _ (m.actorEquiv hkernel ⟨a, ha⟩).property
  exact congrArg Subtype.val hh
end MarkedAction

namespace Alignment

/-- The faithful inner matrices as elements of the actual actor quotient. -/
def innerEmbedding (d : RecognizedAction T Z ZS V t) :
    Matrix.PSL3Two.SL →* ActorQuotient Z :=
  d.actorEquiv.symm.toMonoidHom.comp MulAut.conj

theorem innerEmbedding_injective (d : RecognizedAction T Z ZS V t) :
    Function.Injective (innerEmbedding d) :=
  d.actorEquiv.symm.injective.comp conj_injective

def innerPreimage (d : RecognizedAction T Z ZS V t) (A : Subgroup (ActorQuotient Z)) :
    Subgroup Matrix.PSL3Two.SL := A.comap (innerEmbedding d)

theorem le_innerEmbedding_range (d : RecognizedAction T Z ZS V t)
    (A : Subgroup (ActorQuotient Z))
    (hinner : A.map d.actorEquiv.toMonoidHom ≤ MulAut.innerSubgroup Matrix.PSL3Two.SL) :
    A ≤ (innerEmbedding d).range := by
  intro a ha
  obtain ⟨g, hg⟩ := hinner (mem_map.mpr ⟨a, ha, rfl⟩)
  refine ⟨g, ?_⟩
  change d.actorEquiv.symm (MulAut.conj g) = a
  rw [hg]
  exact d.actorEquiv.symm_apply_apply a

theorem innerPreimage_map (d : RecognizedAction T Z ZS V t)
    (A : Subgroup (ActorQuotient Z))
    (hinner : A.map d.actorEquiv.toMonoidHom ≤ MulAut.innerSubgroup Matrix.PSL3Two.SL) :
    (innerPreimage d A).map (innerEmbedding d) = A :=
  map_comap_eq_self (le_innerEmbedding_range d A hinner)

theorem actor_equivariant (d : RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (g : Matrix.PSL3Two.SL) (w : VectorQuotient Z ZS) :
    d.coordinates (faithfulActorAction hkernel (innerEmbedding d g) w) =
      modelAction g (d.coordinates w) := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective (pCore 2 (centralizerH Z))
    (innerEmbedding d g)
  have he : d.actorEquiv (QuotientGroup.mk' _ h) = MulAut.conj g := by
    rw [hh]
    exact d.actorEquiv.apply_symm_apply _
  rw [← hh]
  apply Multiplicative.toAdd.injective
  exact d.equivariant h g he w

theorem modelCenter_iff (d : RecognizedAction T Z ZS V t)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (A : Subgroup (ActorQuotient Z))
    (hinner : A.map d.actorEquiv.toMonoidHom ≤ MulAut.innerSubgroup Matrix.PSL3Two.SL)
    (w : VectorQuotient Z ZS) :
    d.coordinates w ∈ modelCenter (innerPreimage d A) ↔
      w ∈ commonDisplacement (fun a => faithfulActorAction hkernel a) A :=
  commonDisplacement_comap (fun a => faithfulActorAction hkernel a) modelAction
    (innerEmbedding d) (innerEmbedding_injective d) d.coordinates A
    (le_innerEmbedding_range d A hinner) (actor_equivariant d hkernel) w

theorem innerPreimage_card (d : RecognizedAction T Z ZS V t)
    (A : Subgroup (ActorQuotient Z))
    (hinner : A.map d.actorEquiv.toMonoidHom ≤ MulAut.innerSubgroup Matrix.PSL3Two.SL) :
    Nat.card (innerPreimage d A) = Nat.card A := by
  have hc := Nat.card_congr ((innerPreimage d A).equivMapOfInjective
    (innerEmbedding d) (innerEmbedding_injective d)).toEquiv
  rwa [innerPreimage_map d A hinner] at hc

theorem innerPreimage_square (d : RecognizedAction T Z ZS V t)
    (A : Subgroup (ActorQuotient Z)) (hsq : ∀ a ∈ A, a ^ 2 = 1) :
    ∀ g ∈ innerPreimage d A, g ^ 2 = 1 := by
  intro g hg
  apply innerEmbedding_injective d
  rw [map_pow, map_one]
  exact hsq _ hg

end Alignment
end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
