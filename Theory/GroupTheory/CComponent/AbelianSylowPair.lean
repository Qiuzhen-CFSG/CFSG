module
public import Theory.GroupTheory.AbelianSylowSections
public import Theory.GroupTheory.CComponent.RadicalFreeProduct
public import Theory.GroupTheory.CComponent.LayerTransport

/-!
# Abelian Sylows in a pair of C-components

Pass to the solvable-radical quotient, where the two distinct components
are a direct product. Each factor inherits abelian Sylows from its actual
source component. A radical of order prime to p allows this property to
lift back to the original group. No ambient normality of the factors is
assumed beyond their C-component membership.

Source application: Aschbacher--Smith 15.2.15 and 15.2.12(2), pp.1111,1118.
-/

public section
open Subgroup
namespace Theory.GroupTheory.HasAbelianSylow
variable {G : Type*} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- Two distinct C-components with abelian Sylows generate a group with abelian
Sylows when its solvable radical has order prime to the specified prime. -/
theorem of_cComponent_pair {A B : Subgroup G}
    (hA : A.IsCComponent) (hB : B.IsCComponent) (hne : A ≠ B)
    (hgen : A ⊔ B = ⊤)
    (hcop : Nat.Coprime p (Nat.card (solvableRadical G)))
    (ha : HasAbelianSylow p A) (hb : HasAbelianSylow p B) :
    HasAbelianSylow p G := by
  let R := solvableRadical G
  let q := QuotientGroup.mk' R
  let U := A.map q
  let V := B.map q
  have hU : U.IsCComponent := hA.map_quotient R
  have hV : V.IsCComponent := hB.map_quotient R
  have hR : solvableRadical (G ⧸ R) = ⊥ := solvableRadical_quotient_solvableRadical
  have hne' : U ≠ V := fun he => hne (hA.eq_of_map_quotient_eq hB R he)
  have hgen' : U ⊔ V = ⊤ := by
    rw [show U ⊔ V = (A ⊔ B).map q from (Subgroup.map_sup _ _ _).symm,hgen,
      map_top_of_surjective q (QuotientGroup.mk'_surjective R)]
  obtain ⟨e,_⟩ := hU.exists_mulEquiv_prod_sup_of_solvableRadical_eq_bot hR
    (hU.commutator_eq_bot_of_ne_of_solvableRadical_eq_bot hR hV hne')
  let e' : U × V ≃* (G ⧸ R) := e.trans ((MulEquiv.subgroupCongr hgen').trans topEquiv)
  have hu : HasAbelianSylow p U := ha.of_surjective (q.subgroupMap A) (q.subgroupMap_surjective A)
  have hv : HasAbelianSylow p V := hb.of_surjective (q.subgroupMap B) (q.subgroupMap_surjective B)
  have hq : HasAbelianSylow p (G ⧸ R) :=
    (hu.prod hv).of_surjective e'.toMonoidHom e'.surjective
  exact hq.of_coprime_kernel q (by simpa only [q,QuotientGroup.ker_mk'] using hcop)
end Theory.GroupTheory.HasAbelianSylow
