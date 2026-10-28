module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.LocalAnalysisSylowReduction
public import Theory.GroupTheory.NormalCentralQuotientAction.SolvableKernel
public import Theory.GroupTheory.PCoreRestriction
public import Theory.SpecificGroups.Alternating.SixFiveImage

/-!
# Transporting the literal A₅ residual into the A₆ quotient

Given the two local quotient identifications, perfectness of the weight-two
residual puts it in O^{3′}(C_G(e₂)). After a conjugate is contained in the
weight-six residual, the kernel of its O₂,Z projection is solvable. The
perfect A₅ two-extension image theorem identifies its actual image with A₅.
The conditional constructor applies these proofs to `Points.Models`, and
the final theorem feeds the actual `no_transport` consumer.

The local quotient identifications and the common two-core are still source
obligations. Only the easy inclusion of the latter is established here.
In particular, this module does not prove `Nonempty P.Models` from `Setup`.

Source: Aschbacher--Smith, 3.3.22, printed pp.597--598, used in 12.3.5.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
open Section02
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {L V : Subgroup G} {S : Setup T L V}
variable {E : S.NaturalCoordinates}
namespace SylowNormalizer
/-- A finite terminal derived subgroup stays perfect in its ambient embedding. -/
instance pointResidual_isPerfect (L : Subgroup G) (x : G) :
    Group.IsPerfect (pointResidual L x) := Group.IsPerfect.map _

omit [Finite G] in
/-- The residual retains its original component and point-centralizer containment. -/
lemma pointResidual_le (L : Subgroup G) (x : G) :
    pointResidual L x ≤ L ⊓ centralizer ({x} : Set G) := map_subtype_le _

namespace Points
variable (P : Points E)
/-- Sylow containment supplies the easy inclusion in the common-core identity. -/
lemma core_le_six_core : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
    (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 := by
  have hR : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hH : P.sixGroup ⊔ (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) :=
    sup_le_sup ((pointResidual_le L (P.six : G)).trans inf_le_left) le_rfl
  exact (le_inf (hR.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hH)

/-- The marked A₅ residual lies in the actual ambient O^{3′}-centralizer. -/
lemma five_le_three_of_quotient
    (e5 : (P.five ⧸ pCore 2 P.five) ≃* alternatingGroup (Fin 5)) :
    P.five ≤ pointThreeResidual (P.two : G) := by
  have h := embedded_primeToResidual_mono 3
    ((pointResidual_le L (P.two : G)).trans inf_le_right)
  rw [Theory.SpecificGroups.Alternating.SixFiveImage.primeToThreeResidual_eq_top e5,
    ← MonoidHom.range_eq_map, range_subtype] at h
  exact h

/-- Every contained conjugate has an actual A₅ image under the specified
O₂,Z projection. The possible central cover in the target is retained. -/
lemma five_image_of_quotients
    (e5 : (P.five ⧸ pCore 2 P.five) ≃* alternatingGroup (Fin 5))
    (e6 : CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6))
    (g : G) (hA : P.five.map (MulAut.conj g).toMonoidHom ≤ P.sixGroup) :
    Nonempty (((P.five.map (MulAut.conj g).toMonoidHom).subgroupOf P.sixGroup).map
      (projection P.sixGroup e6) ≃* alternatingGroup (Fin 5)) := by
  let A := (P.five.map (MulAut.conj g).toMonoidHom).subgroupOf P.sixGroup
  let d : A ≃* P.five := (subgroupOfEquivOfLe hA).trans
    (P.five.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).symm
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := d.symm.toMonoidHom) d.symm.surjective
  let eA : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ d (pCore_map_iso 2 d)).trans e5
  let q := projection P.sixGroup e6
  let f := q.subgroupMap A
  let C := centralPreimage (pCore 2 P.sixGroup)
  let : Group.IsSolvable C := centralPreimage_pCore_isSolvable 2
  let i : f.ker →* C := {
    toFun := fun x => ⟨x.val.val, by
      apply (QuotientGroup.eq_one_iff _).mp
      apply e6.injective
      exact (congrArg Subtype.val x.property).trans (map_one e6).symm⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  have hi : Function.Injective i := by
    intro x y h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : C => (z : P.sixGroup)) h
  let : Group.IsSolvable f.ker := Group.isSolvable_of_isSolvable_injective hi
  exact ⟨Theory.SpecificGroups.Alternating.SixFiveImage.imageEquiv q A eA⟩

/-- Conditional local assembly: the point-quotient recognition and common core
remain genuine source obligations. The other two fields are proved here. -/
def models_of_quotients
    (e5 : (P.five ⧸ pCore 2 P.five) ≃* alternatingGroup (Fin 5))
    (e6 : CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6))
    (hcore : (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 =
      (L ⊔ (T : Subgroup G)).pCoreIn 2) : P.Models where
  six_quotient := e6
  core_eq := hcore
  five_le_three := P.five_le_three_of_quotient e5
  five_image g _ _ hA := P.five_image_of_quotients e5 e6 g hA

/-- Application to the literal source obstruction, with local recognition,
the common two-core and independent ambient residual identities explicit. -/
lemma no_transport_of_quotients
    (e5 : (P.five ⧸ pCore 2 P.five) ≃* alternatingGroup (Fin 5))
    (e6 : CentralQuotient P.sixGroup ≃* alternatingGroup (Fin 6))
    (hcore : (P.sixGroup ⊔ (T : Subgroup G)).pCoreIn 2 =
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (R : P.AmbientResiduals) {g : G} (hg : g ∈ normalizer (T : Set G)) :
    g * (P.two : G) * g⁻¹ ≠ P.six :=
  no_transport (P.models_of_quotients e5 e6 hcore) R S.chosen.sylow_normalizes_component hg
end Points
end SylowNormalizer
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven
