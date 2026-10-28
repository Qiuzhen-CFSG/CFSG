module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.ActorCalculation.Interface
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner.ActorCalculation.Alignment.Transport

public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.FourGroupCoverage
public import Theory.Representation.PSL3Two.FourGroupGeometry.Normalizers.PointModel
public import Theory.SpecificGroups.PSL3Two.Parabolics.MarkedAutomorphisms.FourGroupGeometry.DisplacementCenters


/-!
# Simultaneous placement from intrinsic displacement geometry

The literal quotient normalizer stabilizes the marked line. Recovering this
line as the common displacement intersection identifies that stabilizer with
the normalizer of the actual inner four-group: conjugation preserves the
intersection, and uniqueness of the model intersection gives the converse.
The checked four-group coverage then supplies one automorphism that transports
both the group and its normalizer to the point radical and point parabolic.

The transport lemmas retain explicit finite-model displacement premises. The
final `parabolicAlignment_of_inner` discharges them using the point-center
calculation and uniqueness theorem in `DisplacementCenters`. Only the placement
of the actual actor image in the inner automorphisms remains an explicit input;
no normalization of the source subgroup X is assumed.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.56(3–5), 15.3.58(3), and 15.3.59, printed pp.1147–1150.
-/

public section

open Subgroup
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
open Matrix.PSL3Two.MarkedAutomorphisms
open Matrix.PSL3Two.MarkedAutomorphisms.FourGroupGeometry
open Alignment

variable {G : Type*} [Group G]
variable {T Z ZS V : Subgroup G} {t : G}
variable [(Z.subgroupOf (closureU Z ZS)).Normal]

theorem markedNormalizer_eq_actorNormalizer_of_modelCenter
    (d : RecognizedAction T Z ZS V t)
    {V₀ : Subgroup G} {y : G} {hXH : partnerX Z ZS y ≤ centralizerH Z}
    (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZV : Z ≤ V₀) (hVU : V₀ ≤ closureU Z ZS)
    (hinner : (actorImage Z (partnerX Z ZS y)).map d.actorEquiv.toMonoidHom ≤
      MulAut.innerSubgroup Matrix.PSL3Two.SL)
    (hpoint : modelCenter pointV = pointCenter)
    (hunique : ∀ E F : Subgroup Matrix.PSL3Two.SL,
      (∀ g ∈ E, g ^ 2 = 1) → Nat.card E = 4 →
      (∀ g ∈ F, g ^ 2 = 1) → Nat.card F = 4 →
      modelCenter E = modelCenter F → E = F) :
    actorImage Z (markedNormalizer Z V₀) =
      normalizer (actorImage Z (partnerX Z ZS y) : Set (ActorQuotient Z)) := by
  let A := actorImage Z (partnerX Z ZS y)
  let ρ := faithfulActorAction hkernel
  ext a
  rw [mem_actorImage_markedNormalizer_iff hkernel V₀ hZV hVU]
  constructor
  · intro ha
    let F := A.map (MulAut.conj a).toMonoidHom
    have hinnerF : F.map d.actorEquiv.toMonoidHom ≤
        MulAut.innerSubgroup Matrix.PSL3Two.SL := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      change d.actorEquiv (a * x * a⁻¹) ∈ MulAut.innerSubgroup Matrix.PSL3Two.SL
      rw [map_mul, map_mul, map_inv]
      exact (inferInstance : (MulAut.innerSubgroup Matrix.PSL3Two.SL).Normal).conj_mem
        _ (hinner ⟨x, hx, rfl⟩) _
    have hsqF : ∀ f ∈ F, f ^ 2 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      change (MulAut.conj a x) ^ 2 = 1
      rw [← map_pow, m.actor_square hkernel x hx, map_one]
    have hcF : Nat.card F = 4 :=
      (Nat.card_congr ((MulAut.conj a).subgroupMap A).toEquiv).symm.trans
        (m.actor_card hkernel)
    have hcenter : commonDisplacement (fun b => ρ b) F =
        commonDisplacement (fun b => ρ b) A := by
      ext w
      obtain ⟨v, rfl⟩ := (ρ a).surjective w
      change ρ a v ∈ commonDisplacement (fun b => ρ b)
          (A.map (MulAut.conj a).toMonoidHom) ↔ _
      rw [commonDisplacement_conj]
      rw [← m.center_iff_commonDisplacement hkernel hpoint,
        ← m.center_iff_commonDisplacement hkernel hpoint]
      exact (ha v).symm
    have hmodel : modelCenter (innerPreimage d F) = modelCenter (innerPreimage d A) := by
      ext w
      obtain ⟨v, rfl⟩ := d.coordinates.surjective w
      rw [modelCenter_iff d hkernel F hinnerF, modelCenter_iff d hkernel A hinner]
      exact Set.ext_iff.mp hcenter v
    have he := hunique (innerPreimage d F) (innerPreimage d A)
      (innerPreimage_square d F hsqF) ((innerPreimage_card d F hinnerF).trans hcF)
      (innerPreimage_square d A (m.actor_square hkernel))
      ((innerPreimage_card d A hinner).trans (m.actor_card hkernel)) hmodel
    have hFA : F = A := by
      have hh := congrArg (fun E => E.map (innerEmbedding d)) he
      simpa only [innerPreimage_map d F hinnerF, innerPreimage_map d A hinner] using hh
    exact mem_normalizer_iff_map_conj_eq.mpr hFA
  · intro ha w
    rw [m.center_iff_commonDisplacement hkernel hpoint,
      m.center_iff_commonDisplacement hkernel hpoint]
    exact commonDisplacement_normalizer ρ A ha w

namespace Alignment

private theorem elementary_of_square (E : Subgroup Matrix.PSL3Two.SL)
    (hsq : ∀ g ∈ E, g ^ 2 = 1) : IsElementaryAbelian 2 E := by
  have hi (x : E) : x⁻¹ = x := by
    apply inv_eq_of_mul_eq_one_left
    apply Subtype.ext
    simpa only [coe_mul, coe_one, pow_two] using hsq x x.property
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · intro a b
    calc
      a * b = (a * b)⁻¹ := (hi _).symm
      _ = b * a := by rw [mul_inv_rev, hi, hi]
  · apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
    intro x
    exact Subtype.ext (hsq x x.property)

theorem actor_map_point (d : RecognizedAction T Z ZS V t)
    (A : Subgroup (ActorQuotient Z))
    (hinner : A.map d.actorEquiv.toMonoidHom ≤ MulAut.innerSubgroup Matrix.PSL3Two.SL)
    (hsq : ∀ a ∈ A, a ^ 2 = 1) (hc : Nat.card A = 4) :
    ∃ α : MulAut Matrix.PSL3Two.SL,
      A.map (actorRelabel d α).toMonoidHom = pointV.map MulAut.conj := by
  let E := innerPreimage d A
  let : IsElementaryAbelian 2 E := elementary_of_square E (innerPreimage_square d A hsq)
  obtain ⟨α, hα⟩ := BinaryLinearThree.FourGroupGeometry.Normalizers.fourGroup_map_point E
    ((innerPreimage_card d A hinner).trans hc)
  refine ⟨α, ?_⟩
  have hcomp : (actorRelabel d α).toMonoidHom.comp (innerEmbedding d) =
      MulAut.conj.comp α.toMonoidHom := by
    ext g : 1
    change (MulAut.congr α) (d.actorEquiv (d.actorEquiv.symm (MulAut.conj g))) =
      MulAut.conj (α g)
    rw [MulEquiv.apply_symm_apply, MulAut.congr_conj]
  rw [← innerPreimage_map d A hinner, map_map, hcomp, ← map_map, hα]

end Alignment

/-- Two concrete displacement calculations suffice to align the actual actor
and its full marked normalizer. `parabolicAlignment_of_inner` supplies both
finite-model premises. -/
theorem parabolicAlignment_of_modelCenter
    (d : RecognizedAction T Z ZS V t)
    {V₀ : Subgroup G} {y : G} {hXH : partnerX Z ZS y ≤ centralizerH Z}
    (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZV : Z ≤ V₀) (hVU : V₀ ≤ closureU Z ZS)
    (hinner : (actorImage Z (partnerX Z ZS y)).map d.actorEquiv.toMonoidHom ≤
      MulAut.innerSubgroup Matrix.PSL3Two.SL)
    (hpoint : modelCenter pointV = pointCenter)
    (hunique : ∀ E F : Subgroup Matrix.PSL3Two.SL,
      (∀ g ∈ E, g ^ 2 = 1) → Nat.card E = 4 →
      (∀ g ∈ F, g ^ 2 = 1) → Nat.card F = 4 →
      modelCenter E = modelCenter F → E = F) :
    ParabolicAlignment d V₀ y := by
  obtain ⟨α, hα⟩ := actor_map_point d (actorImage Z (partnerX Z ZS y)) hinner
    (m.actor_square hkernel) (m.actor_card hkernel)
  refine ⟨α, hα, ?_⟩
  rw [markedNormalizer_eq_actorNormalizer_of_modelCenter d m hkernel hZV hVU hinner
    hpoint hunique, map_equiv_normalizer_eq, hα]
  exact BinaryLinearThree.FourGroupGeometry.Normalizers.point_normalizer

/-- An inner marked four-group and its full marked normalizer are simultaneously
carried to the point radical and point parabolic by one automorphism of SL₃(2).
The displacement-center premises are discharged by concrete model theorems;
the source assembly remains responsible for the explicit inner-image input. -/
theorem parabolicAlignment_of_inner
    (d : RecognizedAction T Z ZS V t)
    {V₀ : Subgroup G} {y : G} {hXH : partnerX Z ZS y ≤ centralizerH Z}
    (m : MarkedAction Z ZS V₀ y t hXH)
    (hkernel : (quotientAction Z ZS).ker = pCore 2 (centralizerH Z))
    (hZV : Z ≤ V₀) (hVU : V₀ ≤ closureU Z ZS)
    (hinner : (actorImage Z (partnerX Z ZS y)).map d.actorEquiv.toMonoidHom ≤
      MulAut.innerSubgroup Matrix.PSL3Two.SL) :
    ParabolicAlignment d V₀ y :=
  parabolicAlignment_of_modelCenter d m hkernel hZV hVU hinner
    modelCenter_pointV modelCenter_injective_four

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Core.ResidualGeneration.Partner
