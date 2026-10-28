module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import Theory.SpecificGroups.SymmetricSix.PolarAffine.QuadraticAutomorphism

/-!
# A genuine quadratic adjustment on the original hexad group

The actual hexad quotient and original binary kernel marking construct an
involutory automorphism of that same hexad group. It fixes the whole original
kernel pointwise and every quotient value, and its displacement is the
explicit nonprincipal quadratic cocycle. Thus it supplies an adjustment
beyond kernel conjugation without assuming an endpoint cocycle extends.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule

/-- The original hexad group has a concrete non-inner quadratic adjustment,
with the same six-letter quotient and every original kernel coordinate. -/
theorem NaturalEndpointData.hexad_quadratic_adjustment (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier≤L) (e : L≃*Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom=Point) :
    ∃ hDN : d.hexad_overgroup≤normalizer (A:Set G),
      ∃ q : d.hexad_overgroup→*A6, Function.Surjective q ∧
        ∃ hqker : q.ker=A.subgroupOf d.hexad_overgroup,
        (∀ g : d.hexad_overgroup, (q g:Equiv.Perm (Fin 6))=
          d.six_letter_quotient (inclusion hDN g)) ∧
        ∃ k : q.ker≃*Multiplicative Vec,
          (∀ a : q.ker, (k a).toAdd=d.binary_coordinates
            (Additive.ofMul ⟨((a:d.hexad_overgroup):G), by
              exact (show (a:d.hexad_overgroup)∈A.subgroupOf d.hexad_overgroup
                from hqker ▸ a.property)⟩)) ∧
          (∀ (g : d.hexad_overgroup) (a : q.ker),
            k (MulAut.conjNormal g a)=Multiplicative.ofAdd
              (Theory.SpecificGroups.SymmetricSix.polarAction (q g).val (k a).toAdd)) ∧
          ∃ α : MulAut d.hexad_overgroup,
            (∀ g, q (α g)=q g) ∧
            (∀ a : q.ker, α a=(a:d.hexad_overgroup)) ∧
            (∀ g, α g=(k.symm (Multiplicative.ofAdd
              (Theory.SpecificGroups.SymmetricSix.PolarAffine.quadratic (q g))) :
                d.hexad_overgroup)*g) ∧
            (∀ g, α (α g)=g) ∧
            ¬ ∃ a : q.ker, ∀ g, α g=(a:d.hexad_overgroup)⁻¹*g*a := by
  obtain ⟨hDN,q,hq,hqker,hqmark,k,hk,hact⟩ :=
    d.hexad_kernel_coordinates L hPL e hmark
  exact ⟨hDN,q,hq,hqker,hqmark,k,hk,hact,
    Theory.SpecificGroups.SymmetricSix.PolarAffine.exists_original_quadratic_automorphism
      q hq k hact⟩

end CFSG.Quasithin.HigmanSims
