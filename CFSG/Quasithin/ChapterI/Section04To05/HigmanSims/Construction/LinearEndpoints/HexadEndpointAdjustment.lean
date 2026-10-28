module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import Theory.SpecificGroups.SymmetricSix.PolarAffine.EndpointAdjustment

/-!
# The attainable displacement orbit of the original endpoint

For the original endpoint inside its original hexad group, an endpoint
marking displacement is attainable precisely when it is a binary quadratic
restriction plus a principal displacement. The automorphism preserves the
literal quotient, the whole original kernel pointwise, and every subgroup
containing that kernel. An endpoint actor is fixed precisely when its
prescribed displacement vanishes.

This is a selection criterion on actual source coordinates. Selecting the
relative field orientation and showing that the desired displacement passes
this criterion remain separate geometric tasks.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] {A : Subgroup G} [IsElementaryAbelian 2 A]
local notation "Point" => Matrix.PSL3.LinearThree.pointParabolic Matrix.PSL3Four.F
local notation "A6" => alternatingGroup (Fin 6)
local notation "Vec" => Theory.SpecificGroups.SymmetricSix.NaturalModule
open Theory.SpecificGroups.SymmetricSix (polarAction)
open Theory.SpecificGroups.SymmetricSix.PolarAffine (quadratic)

/-- Exact endpoint displacement selection on the same original hexad group,
with its original quotient and every original kernel coordinate retained. -/
theorem NaturalEndpointData.hexad_endpoint_adjustment_selection (d : NaturalEndpointData A)
    (L : Subgroup G) (hPL : d.carrier ≤ L) (e : L ≃* Matrix.PSL3Four.PSL)
    (hmark : (d.carrier.subgroupOf L).map e.toMonoidHom = Point) :
    ∃ (hDN : d.hexad_overgroup ≤ normalizer (A : Set G))
      (hPD : d.carrier ≤ d.hexad_overgroup),
      ∃ q : d.hexad_overgroup →* A6, Function.Surjective q ∧
        ∃ hker : q.ker = A.subgroupOf d.hexad_overgroup,
        (∀ g : d.hexad_overgroup, (q g : Equiv.Perm (Fin 6)) =
          d.six_letter_quotient (inclusion hDN g)) ∧
        ∃ k : q.ker ≃* Multiplicative Vec,
          (∀ a : q.ker, (k a).toAdd = d.binary_coordinates
            (Additive.ofMul ⟨((a : d.hexad_overgroup) : G), by
              exact (show (a : d.hexad_overgroup) ∈ A.subgroupOf d.hexad_overgroup
                from hker ▸ a.property)⟩)) ∧
          (∀ (g : d.hexad_overgroup) (a : q.ker),
            k (MulAut.conjNormal g a) = Multiplicative.ofAdd
              (polarAction (q g).val (k a).toAdd)) ∧
          ∀ f : d.carrier → Vec,
            (∃ α : MulAut d.hexad_overgroup,
              (∀ g, q (α g) = q g) ∧
              (∀ a : q.ker, α a = (a : d.hexad_overgroup)) ∧
              (∀ p, α (inclusion hPD p) =
                (k.symm (Multiplicative.ofAdd (f p)) : d.hexad_overgroup) * inclusion hPD p) ∧
              (∀ P : Subgroup d.hexad_overgroup,
                q.ker ≤ P → P.map α.toMonoidHom = P) ∧
              (∀ p, α (inclusion hPD p) = inclusion hPD p ↔ f p = 0)) ↔
            ∃ (b : ZMod 2) (v : Vec), ∀ p,
              f p = b • quadratic (q (inclusion hPD p)) +
                (polarAction (q (inclusion hPD p)).val v - v) := by
  obtain ⟨hDN,q,hq,hker,hqmark,k,hk,hact⟩ :=
    d.hexad_kernel_coordinates L hPL e hmark
  obtain ⟨_,_,hPD,_⟩ := d.hexad_overgroup_structure L hPL e hmark
  refine ⟨hDN,hPD,q,hq,hker,hqmark,k,hk,hact,fun f => ?_⟩
  exact Theory.SpecificGroups.SymmetricSix.PolarAffine.original_endpoint_adjustment_iff
    q hq k hact (inclusion hPD) f

end CFSG.Quasithin.HigmanSims
