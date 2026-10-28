module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.LinearEndpoints.HexadCoordinates
public import Theory.SpecificGroups.SymmetricSix.PolarAffine.EndpointActorAdjustment

/-!
# Selecting endpoint alignment while retaining original actors

This criterion measures a candidate endpoint map in the original hexad
extension. A single quadratic/principal parameter pair must both align that
map and vanish on every prescribed original actor. All kernel coordinates
and the literal six-letter quotient come from the original endpoint data.
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

/-- Actual endpoint alignment with prescribed fixed actors, expressed in the
original binary coordinates and literal six-letter quotient. -/
theorem NaturalEndpointData.hexad_endpoint_actor_selection (d : NaturalEndpointData A)
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
          ∀ (τ : d.carrier →* d.hexad_overgroup)
            (hτ : ∀ p, q (τ p) = q (inclusion hPD p))
            (actors : Set d.hexad_overgroup),
            (∃ α : MulAut d.hexad_overgroup,
              (∀ g, q (α g) = q g) ∧
              (∀ a : q.ker, α a = (a : d.hexad_overgroup)) ∧
              (∀ p, α (inclusion hPD p) = τ p) ∧
              (∀ P : Subgroup d.hexad_overgroup,
                q.ker ≤ P → P.map α.toMonoidHom = P) ∧
              (∀ a ∈ actors, α a = a)) ↔
            ∃ (b : ZMod 2) (v : Vec),
              (∀ p, (k ⟨τ p * (inclusion hPD p)⁻¹, by
                simp only [MonoidHom.mem_ker, map_mul, map_inv, hτ,
                  mul_inv_cancel]⟩).toAdd =
                b • quadratic (q (inclusion hPD p)) +
                  (polarAction (q (inclusion hPD p)).val v - v)) ∧
              (∀ a ∈ actors,
                b • quadratic (q a) + (polarAction (q a).val v - v) = 0) := by
  obtain ⟨hDN,q,hq,hker,hqmark,k,hk,hact⟩ :=
    d.hexad_kernel_coordinates L hPL e hmark
  obtain ⟨_,_,hPD,_⟩ := d.hexad_overgroup_structure L hPL e hmark
  refine ⟨hDN,hPD,q,hq,hker,hqmark,k,hk,hact,fun τ hτ actors => ?_⟩
  exact Theory.SpecificGroups.SymmetricSix.PolarAffine.original_endpoint_alignment_fixing_iff
    q hq k hact (inclusion hPD) τ hτ actors

end CFSG.Quasithin.HigmanSims
