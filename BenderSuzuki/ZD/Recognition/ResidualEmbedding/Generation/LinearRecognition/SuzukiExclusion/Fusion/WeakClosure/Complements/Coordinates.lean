module

public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.SquareFibers
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.Generation.LinearRecognition.SuzukiExclusion.Fusion.WeakClosure.Complements.ActionContract

/-!
# Equivariant commutator coordinates for the source quotient S/T

For a fixed nonidentity u in U, x ↦ [x,u] is a homomorphism S → M°.
Its kernel is the literal T, by the centralizer identity, and U_orbits
makes it surjective. It therefore induces an actual quotient equivalence.
The conjugation formula gives equivariance for every normalizer element
centralizing u, and in particular for the original K once its action
contract has been produced. The abstract SylowGeometry quotient_equiv
field is not used in this construction.

Source: GLS4, Chapter 2, Lemmas 14.6(d) and 14.7.
-/

noncomputable section
namespace BenderSuzuki.ZD.SuzukiExclusion
open Subgroup BenderSuzuki.MatrixGroups
open scoped Pointwise commutatorElement
variable {G : Type*} [Group G] [Finite G] {Z : Set G} {M : Subgroup G}
  {z t : G} {m : ℕ}

/-- Commuting with one fixed nonidentity element of U gives the coordinates
of S/T in the distinguished closure. -/
@[expose] public def SylowGeometry.commutatorCoordinate
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (u : G) (hu : u ∈ g.U) : g.S →* closure (Z ∩ (M : Set G)) where
  toFun x := ⟨⁅(x : G), u⁆, s.central_mod_A (commutator_mem_commutator x.property hu)⟩
  map_one' := by apply Subtype.ext; simp only [coe_one, commutatorElement_one_left]
  map_mul' x y := by
    apply Subtype.ext
    change ⁅(x : G) * (y : G), u⁆ = ⁅(x : G), u⁆ * ⁅(y : G), u⁆
    have hy := s.central_mod_A (commutator_mem_commutator y.property hu)
    have hx := s.central_mod_A (commutator_mem_commutator x.property hu)
    have hc := (s.closure_commute g hy x.property).symm
    rw [commutatorElement_mul_left_eq_conj_mul, hc.eq, mul_inv_cancel_right]
    exact (s.closure_commute g hy (g.closure_le_S hx)).eq

public theorem SylowGeometry.commutatorCoordinate_ker
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (u : G) (hu : u ∈ g.U) (hu1 : u ≠ 1) :
    (s.commutatorCoordinate g u hu).ker = g.T.subgroupOf g.S := by
  ext x
  change (⟨⁅(x : G), u⁆, _⟩ : closure (Z ∩ (M : Set G))) = 1 ↔ (x : G) ∈ g.T
  rw [Subtype.ext_iff, coe_one, commutatorElement_eq_one_iff_commute]
  constructor
  · intro hx
    rw [← g.centralizer_U u hu hu1]
    exact ⟨s.S_le_closure_centralizer g x.property, mem_centralizer_singleton_iff.mpr hx.eq⟩
  · intro hx
    rw [← g.centralizer_U u hu hu1] at hx
    exact mem_centralizer_singleton_iff.mp hx.2

public theorem SylowGeometry.commutatorCoordinate_surjective
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (u : G) (hu : u ∈ g.U) (hu1 : u ≠ 1) :
    Function.Surjective (s.commutatorCoordinate g u hu) := by
  intro a
  obtain ⟨x, hx, he⟩ := (s.U_orbits u hu hu1 ((a : G) * u)).mpr ⟨a, a.property, rfl⟩
  refine ⟨⟨x, hx⟩, Subtype.ext ?_⟩
  change ⁅x, u⁆ = a
  rw [conj_eq_commutatorElement_mul] at he
  exact mul_right_cancel he

/-- The source quotient identification built from the actual commutator map. -/
@[expose] public def SylowGeometry.commutatorQuotientEquiv
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (u : G) (hu : u ∈ g.U) (hu1 : u ≠ 1) :
    letI := s.T_normal
    (g.S ⧸ g.T.subgroupOf g.S) ≃* closure (Z ∩ (M : Set G)) := by
  letI := s.T_normal
  exact QuotientGroup.liftEquiv _ (s.commutatorCoordinate_surjective g u hu hu1)
    (s.commutatorCoordinate_ker g u hu hu1).symm

/-- Formula on literal quotient representatives; this determines the equivariance. -/
public theorem SylowGeometry.commutatorQuotientEquiv_apply
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (u : G) (hu : u ∈ g.U) (hu1 : u ≠ 1) (x : g.S) :
    letI := s.T_normal
    (s.commutatorQuotientEquiv g u hu hu1 (QuotientGroup.mk' _ x) : G) = ⁅(x : G), u⁆ := rfl

/-- Equivariance under every actual normalizer element that centralizes u. -/
public theorem SylowGeometry.commutatorQuotientEquiv_conj
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (u : G) (hu : u ∈ g.U) (hu1 : u ≠ 1)
    (k : G) (hk : k ∈ normalizer (g.S : Set G)) (hku : Commute k u) (x : g.S) :
    letI := s.T_normal
    (s.commutatorQuotientEquiv g u hu hu1
      (QuotientGroup.mk' _ ⟨MulAut.conj k (x : G),
        (mem_normalizer_iff.mp hk (x : G)).mp x.property⟩) : G) =
      MulAut.conj k (s.commutatorQuotientEquiv g u hu hu1 (QuotientGroup.mk' _ x) : G) := by
  change ⁅MulAut.conj k (x : G), u⁆ = MulAut.conj k ⁅(x : G), u⁆
  rw [map_commutatorElement]
  have he : MulAut.conj k u = u := by
    simp only [MulAut.conj_apply, hku.eq, mul_inv_cancel_right]
  rw [he]

/-- The coordinate identification intertwines the original split torus actions,
with the action on quotient representatives given by ambient conjugation. -/
public theorem SylowGeometry.commutatorQuotientEquiv_torus
    (g : LocalGeometry Z M z t m) (s : SylowGeometry g)
    (hK : TorusQuotientAction g) (u : G) (hu : u ∈ g.U) (hu1 : u ≠ 1)
    (k : G) (hk : k ∈ residualCommutator M t) (x : g.S) :
    letI := s.T_normal
    (s.commutatorQuotientEquiv g u hu hu1
      (QuotientGroup.mk' _ ⟨MulAut.conj k (x : G),
        (mem_normalizer_iff.mp (hK.normalizes_S hk) (x : G)).mp x.property⟩) : G) =
      MulAut.conj k (s.commutatorQuotientEquiv g u hu hu1 (QuotientGroup.mk' _ x) : G) := by
  apply s.commutatorQuotientEquiv_conj g u hu hu1 k (hK.normalizes_S hk) _ x
  exact mem_centralizer_iff.mp (g.U_le_centralizer hu) k
    ((show residualCommutator M t ≤ residualGenerated M z t from le_sup_right) hk)


end BenderSuzuki.ZD.SuzukiExclusion
