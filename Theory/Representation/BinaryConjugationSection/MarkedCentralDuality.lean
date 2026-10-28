module
public import Theory.Representation.BinaryConjugationSection.CentralDuality
public import Theory.Representation.BinaryConjugationSection.Projection

/-!
# Central commutator duality in prescribed coordinates

A marked binary section U/Z with Z = C_U(Q) determines the actual dual
section Q/C_Q(U). Central commutator duality first constructs its own
coordinates. The two coordinate maps on U/Z induce an equivariant linear
isomorphism; its dual transports the second section while preserving the
vanishing-commutator pairing. The given natural coordinate map is unchanged.

Source: Aschbacher–Smith, The Classification of Quasithin Groups,
F.9.7, printed p.321; application 13.7.4(2) and 13.8.31, pp.936,965.
-/

public noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}

/-- Construct the dual section in the supplied natural coordinates, preserving
vanishing of the literal ambient commutator pairing. -/
theorem exists_marked_central_duality (d : BinaryConjugationSection H U Z ρ) [IsElementaryAbelian 2 U]
    (Q : Subgroup G) (hQH : Q ≤ H) (hNQ : H ≤ normalizer (Q:Set G))
    (hZQ : Z ≤ Q) (hZ : Z ≤ centralizer (H:Set G))
    (hcomm : ⁅Q,U⁆ ≤ Z) (hcard : Nat.card Z = 2)
    (hfixed : U ⊓ centralizer (Q:Set G) = Z) :
    ∃ sQ : BinaryConjugationSection H Q (Q ⊓ centralizer (U:Set G)) ρ.dual,
      ∀ (q : Q) (u : U), (sQ.coordinates q).toAdd (d.coordinates u).toAdd = 0 ↔
        ⁅(q:G),(u:G)⁆ = 1 := by
  obtain ⟨ρ₀,s₀,sQ,hpair,_⟩ := exists_central_duality H Q U Z hQH d.section_le
    hNQ d.normalized hZQ hZ hcomm hcard
  let s : BinaryConjugationSection H U Z ρ₀ := {
    s₀ with
    kernel_le := hfixed ▸ s₀.kernel_le
    kernel_eq := by rw [s₀.kernel_eq,hfixed] }
  obtain ⟨f,hf,hcoord,hker⟩ := exists_projection H H U Z Z le_rfl le_rfl
    (MonoidHom.id H) (MonoidHom.id H) Function.surjective_id (MonoidHom.id H)
    (fun _ => rfl) ρ ρ₀ d s
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    rw [hker]
    apply bot_unique
    intro w hw
    obtain ⟨u,hu,rfl⟩ := (d.mem_imageSpace_iff Z w).mp hw
    exact (d.coordinates_eq_one_iff u).mpr hu
  let e : W ≃ₗ[ZMod 2] _ := LinearEquiv.ofBijective f.toLinearMap ⟨hinj,hf⟩
  have heq (h : H) (w : W) : e (ρ h w) = ρ₀ h (e w) :=
    IntertwiningMap.isIntertwining _ _ f h w
  let c : Q →* Multiplicative (Module.Dual (ZMod 2) W) :=
    e.dualMap.toAddEquiv.toMultiplicative.toMonoidHom.comp sQ.coordinates
  refine ⟨{ section_le := hQH
            kernel_le := sQ.kernel_le
            normalized := hNQ
            coordinates := c
            onto := e.dualMap.toAddEquiv.toMultiplicative.surjective.comp sQ.onto
            kernel_eq := ?_
            equivariant := ?_ },?_⟩
  · ext q
    change e.dualMap (sQ.coordinates q).toAdd = 0 ↔ _
    rw [e.dualMap.map_eq_zero_iff]
    exact sQ.coordinates_eq_one_iff q
  · intro h q
    ext w
    change (sQ.coordinates _).toAdd (e w) = (sQ.coordinates q).toAdd (e (ρ h⁻¹ w))
    rw [sQ.equivariant,heq]
    rfl
  · intro q u
    change (sQ.coordinates q).toAdd (e (d.coordinates u).toAdd) = 0 ↔ _
    rw [show e (d.coordinates u).toAdd = (s.coordinates u).toAdd from hcoord u]
    exact hpair q u
end Representation.BinaryConjugationSection
