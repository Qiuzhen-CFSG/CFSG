module

public import Theory.Mathieu.M12.TwoCentralInvolutions.CentralizerOrder
public import Theory.Mathieu.M12.SmallParabolicPair.CoverOrbits.Residual
public import Theory.GroupTheory.CentralizerSmallKernelTransport
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.ResidualAction
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.Levi

/-!
# The full binary G₂ first vertex cannot occur in M₁₂

A subgroup of order 192 centralizing the center of an M₁₂ Sylow subgroup
equals the centralizer of its central involution. The actual two-central
conjugacy theorem identifies this centralizer with the marked first M₁₂
parabolic, whose two-residual has order 96. The full binary G₂ first vertex
has the same order 192 but two-residual of order 24, so an injective marked
first-vertex map is impossible. This distinguishes the source amalgams even
though their abstract common Sylow groups and coarse extension shapes agree.

Source: Aschbacher–Smith F.1.12(I)(3,12), F.6.18(11–12), and 14.2.21;
the imported modules supply all concrete residual and involution calculations.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Theory.GroupTheory.DoubleCoverCentralizer
namespace Sporadic.Mathieu.M12FullG2Obstruction
open M12SmallPair

/-- The residual order is invariant across the actual two-central class. -/
theorem residual_card_centralizer_of_twoCentral (x : M12)
    (hx : orderOf x = 2) (hc : TwoCentral x) :
    Nat.card (pResidual 2 (centralizer ({x} : Set M12))) = 96 := by
  obtain ⟨g,rfl⟩ := isConj_iff.mp (M12Involutions.isConj_z_of_twoCentral x hx hc)
  let e : firstParabolic ≃* centralizer ({MulAut.conj g z} : Set M12) :=
    CentralizerSmallKernelTransport.centralizerEquiv (MulAut.conj g) z
  change Nat.card (pResidual 2 (centralizer ({MulAut.conj g z} : Set M12))) = 96
  rw [← map_pResidual 2 e,
    card_map_of_injective (f := e.toMonoidHom) e.injective]
  exact CoverOrbits.card_residual

/-- Centralizing the literal Sylow center identifies any order-192 subgroup's
two-residual, without an assumed parabolic recognition. -/
theorem residual_card_of_sylow_center_centralized
    (A : Subgroup M12) (hA : Nat.card A = 192) (P : Sylow 2 M12)
    (hZ : A ≤ centralizer (((center P).map (P : Subgroup M12).subtype) : Set M12)) :
    Nat.card (pResidual 2 A) = 96 := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq M12 commonSylow P
  let e : commonSylow ≃* P := (commonSylow.equivSMul g).trans
    (MulEquiv.subgroupCongr (congrArg (fun T : Sylow 2 M12 => (T : Subgroup M12)) hg))
  let z₀ : commonSylow := ⟨z,core_le_sylowCandidate z_mem_core⟩
  have hz₀ : z₀ ∈ center commonSylow :=
    (sylowCandidate_center_mem _).mpr (Or.inr rfl)
  let x : P := e z₀
  have hxc : x ∈ center P := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨w,rfl⟩ := e.surjective y
    change e w * e z₀ = e z₀ * e w
    rw [← e.map_mul, ← e.map_mul, mem_center_iff.mp hz₀ w]
  have hx : orderOf (x : M12) = 2 := by
    calc
      orderOf (x : M12) = orderOf x :=
        orderOf_injective (P : Subgroup M12).subtype (P : Subgroup M12).subtype_injective x
      _ = orderOf z₀ := e.orderOf_eq z₀
      _ = orderOf z := (orderOf_injective (commonSylow : Subgroup M12).subtype
        (commonSylow : Subgroup M12).subtype_injective z₀).symm
      _ = 2 := z_order
  have hc : TwoCentral (x : M12) := ⟨P,x.property,hxc⟩
  have hle : A ≤ centralizer ({(x : M12)} : Set M12) := by
    intro a ha
    apply mem_centralizer_singleton_iff.mpr
    exact (mem_centralizer_iff.mp (hZ ha) _ ⟨x,hxc,rfl⟩).symm
  have he : A = centralizer ({(x : M12)} : Set M12) :=
    eq_of_le_of_card_ge hle (by rw [hA,M12Involutions.card_centralizer_of_twoCentral _ hx hc])
  rw [he]
  exact residual_card_centralizer_of_twoCentral _ hx hc

/-- The first full-G₂ vertex is excluded by its actual residual, retaining
the precise image and Sylow-center map needed by the source consumer. -/
theorem not_injective_first_parabolic
    (f : Atlas.G2.BinaryParabolicPair.firstParabolic →* M12)
    (hf : Function.Injective f) (P : Sylow 2 M12)
    (hZ : f.range ≤ centralizer (((center P).map (P : Subgroup M12).subtype) : Set M12)) :
    False := by
  let e := MonoidHom.ofInjective hf
  have hA : Nat.card f.range = 192 :=
    (Nat.card_congr e.symm.toEquiv).trans Atlas.G2.BinaryParabolicPair.card_firstParabolic
  have hc := residual_card_of_sylow_center_centralized f.range hA P hZ
  have h24 : Nat.card (pResidual 2 Atlas.G2.BinaryParabolicPair.firstParabolic) = 24 := by
    rw [← card_map_of_injective Atlas.G2.BinaryParabolicPair.firstParabolic.subtype_injective,
      Atlas.G2.BinaryParabolicPair.ResidualAction.first_residual]
    exact Atlas.G2.BinaryParabolicPair.ResidualAction.card_K
  rw [← map_pResidual 2 e,
    card_map_of_injective (f := e.toMonoidHom) e.injective, h24] at hc
  omega

end Sporadic.Mathieu.M12FullG2Obstruction
