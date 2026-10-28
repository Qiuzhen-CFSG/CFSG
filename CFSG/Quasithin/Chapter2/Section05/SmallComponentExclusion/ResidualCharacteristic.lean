module
public import CFSG.Quasithin.Chapter2.Section05.SmallComponentExclusion.LocalResidualFacts
public import Theory.GroupTheory.PResidual.PrimeToIntersection
public import Theory.SpecificGroups.SL2.PrimeToResidual
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-!
# Prime-to-three transport of the local SL₂(3) residual

The concrete GL₂(3) two-residual is also O^{3′}. Intersecting the
ambient O^{3′} with the involution centralizer transports the literal
component residual to O^{3′}(C_G(Z(S))). This is the characteristic residual
used by the 2.5.15 crossing argument.
Source: Aschbacher--Smith 2.5.15, printed pp.558--559.
-/

public section
namespace CFSG.Quasithin.Chapter2.Section05
open Subgroup Theory.GroupTheory ComponentSelection
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem local_residual_primeTo (K : Subgroup G)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (z : K) (hz : orderOf z = 2) :
    pResidual 2 (centralizer ({z} : Set K)) = primeToResidual 3 (centralizer ({z} : Set K)) := by
  let e := localResidualCentralizerEquiv K hK z hz
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [map_pResidual 2 e, map_primeToResidual e,
    Matrix.GeneralLinearGroup.three_twoResidual,
    Matrix.GeneralLinearGroup.primeToResidual_eq_det_ker]
  rfl

omit [Finite G] in
theorem local_residual_primeTo_ambient (K : Subgroup G)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (z : K) (hz : orderOf z = 2) :
    (GLTwoThreeLocal.residual z).map K.subtype =
      (primeToResidual 3 (K ⊓ centralizer ({(z : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(z : G)} : Set G)).subtype := by
  let C := K ⊓ centralizer ({(z : G)} : Set G)
  let e : centralizer ({z} : Set K) ≃* C := {
    toFun x := ⟨x,⟨x.val.property,mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp x.property))⟩⟩
    invFun x := ⟨⟨x,x.property.1⟩,mem_centralizer_singleton_iff.mpr
      (Subtype.ext (mem_centralizer_singleton_iff.mp x.property.2))⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  change ((pResidual 2 (centralizer ({z} : Set K))).map _).map _ = _
  rw [local_residual_primeTo K hK z hz,map_map]
  have hf : K.subtype.comp (centralizer ({z} : Set K)).subtype = C.subtype.comp e.toMonoidHom := rfl
  rw [hf,←map_map,map_primeToResidual e]

theorem local_residual_characteristic_centralizer
    (K Y : Subgroup G)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (z : K) (hz : orderOf z = 2) (t : G)
    (hZ : centerIn Y = zpowers t ⊔ zpowers (z : G))
    (hres : K = (primeToResidual 3 (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype) :
    (GLTwoThreeLocal.residual z).map K.subtype =
      (primeToResidual 3 (centralizer (centerIn Y : Set G))).map
        (centralizer (centerIn Y : Set G)).subtype := by
  rw [local_residual_primeTo_ambient K hK z hz]
  have hh := embedded_primeToResidual_intersection 3 (centralizer ({t} : Set G))
    (centralizer ({(z : G)} : Set G))
  rw [← hres] at hh
  rw [hh]
  have hc : centralizer ({t} : Set G) ⊓ centralizer ({(z : G)} : Set G) =
      centralizer (centerIn Y : Set G) := by
    apply le_antisymm
    · intro x hx
      have ht : t ∈ centralizer ({x} : Set G) :=
        mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hx.1).symm
      have hz : (z : G) ∈ centralizer ({x} : Set G) :=
        mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp hx.2).symm
      have hle : centerIn Y ≤ centralizer ({x} : Set G) := by
        rw [hZ]; exact sup_le (zpowers_le.mpr ht) (zpowers_le.mpr hz)
      intro y hy
      exact mem_centralizer_singleton_iff.mp (hle hy)
    · intro x hx
      have ht : t ∈ centerIn Y := hZ ▸ mem_sup_left (mem_zpowers t)
      have hz : (z : G) ∈ centerIn Y := hZ ▸ mem_sup_right (mem_zpowers (z : G))
      exact ⟨mem_centralizer_singleton_iff.mpr (hx t ht).symm,
        mem_centralizer_singleton_iff.mpr (hx z hz).symm⟩
  rw [hc]

/-- The original Sylow normalizer acts on the actual local residual. -/
theorem local_residual_normalized_by_sylow_normalizer
    (K Y : Subgroup G)
    (hK : Nonempty (K ≃* Matrix.PSL3Three.PSL) ∨ Nonempty (K ≃* Sporadic.Mathieu.M11))
    (z : K) (hz : orderOf z = 2) (t : G)
    (hZ : centerIn Y = zpowers t ⊔ zpowers (z : G))
    (hres : K = (primeToResidual 3 (centralizer ({t} : Set G))).map
      (centralizer ({t} : Set G)).subtype) :
    normalizer (Y : Set G) ≤ normalizer ((GLTwoThreeLocal.residual z).map K.subtype : Set G) := by
  rw [local_residual_characteristic_centralizer K Y hK z hz t hZ hres]
  exact (normalizes_centerIn (le_rfl : normalizer (Y : Set G) ≤ normalizer (Y : Set G))).trans
    ((normalizer_le_normalizer_centralizer (centerIn Y)).trans
      (normalizer_le_normalizer_characteristic_image _ (primeToResidual 3 _)))

end CFSG.Quasithin.Chapter2.Section05
