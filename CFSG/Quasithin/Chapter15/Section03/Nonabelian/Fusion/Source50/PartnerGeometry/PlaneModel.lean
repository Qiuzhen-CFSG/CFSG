module
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixRankOne

/-!
# The literal cubic orbit plane

Two orbit vectors give coordinates on the selected totally singular plane.
The order-twelve rank-one model preserves it, with the right involution
as its exact pointwise kernel. These coordinates are transported unchanged
to V₀ in the original group in source 15.3.56.
-/

@[expose] public noncomputable section
open Matrix Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixOrbit
open ClassicalOrthogonal.FourPlusMatrix

def orbitMap (X : M) : (Fin 2 → ZMod 2) →ₗ[ZMod 2] M where
  toFun a := a 0 • X + a 1 • matrixAction leftCubic X
  map_add' a b := by simp only [Pi.add_apply, add_smul]; abel
  map_smul' a b := by simp only [Pi.smul_apply, smul_add, smul_smul]; rfl

def orbitGroupMap (X : M) : Multiplicative (Fin 2 → ZMod 2) →* Multiplicative M :=
  (orbitMap X).toAddMonoidHom.toMultiplicative

def orbitPlane (X : M) : Subgroup (Multiplicative M) := (orbitGroupMap X).range

theorem mem_orbitPlane (X : M) (v : Multiplicative M) :
    v ∈ orbitPlane X ↔ ∃ a : Fin 2 → ZMod 2, orbitMap X a = v.toAdd := Iff.rfl

theorem orbitPlane_card (X : M) (hX : X ≠ 0) : Nat.card (orbitPlane X) = 4 := by
  let e := (MonoidHom.ofInjective (f := orbitGroupMap X) (orbit_coordinates_injective X hX))
  change Nat.card (orbitGroupMap X).range = 4
  rw [← Nat.card_congr e.toEquiv]
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 2) ≃ _)]
  simp only [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  rfl

theorem orbitPlane_first (X : M) : Multiplicative.ofAdd X ∈ orbitPlane X := by
  refine ⟨Multiplicative.ofAdd ![1,0], ?_⟩
  apply Multiplicative.toAdd.injective
  change (1 : ZMod 2) • X + (0 : ZMod 2) • matrixAction leftCubic X = X
  simp

theorem orbitPlane_second (X : M) :
    Multiplicative.ofAdd (matrixAction leftCubic X) ∈ orbitPlane X := by
  refine ⟨Multiplicative.ofAdd ![0,1], ?_⟩
  apply Multiplicative.toAdd.injective
  change (0 : ZMod 2) • X + (1 : ZMod 2) • matrixAction leftCubic X = _
  simp

theorem rankOne_preserves_plane (X : M) (hX : X ≠ 0) (hs : X.det = 0)
    (a : rankOne X) (v : Multiplicative M) (hv : v ∈ orbitPlane X) :
    Multiplicative.ofAdd (matrixAction a.val v.toAdd) ∈ orbitPlane X := by
  obtain ⟨b, hb⟩ := hv
  have hr : matrixAction (1, a.val.2) X = X := a.property
  obtain ⟨c, hc⟩ := (show ∀ X : M, X ≠ 0 → X.det = 0 → ∀ a : P,
    matrixAction (1, a.2) X = X → ∀ b : Fin 2 → ZMod 2,
      ∃ c : Fin 2 → ZMod 2, matrixAction a (orbitMap X b) = orbitMap X c
      by decide +kernel) X hX hs a.val hr b.toAdd
  refine ⟨Multiplicative.ofAdd c, ?_⟩
  apply Multiplicative.toAdd.injective
  change orbitMap X c = matrixAction a.val v.toAdd
  rw [← hc]
  exact congrArg (matrixAction a.val) (congrArg Multiplicative.toAdd hb)

theorem rankOne_plane_kernel (X : M) (hX : X ≠ 0) (a : rankOne X) :
    (∀ v ∈ orbitPlane X, matrixAction a.val v.toAdd = v.toAdd) ↔ a.val.1 = 1 := by
  rw [← orbit_plane_kernel X hX a.val a.property]
  constructor
  · intro h
    exact ⟨h _ (orbitPlane_first X), h _ (orbitPlane_second X)⟩
  · rintro ⟨hfirst,hsecond⟩ v ⟨b,rfl⟩
    change matrixAction a.val (b.toAdd 0 • X + b.toAdd 1 • matrixAction leftCubic X) = _
    rw [map_add, map_smul, map_smul, hfirst, hsecond]
    rfl

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Source50.PartnerGeometry.MatrixOrbit
