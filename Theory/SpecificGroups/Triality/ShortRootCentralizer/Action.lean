module
public import Theory.SpecificGroups.Triality.ShortRootCentralizer.Plane
public import Theory.SpecificGroups.Triality.RadicalCoordinates.LeviCommutators.TorusMotion.Weights

/-!
# Action on the long-root plane of a triality short-root centralizer

The central torus moves the highest long root when q > 2, so the perfect
central Levi acts nontrivially on the characteristic long-root plane.
Explicit torus, Weyl and positive-root conjugations send that highest long
root to every nonidentity element of the plane. All conjugators centralize
the same highest short root. These equations supply the nonunitary action
and transitivity used in the I.8.5 step of Aschbacher–Smith F.4.42,
printed p.295 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup
namespace Triality.Standard.ShortRootCentralizer
open Parabolics ConcreteBruhat RadicalCoordinates RadicalCoordinates.LeviCommutators
open EvenInvolutionGeometry.ArmsNormalization

theorem long_two_injective (P : Parameters) (hp : P.prime = 2) :
    Function.Injective (long P hp 2) := by
  intro a b hab
  have he : planeHom P hp (Multiplicative.ofAdd ![0,a]) =
      planeHom P hp (Multiplicative.ofAdd ![0,b]) := by
    apply Subtype.ext
    rw [planeHom_val,planeHom_val]
    change long P hp 1 0 * long P hp 2 a = long P hp 1 0 * long P hp 2 b
    simp only [long_zero,one_mul]
    exact hab
  exact congrFun (congrArg Multiplicative.toAdd (planeHom_injective P hp he)) 1

theorem long_two_mem_plane (P : Parameters) (hp : P.prime = 2) (a : fixedField P) :
    long P hp 2 a ∈ plane P :=
  (plane_mem_iff P hp _).mpr ⟨0,a,by rw [long_zero,one_mul]⟩

theorem torus_long_two (P : Parameters) (hp : P.prime = 2)
    (u : (fixedField P)ˣ) (a : fixedField P) :
    RadicalCoordinates.LeviCommutators.torusActor P hp .central u * long P hp 2 a *
      (RadicalCoordinates.LeviCommutators.torusActor P hp .central u)⁻¹ =
      long P hp 2 (u.val*a) := by
  simp only [RadicalCoordinates.LeviCommutators.torusActor, long, ←map_mul, ←map_inv]
  apply congrArg (toCarrier P)
  apply elementaryInclusion_injective P
  simp only [map_mul,map_inv,longElementary_val]
  exact torus_central_long_two_conjugate P hp u a

/-- For q > 2 the perfect central Levi acts nontrivially on the plane. -/
theorem levi_moves_plane (P : Parameters) (hp : P.prime = 2) (hq : 2 < P.q) :
    ¬ ∀ a ∈ levi P .central, ∀ b ∈ plane P, a*b=b*a := by
  intro h
  obtain ⟨u,hu⟩ := exists_fixedUnit_ne_one P hq
  have he := h _ (torusActor_mem_levi P hp .central u) _ (long_two_mem_plane P hp 1)
  have hh := torus_long_two P hp u 1
  rw [mul_one,he,mul_inv_cancel_right] at hh
  exact hu ((long_two_injective P hp hh).symm)

theorem long_zero_mem_levi (P : Parameters) (hp : P.prime = 2) (a : fixedField P) :
    long P hp 0 a ∈ levi P .central := by
  refine ⟨longElementary P hp 0 a,?_,rfl⟩
  change elementaryInclusion P (longElementary P hp 0 a) ∈ splitLevi P .central
  rw [longElementary_val]
  change PositiveCoordinates.curve P 3 a.val ∈ splitLevi P .central
  rw [show PositiveCoordinates.curve P 3 a.val = positiveRoot P 1 a.val from
    PositiveCoordinates.curve_simple P 1 a.val]
  exact subset_closure ⟨1,rfl,a.val,Or.inl rfl⟩

theorem long_zero_conjugate_one (P : Parameters) (hp : P.prime = 2)
    (a b : fixedField P) :
    long P hp 0 a * long P hp 1 b * (long P hp 0 a)⁻¹ =
      long P hp 1 b * long P hp 2 (a*b) := by
  rw [long_zero_one_exchange P hp a b]
  calc
    _ = long P hp 1 b * (long P hp 0 a * long P hp 2 (a*b) *
      (long P hp 0 a)⁻¹) := by group
    _ = _ := by rw [←(highest_commute_long P hp (a*b) 0 a).eq]; simp

/-- All nonidentity plane elements are conjugate to the pinned highest long
root inside the marked short-root centralizer. -/
theorem plane_orbit (P : Parameters) (hp : P.prime = 2) (t : ExtensionField P)
    (x : Carrier P) (hx : x ∈ plane P) (hx1 : x ≠ 1) :
    ∃ g ∈ centralizer ({short P hp 2 t} : Set (Carrier P)),
      g * long P hp 2 1 * g⁻¹ = x := by
  obtain ⟨a,b,rfl⟩ := (plane_mem_iff P hp x).mp hx
  let C := centralizer ({short P hp 2 t} : Set (Carrier P))
  have htor (u : (fixedField P)ˣ) :
      RadicalCoordinates.LeviCommutators.torusActor P hp .central u ∈ C :=
    levi_central_le_centralizer P hp t (torusActor_mem_levi P hp .central u)
  by_cases ha : a=0
  · have hb : b≠0 := by intro hb; apply hx1; simp [ha,hb,long_zero]
    let u := Units.mk0 b hb
    refine ⟨RadicalCoordinates.LeviCommutators.torusActor P hp .central u,htor u,?_⟩
    simpa only [mul_one,ha,long_zero,one_mul,u,Units.val_mk0] using
      torus_long_two P hp u 1
  · let u := Units.mk0 a ha
    let w := weylRepresentative P hp (.sr 1)
    let k := long P hp 0 (b/a)
    let c := RadicalCoordinates.LeviCommutators.torusActor P hp .central u
    have hw : w ∈ C := mem_centralizer_singleton_iff.mpr
      (mul_inv_eq_iff_eq_mul.mp (central_short_two P hp t))
    have hk : k ∈ C := levi_central_le_centralizer P hp t (long_zero_mem_levi P hp _)
    refine ⟨k*w*c,C.mul_mem (C.mul_mem hk hw) (htor u),?_⟩
    change MulAut.conj (k*w*c) (long P hp 2 1) = _
    rw [map_mul,map_mul,MulAut.mul_apply,MulAut.mul_apply]
    change k*(w*(c*long P hp 2 1*c⁻¹)*w⁻¹)*k⁻¹ = _
    rw [show c*long P hp 2 1*c⁻¹=long P hp 2 a by simpa [c,u] using torus_long_two P hp u 1]
    rw [show w*long P hp 2 a*w⁻¹=long P hp 1 a from central_long_two P hp a]
    simpa only [k,div_mul_cancel₀ _ ha] using long_zero_conjugate_one P hp (b/a) a

end Triality.Standard.ShortRootCentralizer
