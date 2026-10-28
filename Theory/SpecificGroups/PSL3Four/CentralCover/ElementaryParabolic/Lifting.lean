module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.CentralTwist.StandardCover.InvolutionLifting
public import Theory.Frattini.PGroup

/-!
# Elementary inverse images in central covers of PSL₃(4)

The involution-lifting theorem implies that the full inverse image of every
binary elementary subgroup is elementary. This applies to the actual quotient
by the center once its Frattini subgroup is trivial; no restriction on the
order of that elementary center is imposed.

Source: Aschbacher--Smith I.2.2(3b), printed pp.409--410, and the application
in 2.5.7, printed pp.554--555.
-/

public section
open Subgroup
namespace Matrix.PSL3Four.ElementaryParabolic
variable {E : Type*} [Group E]

private theorem elementary_of_squares {A : Type*} [Group A]
    (hs : ∀ a : A, a ^ 2 = 1) : IsElementaryAbelian 2 A where
  toIsMulCommutative := ⟨⟨fun x y => Commute.of_orderOf_dvd_two
    (fun a => orderOf_dvd_of_pow_eq_one (hs a)) x y⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs

/-- Every full elementary inverse image, with the original covering map. -/
theorem elementary_comap (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀ z ∈ f.ker, z ^ 2 = 1)
    (A : Subgroup PSL) [IsElementaryAbelian 2 A] :
    IsElementaryAbelian 2 (A.comap f) := by
  apply elementary_of_squares
  intro x
  apply Subtype.ext
  exact ExtendedCentralizer.CoverCentralizers.CentralTwist.square_eq_one_of_elementary_kernel
    f hf hc hs x (elemPow_eq_one_of_isElementaryAbelian (f x) x.property)

/-- The same conclusion for a subgroup whose literal image is elementary. -/
theorem elementary_of_image (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀ z ∈ f.ker, z ^ 2 = 1)
    (A : Subgroup E) [IsElementaryAbelian 2 (A.map f)] : IsElementaryAbelian 2 A := by
  apply elementary_of_squares
  intro x
  apply Subtype.ext
  exact ExtendedCentralizer.CoverCentralizers.CentralTwist.square_eq_one_of_elementary_kernel
    f hf hc hs x (elemPow_eq_one_of_isElementaryAbelian (f x) (mem_map_of_mem f x.property))

/-- Frattini-trivial inverse images, without a perfect-cover certificate. -/
theorem comap_frattini_eq_bot [Finite E]
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀ z ∈ f.ker, z ^ 2 = 1)
    (A : Subgroup PSL) [IsElementaryAbelian 2 A] : frattini (A.comap f) = ⊥ := by
  let := elementary_comap f hf hc hs A
  let : Fact (IsPGroup 2 (A.comap f)) := ⟨IsElementaryAbelian.isPGroup 2 _⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- The canonical marked quotient map used by the original source. -/
noncomputable def centerProjection (e : (E ⧸ center E) ≃* PSL) : E →* PSL :=
  e.toMonoidHom.comp (QuotientGroup.mk' (center E))

theorem centerProjection_surjective (e : (E ⧸ center E) ≃* PSL) :
    Function.Surjective (centerProjection e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

@[simp] theorem centerProjection_ker (e : (E ⧸ center E) ≃* PSL) :
    (centerProjection e).ker = center E := by
  ext x
  change e (QuotientGroup.mk' (center E) x) = 1 ↔ x ∈ center E
  rw [← e.map_one, e.injective.eq_iff]
  exact QuotientGroup.eq_one_iff x

/-- Literal quotient involution lifts from the source Frattini hypothesis. -/
theorem centerProjection_square [Finite E] (e : (E ⧸ center E) ≃* PSL)
    (hz : IsPGroup 2 (center E)) (hphi : frattini (center E) = ⊥)
    (x : E) (hx : (centerProjection e x) ^ 2 = 1) : x ^ 2 = 1 := by
  let : Fact (IsPGroup 2 (center E)) := ⟨hz⟩
  let : IsElementaryAbelian 2 (center E) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  apply ExtendedCentralizer.CoverCentralizers.CentralTwist.square_eq_one_of_elementary_kernel
    (centerProjection e) (centerProjection_surjective e)
  · rw [centerProjection_ker]
  · intro z hz
    rw [centerProjection_ker] at hz
    exact elemPow_eq_one_of_isElementaryAbelian z hz
  · exact hx

/-- Every elementary subgroup of the source quotient has elementary full preimage. -/
theorem centerProjection_elementary_comap [Finite E]
    (e : (E ⧸ center E) ≃* PSL)
    (hz : IsPGroup 2 (center E)) (hphi : frattini (center E) = ⊥)
    (A : Subgroup PSL) [IsElementaryAbelian 2 A] :
    IsElementaryAbelian 2 (A.comap (centerProjection e)) := by
  apply elementary_of_squares
  intro x
  exact Subtype.ext (centerProjection_square e hz hphi x
    (elemPow_eq_one_of_isElementaryAbelian _ x.property))

end Matrix.PSL3Four.ElementaryParabolic
