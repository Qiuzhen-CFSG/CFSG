module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ElementaryParabolic.Natural

/-!
# The full parabolic cores in elementary PSL₃(4) covers

At field order four the scalar quotient of a maximal parabolic disappears
projectively: scaling by its distinguished diagonal entry produces an actual
root-local representative. The full parabolic therefore has the same affine
model as its residual. Involution lifting makes its actual two-core elementary.

Source: Aschbacher--Smith I.2.2(3b), printed pp.409--410.
-/

@[expose] public section
open Subgroup Matrix
open scoped MatrixGroups
noncomputable section
namespace Matrix.PSL3Four.ElementaryParabolic
open Matrix.PSL3.LinearThree Matrix.PSL3.RootPlaneGeometry
open Matrix.PSL3.LinearThree.OuterExtensions
private def scalarFour (r : F) (hr : r ≠ 0) : SL(3,F) :=
  ⟨Matrix.scalar (Fin 3) r, by
    let : Fintype F := Fintype.ofFinite F
    have hh := FiniteField.pow_card_sub_one_eq_one r hr
    have he : r ^ 3 = 1 := by simpa only [← Nat.card_eq_fintype_card, card_F] using hh
    simpa [Matrix.scalar, Matrix.det_diagonal, Fin.prod_univ_three, pow_succ] using he⟩
private theorem scalarFour_center (r : F) (hr : r ≠ 0) : scalarFour r hr ∈ center SL(3,F) := by
  apply Matrix.SpecialLinearGroup.mem_center_iff.mpr
  refine ⟨r, ?_, rfl⟩
  simpa [scalarFour, Matrix.scalar, Matrix.det_diagonal, Fin.prod_univ_three, pow_succ]
    using (scalarFour r hr).property
theorem native_parabolic_eq_local (b : Bool) : parabolic F b = localFactor F b := by
  cases b
  · apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      have h := (mem_lineParabolicSL_iff F g).mp hg
      have hn : g.val 2 2 ≠ 0 := by
        intro hz
        have hh := congrArg (fun a : SL(3,F) => a.val 2 2) (mul_inv_cancel g)
        change (g.val * g⁻¹.val) 2 2 = 1 at hh
        simp [Matrix.mul_apply, Fin.sum_univ_three, h.1, h.2, hz] at hh
      let c := scalarFour (g.val 2 2)⁻¹ (inv_ne_zero hn)
      have hc : c ∈ center SL(3,F) := scalarFour_center _ _
      refine ⟨g*c, ?_, ?_⟩
      · apply (mem_lineLocalSL_iff F _).mpr
        change (g.val * c.val) 2 0 = 0 ∧ (g.val * c.val) 2 1 = 0 ∧ (g.val * c.val) 2 2 = 1
        simp [c,scalarFour,Matrix.scalar,Matrix.mul_diagonal,h.1,h.2,hn]
      · rw [map_mul, show Matrix.PSL3.projection F c = 1 from by
          apply MonoidHom.mem_ker.mp
          rwa [Matrix.PSL3.projection_ker], mul_one]
    · exact Subgroup.map_mono (lineLocalSL_le F)
  · apply le_antisymm
    · rintro _ ⟨g,hg,rfl⟩
      have h := (mem_pointParabolicSL_iff F g).mp hg
      have hn : g.val 0 0 ≠ 0 := by
        intro hz
        have hh := congrArg (fun a : SL(3,F) => a.val 0 0) (inv_mul_cancel g)
        change (g⁻¹.val * g.val) 0 0 = 1 at hh
        simp [Matrix.mul_apply, Fin.sum_univ_three, h.1, h.2, hz] at hh
      let c := scalarFour (g.val 0 0)⁻¹ (inv_ne_zero hn)
      have hc : c ∈ center SL(3,F) := scalarFour_center _ _
      refine ⟨g*c, ?_, ?_⟩
      · apply (mem_pointLocalSL_iff F _).mpr
        change (g.val * c.val) 0 0 = 1 ∧ (g.val * c.val) 1 0 = 0 ∧ (g.val * c.val) 2 0 = 0
        simp [c,scalarFour,Matrix.scalar,Matrix.mul_diagonal,h.1,h.2,hn]
      · rw [map_mul, show Matrix.PSL3.projection F c = 1 from by
          apply MonoidHom.mem_ker.mp
          rwa [Matrix.PSL3.projection_ker], mul_one]
    · exact Subgroup.map_mono (pointLocalSL_le F)

variable {E : Type*} [Group E] [Finite E]

/-- The affine projection on the entire original parabolic preimage. -/
noncomputable def parabolicAffine (f : E →* PSL) (b : Bool) :
    liftedParabolic f b →* Matrix.SL2.Affine F :=
  (localAffine b).toMonoidHom.comp
    (((f.comp (liftedParabolic f b).subtype).codRestrict (localFactor F b)
      (fun x => (native_parabolic_eq_local b).le x.property)))

omit [Finite E] in
theorem parabolicAffine_surjective (f : E →* PSL) (hf : Function.Surjective f) (b : Bool) :
    Function.Surjective (parabolicAffine f b) := by
  intro y
  obtain ⟨x, hx⟩ := hf ((localAffine b).symm y)
  have hp : x ∈ liftedParabolic f b := by
    change f x ∈ parabolic F b
    rw [hx, native_parabolic_eq_local]
    exact ((localAffine b).symm y).property
  refine ⟨⟨x,hp⟩, ?_⟩
  change localAffine b ⟨f x,_⟩ = y
  exact (congrArg (localAffine b) (Subtype.ext hx)).trans ((localAffine b).apply_symm_apply y)

omit [Finite E] in
@[simp] theorem parabolicAffine_ker (f : E →* PSL) (b : Bool) :
    (parabolicAffine f b).ker = f.ker.comap (liftedParabolic f b).subtype := by
  ext x
  change localAffine b ⟨f x,_⟩ = 1 ↔ f x = 1
  rw [← (localAffine b).map_one, (localAffine b).injective.eq_iff]
  exact Subtype.ext_iff

/-- The full parabolic's original two-core is elementary. -/
theorem parabolicCore_elementary
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀z ∈ f.ker, z ^ 2 = 1) (b : Bool) :
    IsElementaryAbelian 2 (pCore 2 (liftedParabolic f b)) := by
  have hk : IsPGroup 2 f.ker := fun z => ⟨1, by simpa using Subtype.ext (hs z z.property)⟩
  have hpk : IsPGroup 2 (parabolicAffine f b).ker := by
    rw [parabolicAffine_ker]
    exact hk.comap_of_injective _ (liftedParabolic f b).subtype_injective
  have he := (parabolicAffine f b).comap_pCore_of_ker_isPGroup
    (parabolicAffine_surjective f hf b) hpk
  have hpow (x : pCore 2 (liftedParabolic f b)) : x ^ 2 = 1 := by
    have hx := he.ge x.property
    rw [Subgroup.mem_comap, Matrix.SL2.affine_twoCore_eq] at hx
    have hp := elemPow_eq_one_of_isElementaryAbelian (p := 2) _ hx
    change (localAffine b ⟨f x.val.val,_⟩) ^ 2 = 1 at hp
    have hh : (⟨f x.val.val,_⟩ : localFactor F b) ^ 2 = 1 :=
      (localAffine b).injective (by simpa only [map_pow,map_one] using hp)
    have hq : (f x.val.val) ^ 2 = 1 := congrArg Subtype.val hh
    exact Subtype.ext (Subtype.ext
      (ExtendedCentralizer.CoverCentralizers.CentralTwist.square_eq_one_of_elementary_kernel
        f hf hc hs x.val.val hq))
  exact {
    toIsMulCommutative := ⟨⟨fun x y => Commute.of_orderOf_dvd_two
      (fun z => orderOf_dvd_of_pow_eq_one (hpow z)) x y⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }

/-- The full-parabolic Frattini conclusion in I.2.2(3b). -/
theorem parabolicCore_frattini
    (f : E →* PSL) (hf : Function.Surjective f)
    (hc : f.ker ≤ center E) (hs : ∀z ∈ f.ker, z ^ 2 = 1) (b : Bool) :
    frattini (pCore 2 (liftedParabolic f b)) = ⊥ := by
  let := parabolicCore_elementary f hf hc hs b
  let : Fact (IsPGroup 2 (pCore 2 (liftedParabolic f b))) := ⟨pCore_isPGroup⟩
  exact frattini_eq_bot_of_isElementaryAbelian (p := 2)

/-- Literal source application, without assumptions about the size of Z. -/
theorem source_parabolicCore_frattini
    (e : (E ⧸ center E) ≃* PSL)
    (hz : IsPGroup 2 (center E)) (hphi : frattini (center E) = ⊥) (b : Bool) :
    frattini (pCore 2 (liftedParabolic (centerProjection e) b)) = ⊥ := by
  let : Fact (IsPGroup 2 (center E)) := ⟨hz⟩
  let : IsElementaryAbelian 2 (center E) :=
    (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp hphi
  apply parabolicCore_frattini (centerProjection e) (centerProjection_surjective e)
    (by rw [centerProjection_ker]) _ b
  intro z hz
  rw [centerProjection_ker] at hz
  exact elemPow_eq_one_of_isElementaryAbelian z hz

end Matrix.PSL3Four.ElementaryParabolic
end

