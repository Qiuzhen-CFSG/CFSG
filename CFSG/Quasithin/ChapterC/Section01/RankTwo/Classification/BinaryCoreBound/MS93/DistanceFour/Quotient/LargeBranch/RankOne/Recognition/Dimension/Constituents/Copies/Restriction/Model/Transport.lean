module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Dimension.Constituents.Copies.Restriction.Geometry
public import Theory.GroupTheory.NormalSymmetricThreePairRank.Inner
public import Theory.GroupTheory.SpecificGroups.SLTwoPermThree

/-!
# Transport for the homogeneous parabolic restriction calculation

The finite calculations can use the coordinate flag and any actual rank-one
quotient with the correct kernel. Every automorphism of SL₂(2) is inner, so a
single matrix change of coordinates matches that quotient to any prescribed
surjection with the same kernel. The change intertwines the full group.

Equivariant linear maps transport literal orbit spans. Representation operators
then remove flag conjugation, and genuine representation equivalences transport
the resulting coordinates to any homogeneous splitting. The standard natural
and dual calculations remain separate inputs to this transport; no module
classification or source theorem is asserted by their specification.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(5), printed pp.911--912.
-/

@[expose] public section
open Subgroup Matrix Representation
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction

private theorem sl2_aut_inner (α : MulAut SL2) : ∃ k, ∀ a, α a = k * a * k⁻¹ := by
  obtain ⟨e⟩ := SLTwoPermThree.sl2Two_equiv_perm_three
  obtain ⟨k, hk⟩ := Theory.GroupTheory.NormalSymmetricThreePairRank.symmetricThree_aut_inner
    (e.symm.trans (α.trans e))
  refine ⟨e.symm k, fun a => ?_⟩
  apply e.injective
  simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply, MulAut.conj_apply] using DFunLike.congr_fun hk (e a)


private theorem quotient_marks_conjugate {G : Type*} [Group G]
    (q r : G →* SL2) (hq : Function.Surjective q) (hr : Function.Surjective r)
    (hk : q.ker = r.ker) : ∃ k : SL2, ∀ a, r a = k * q a * k⁻¹ := by
  let f : SL2 →* SL2 := q.liftOfSurjective hq ⟨r, hk.le⟩
  have hf (a : G) : f (q a) = r a :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have hinj : Function.Injective f := by
    intro x y h
    obtain ⟨a, rfl⟩ := hq x
    obtain ⟨b, rfl⟩ := hq y
    rw [hf, hf] at h
    exact q.eq_iff.mpr (hk.symm ▸ r.eq_iff.mp h)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨a, rfl⟩ := hr x
    exact ⟨q a, hf a⟩
  obtain ⟨k, h⟩ := sl2_aut_inner (MulEquiv.ofBijective f ⟨hinj, hsurj⟩)
  exact ⟨k, fun a => (hf a).symm.trans (h (q a))⟩


variable {V X : Type*} [AddCommGroup V] [Module (ZMod 2) V]
  [AddCommGroup X] [Module (ZMod 2) X]

/-- Full SL₂(2) coordinates on the specified adjacent orbit span. -/
def OrbitCoordinates (ρ : Representation (ZMod 2) SL V) (H : Subgroup SL)
    (E : Submodule (ZMod 2) V) (q : H →* SL2) : Prop :=
  ∃ e : Seed.orbitSpace ρ H E ≃ₗ[ZMod 2] (Fin 2 → Fin 2 → ZMod 2),
    ∀ (a : H) (v w : Seed.orbitSpace ρ H E),
      (w : V) = ρ a.val (v : V) → ∀ j : Fin 2,
        e w j = (q a).val.mulVec (e v j)

theorem orbit_coordinates_change_quotient
    (ρ : Representation (ZMod 2) SL V) (H : Subgroup SL)
    (E : Submodule (ZMod 2) V) (q r : H →* SL2)
    (hq : Function.Surjective q) (hr : Function.Surjective r) (hk : q.ker = r.ker)
    (he : OrbitCoordinates ρ H E q) : OrbitCoordinates ρ H E r := by
  obtain ⟨e, he⟩ := he
  obtain ⟨k, hk⟩ := quotient_marks_conjugate q r hq hr hk
  let f := e.trans (LinearEquiv.piCongrRight (fun _ : Fin 2 => SpecialLinearGroup.toLin' k))
  refine ⟨f, fun a v w hw j => ?_⟩
  change k.val.mulVec (e w j) = (r a).val.mulVec (k.val.mulVec (e v j))
  rw [he a v w hw, hk]
  change k.val.mulVec ((q a).val.mulVec (e v j)) =
    (k.val * (q a).val * k⁻¹.val).mulVec (k.val.mulVec (e v j))
  simp only [Matrix.mulVec_mulVec]
  congr 1
  change _ = ((k * q a * k⁻¹) * k).val
  simp only [mul_assoc, inv_mul_cancel, mul_one]
  rfl

theorem orbitSpace_map_twist
    (ρ : Representation (ZMod 2) SL V) (σ : Representation (ZMod 2) SL X)
    (α : MulAut SL) (l : V →ₗ[ZMod 2] X)
    (hl : ∀ g v, l (ρ g v) = σ (α g) (l v))
    (H : Subgroup SL) (E : Submodule (ZMod 2) V) :
    (Seed.orbitSpace ρ H E).map l =
      Seed.orbitSpace σ (H.map α.toMonoidHom) (E.map l) := by
  unfold Seed.orbitSpace
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨g, hg, v, hv, rfl⟩, rfl⟩
    exact ⟨α g, ⟨g, hg, rfl⟩, l v, ⟨v, hv, rfl⟩, (hl g v).symm⟩
  · rintro ⟨_, ⟨g, hg, rfl⟩, _, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨ρ g v, ⟨g, hg, v, hv, rfl⟩, hl g v⟩

theorem fixedSpace_map_twist
    (ρ : Representation (ZMod 2) SL V) (σ : Representation (ZMod 2) SL X)
    (α : MulAut SL) (l : V →ₗ[ZMod 2] X)
    (hl : ∀ g v, l (ρ g v) = σ (α g) (l v))
    (H : Subgroup SL) (E : Submodule (ZMod 2) V)
    (hE : E ≤ BinaryOffender.fixedSpace ρ H) :
    E.map l ≤ BinaryOffender.fixedSpace σ (H.map α.toMonoidHom) := by
  rintro _ ⟨v, hv, rfl⟩ ⟨_, g, hg, rfl⟩
  change σ (α g) (l v) = l v
  rw [← hl]
  exact congrArg l (hE hv ⟨g, hg⟩)

/-- Transport through actual actor and vector equivalences, retaining every
matrix-parabolic element in the action equation. -/
theorem orbit_coordinates_transport
    (ρ : Representation (ZMod 2) SL V) (σ : Representation (ZMod 2) SL X)
    (α : MulAut SL) (l : V ≃ₗ[ZMod 2] X)
    (hl : ∀ g v, l (ρ g v) = σ (α g) (l v))
    (H K : Subgroup SL) (hK : H.map α.toMonoidHom = K)
    (E : Submodule (ZMod 2) V) (q : K →* SL2)
    (hq : OrbitCoordinates σ K (E.map l.toLinearMap) q) :
    OrbitCoordinates ρ H E
      (q.comp (((H.equivMapOfInjective α.toMonoidHom α.injective).trans
        (MulEquiv.subgroupCongr hK)).toMonoidHom)) := by
  let t : H ≃* K := (H.equivMapOfInjective α.toMonoidHom α.injective).trans
    (MulEquiv.subgroupCongr hK)
  have hA : (Seed.orbitSpace ρ H E).map l.toLinearMap =
      Seed.orbitSpace σ K (E.map l.toLinearMap) := by
    rw [orbitSpace_map_twist ρ σ α l.toLinearMap hl, hK]
  let u := l.ofSubmodules _ _ hA
  obtain ⟨e, he⟩ := hq
  refine ⟨u.trans e, fun a v w hw j => ?_⟩
  exact he (t a) (u v) (u w) (by
    change l (w : V) = σ (α a.val) (l (v : V))
    rw [hw, hl]) j

/-- The point and plane stabilizers of the coordinate flag. -/
abbrev standardParabolic (i : Bool) : Subgroup SL :=
  if i then Matrix.PSL3Two.lineParabolicSL else Matrix.PSL3Two.pointParabolicSL

/-- The standard flag calculation is deliberately separate from conjugation,
quotient marking and homogeneous splitting. Its output includes an actual
surjective rank-one quotient and the full action on its orbit span. -/
def StandardOrbitCalculation (σ : Representation (ZMod 2) SL V) : Prop :=
  ∀ (i : Bool) (E : Submodule (ZMod 2) V),
    E ≤ BinaryOffender.fixedSpace σ (standardParabolic i) →
    Seed.orbitSpace σ ⊤ E = ⊤ →
    ∃ q : standardParabolic (!i) →* SL2,
      Function.Surjective q ∧ q.ker = pCore 2 (standardParabolic (!i)) ∧
        OrbitCoordinates σ (standardParabolic (!i)) E q


private theorem modelParabolic_unconjugate (g : SL) (i : Bool) :
    (modelParabolic g i).map (MulAut.conj g⁻¹).toMonoidHom = standardParabolic i := by
  have hc : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id SL := by
    apply MonoidHom.ext
    intro a
    change g⁻¹ * (g * a * g⁻¹) * (g⁻¹)⁻¹ = a
    simp only [inv_inv, mul_one, mul_assoc, inv_mul_cancel_left,
      inv_mul_cancel]
  simp only [modelParabolic, Subgroup.map_map, hc, Subgroup.map_id]

/-- A calculation at the standard flag determines the result for every
conjugate flag and every surjective marking with the intrinsic two-core kernel. -/
theorem orbit_coordinates_of_standard
    (ρ : Representation (ZMod 2) SL V) (hstandard : StandardOrbitCalculation ρ)
    (flag : SL) (i : Bool) (E : Submodule (ZMod 2) V)
    (hfixed : E ≤ BinaryOffender.fixedSpace ρ (modelParabolic flag i))
    (hgen : Seed.orbitSpace ρ ⊤ E = ⊤)
    (q : modelParabolic flag (!i) →* SL2) (hq : Function.Surjective q)
    (hker : q.ker = pCore 2 (modelParabolic flag (!i))) :
    OrbitCoordinates ρ (modelParabolic flag (!i)) E q := by
  let α : MulAut SL := MulAut.conj flag⁻¹
  let l : V ≃ₗ[ZMod 2] V := LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom flag⁻¹)
  have hl (g : SL) (v : V) : l (ρ g v) = ρ (α g) (l v) := by
    change ρ flag⁻¹ (ρ g v) = ρ (flag⁻¹ * g * (flag⁻¹)⁻¹) (ρ flag⁻¹ v)
    simp only [← Module.End.mul_apply, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
  let E₀ := E.map l.toLinearMap
  have hf₀ : E₀ ≤ BinaryOffender.fixedSpace ρ (standardParabolic i) := by
    have h := fixedSpace_map_twist ρ ρ α l.toLinearMap hl _ E hfixed
    rwa [modelParabolic_unconjugate] at h
  have hg₀ : Seed.orbitSpace ρ ⊤ E₀ = ⊤ := by
    have h := orbitSpace_map_twist ρ ρ α l.toLinearMap hl ⊤ E
    rw [Subgroup.map_top_of_surjective _ α.surjective, hgen] at h
    rw [← h, Submodule.map_top, LinearMap.range_eq_top.mpr l.surjective]
  obtain ⟨q₀, hq₀, hk₀, he₀⟩ := hstandard i E₀ hf₀ hg₀
  let t : modelParabolic flag (!i) ≃* standardParabolic (!i) :=
    ((modelParabolic flag (!i)).equivMapOfInjective α.toMonoidHom α.injective).trans
      (MulEquiv.subgroupCongr (modelParabolic_unconjugate flag (!i)))
  have he : OrbitCoordinates ρ (modelParabolic flag (!i)) E (q₀.comp t.toMonoidHom) :=
    orbit_coordinates_transport ρ ρ α l hl _ _ (modelParabolic_unconjugate flag (!i)) E q₀ he₀
  apply orbit_coordinates_change_quotient ρ _ E (q₀.comp t.toMonoidHom) q
    (hq₀.comp t.surjective) hq _ he
  rw [← MonoidHom.comap_ker, hk₀, hker, ← pCore_map_iso 2 t]
  exact Subgroup.comap_map_eq_self_of_injective t.injective _

/-- Transport from a genuine representation equivalence, without changing
the actor or the prescribed quotient map. -/
theorem orbit_coordinates_of_equiv
    (ρ : Representation (ZMod 2) SL V) (σ : Representation (ZMod 2) SL X)
    (e : ρ.Equiv σ) (H : Subgroup SL) (E : Submodule (ZMod 2) V) (q : H →* SL2)
    (h : OrbitCoordinates σ H (E.map e.toLinearEquiv.toLinearMap) q) :
    OrbitCoordinates ρ H E q := by
  have he (g : SL) (v : V) : e (ρ g v) = σ g (e v) :=
    LinearMap.congr_fun (e.isIntertwining' g) v
  have hA := orbitSpace_map ρ σ e.toLinearEquiv.toLinearMap he H E
  let u := e.toLinearEquiv.ofSubmodules _ _ hA
  obtain ⟨f, hf⟩ := h
  refine ⟨u.trans f, fun a v w hw j => ?_⟩
  exact hf a (u v) (u w) (by
    change e (w : V) = σ a.val (e (v : V))
    rw [hw, he]) j

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Dimension.Restriction
