module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic.Alignment
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Terminal.PlaneGeometry

/-!
# The forward point-or-plane alternatives in the even critical pair

Every nonidentity point-radical matrix moves the full point. On the point
hyperplane its displacement lies in the point, with equality when it moves
that hyperplane. The explicit Levi alignment then places a noncentral actor
so that its fixed space bounds the original plane and its displacement
contains that plane. Mutual quadraticity makes these bounds equalities.

The correction is an actual element of L₁. We retain containment in R₁,
noncommutation, and the commutator-intersection bound under that correction.
The earlier PointCoordinates premise includes the actual R₁ action; it is
not yet constructed here. The common field line on the reverse module is
also a separate obligation.
Source: Aschbacher--Smith, 11.5.8, refs/quasithin.pdf, printed p.784.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup
open Theory.SpecificGroups.SymplecticFour
open CFSG.Quasithin.Chapter12.Section02
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
open Closure.Symplectic Closure.Symplectic.Terminal
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} {E : Geometry D}

private theorem radical_displacement_three {F : Type*} [Field F] [CharP F 2]
    (u v z : F) (x : Vector F) (hx : x (.inr 0) = 0) :
    PlaneModel.radical u v z • x - x ∈ point F := by
  rw [PlaneModel.radical_apply, mem_point_iff]
  constructor
  · simp [hx]
  · intro i
    fin_cases i <;> simp [hx]

private theorem radical_point_surjective {F : Type*} [Field F] [CharP F 2]
    (u v z : F) (hne : u ≠ 0 ∨ v ≠ 0 ∨ z ≠ 0)
    (x : Vector F) (hx : x ∈ point F) :
    ∃ y : Vector F, PlaneModel.radical u v z • y - y = x := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rcases hne with hu | hv | hz
  · refine ⟨Pi.single (.inr 1) (a / u), ?_⟩
    rw [PlaneModel.radical_apply]
    ext i
    fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e, hu, mul_div_cancel₀]
  · refine ⟨Pi.single (.inl 1) (a / v), ?_⟩
    rw [PlaneModel.radical_apply]
    ext i
    fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e, hv, mul_div_cancel₀]
  · by_cases hu : u = 0
    · by_cases hv : v = 0
      · refine ⟨Pi.single (.inr 0) (a / z), ?_⟩
        rw [PlaneModel.radical_apply]
        ext i
        fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e, hu, hv, hz, mul_div_cancel₀]
      · refine ⟨Pi.single (.inl 1) (a / v), ?_⟩
        rw [PlaneModel.radical_apply]
        ext i
        fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e, hv, mul_div_cancel₀]
    · refine ⟨Pi.single (.inr 1) (a / u), ?_⟩
      rw [PlaneModel.radical_apply]
      ext i
      fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e, hu, mul_div_cancel₀]

variable (m : MarkedFlag E) (p : PointCoordinates E m)
  (hc : V ⊓ centralizer (L : Set G) = ⊥)

include m p hc in
/-- Every nontrivial original radical action moves the entire original point. -/
theorem point_le_commutator (A : Subgroup G) (hA : A ≤ E.R₁)
    (hn : ⁅V, A⁆ ≠ ⊥) : E.V₁ ≤ ⁅V, A⁆ := by
  let π := markedProjection E m p.basis
  have hi := markedProjection_injective E m p.basis hc
  have hbad : ¬ A ≤ centralizer (V : Set G) := by
    intro h
    exact hn (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp h))
  obtain ⟨a, ha, han⟩ := SetLike.not_le_iff_exists.mp hbad
  let aN : normalizer (V : Set G) := ⟨a, radical_normalizes_seed E (hA ha)⟩
  obtain ⟨u,v,z,hr⟩ := p.radical ⟨a,hA ha⟩
  have hne : u ≠ 0 ∨ v ≠ 0 ∨ z ≠ 0 := by
    by_contra! hz
    apply han
    intro x hx
    have he : V.normalizerMonoidHom aN ⟨x,hx⟩ = ⟨x,hx⟩ := by
      apply hi
      apply Multiplicative.toAdd.injective
      rw [hr, hz.1, hz.2.1, hz.2.2, PlaneModel.radical_apply]
      ext i
      fin_cases i <;> simp
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  intro x hx
  let xV : V := ⟨x, E.V₁_le hx⟩
  obtain ⟨w,hw⟩ := radical_point_surjective u v z hne (π xV).toAdd
    ((p.point xV).mp hx)
  obtain ⟨y,hy⟩ := markedProjection_surjective E m p.basis (Multiplicative.ofAdd w)
  change π y = Multiplicative.ofAdd w at hy
  let d : V := V.normalizerMonoidHom aN y * y⁻¹
  have he : d = xV := by
    apply hi
    apply Multiplicative.toAdd.injective
    change (π (V.normalizerMonoidHom aN y * y⁻¹)).toAdd = _
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,hr]
    change PlaneModel.radical u v z • (π y).toAdd + -(π y).toAdd = (π xV).toAdd
    simpa only [hy,toAdd_ofAdd,sub_eq_add_neg] using hw
  have hm : d.val ∈ ⁅V,A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator ha y.property
  rwa [he] at hm

include m p in
/-- Restriction to the actual point hyperplane has displacement in the point. -/
theorem threeSpace_commutator_le_point (A : Subgroup G) (hA : A ≤ E.R₁) :
    ⁅E.V₃,A⁆ ≤ E.V₁ := by
  let π := markedProjection E m p.basis
  rw [commutator_comm]
  apply commutator_le.mpr
  intro a ha x hx
  let aN : normalizer (V : Set G) := ⟨a,radical_normalizes_seed E (hA ha)⟩
  obtain ⟨u,v,z,hr⟩ := p.radical ⟨a,hA ha⟩
  let xV : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
  let d : V := V.normalizerMonoidHom aN xV * xV⁻¹
  change (d : G) ∈ E.V₁
  apply (p.point d).mpr
  change (π d).toAdd ∈ _
  simp only [d,map_mul,map_inv,toAdd_mul,toAdd_inv]
  rw [hr]
  simpa only [sub_eq_add_neg] using radical_displacement_three u v z (π xV).toAdd
    ((p.three xV).mp hx)

private theorem radical_point_from_three {F : Type*} [Field F] [CharP F 2]
    (u v z : F) (hne : u ≠ 0 ∨ v ≠ 0) (x : Vector F) (hx : x ∈ point F) :
    ∃ y : Vector F, y (.inr 0) = 0 ∧ PlaneModel.radical u v z • y - y = x := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  rcases hne with hu | hv
  · refine ⟨Pi.single (.inr 1) (a / u), by simp, ?_⟩
    rw [PlaneModel.radical_apply]
    ext i
    fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e, hu, mul_div_cancel₀]
  · refine ⟨Pi.single (.inl 1) (a / v), by simp, ?_⟩
    rw [PlaneModel.radical_apply]
    ext i
    fin_cases i <;> simp [Theory.SpecificGroups.SymplecticFour.e, hv, mul_div_cancel₀]

include m p hc in
/-- A radical actor moving V₃ has precisely V₁ as its hyperplane commutator. -/
theorem threeSpace_commutator_eq_point (A : Subgroup G) (hA : A ≤ E.R₁)
    (hn : ¬ A ≤ centralizer (E.V₃ : Set G)) : ⁅E.V₃,A⁆ = E.V₁ := by
  let π := markedProjection E m p.basis
  have hi := markedProjection_injective E m p.basis hc
  apply le_antisymm (threeSpace_commutator_le_point m p A hA)
  obtain ⟨a, ha, han⟩ := SetLike.not_le_iff_exists.mp hn
  let aN : normalizer (V : Set G) := ⟨a, radical_normalizes_seed E (hA ha)⟩
  obtain ⟨u,v,z,hr⟩ := p.radical ⟨a,hA ha⟩
  have hne : u ≠ 0 ∨ v ≠ 0 := by
    by_contra! hz
    apply han
    intro x hx
    let xV : V := ⟨x,D.centralQuotientPreimage_le _ hx⟩
    have he : V.normalizerMonoidHom aN xV = xV := by
      apply hi
      apply Multiplicative.toAdd.injective
      rw [hr, hz.1, hz.2]
      exact PlaneModel.central_fixes_three z _ ((p.three xV).mp hx)
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  intro x hx
  let xV : V := ⟨x,E.V₁_le hx⟩
  obtain ⟨w,hw3,hw⟩ := radical_point_from_three u v z hne (π xV).toAdd
    ((p.point xV).mp hx)
  obtain ⟨y,hy⟩ := markedProjection_surjective E m p.basis (Multiplicative.ofAdd w)
  change π y = Multiplicative.ofAdd w at hy
  have hy3 : (y : G) ∈ E.V₃ := (p.three y).mpr (by
    change (π y).toAdd (.inr 0) = 0
    rw [hy]
    exact hw3)
  let d : V := V.normalizerMonoidHom aN y * y⁻¹
  have he : d = xV := by
    apply hi
    apply Multiplicative.toAdd.injective
    change (π (V.normalizerMonoidHom aN y * y⁻¹)).toAdd = _
    rw [map_mul,map_inv,toAdd_mul,toAdd_inv,hr]
    change PlaneModel.radical u v z • (π y).toAdd + -(π y).toAdd = (π xV).toAdd
    simpa only [hy,toAdd_ofAdd,sub_eq_add_neg] using hw
  have hm : d.val ∈ ⁅E.V₃,A⁆ := by
    rw [commutator_comm]
    exact commutator_mem_commutator ha hy3
  rwa [he] at hm

/-- An L₁ correction keeps the critical pair inside the same radical. -/
theorem corrected_pair (g a : G) (ha : a ∈ E.L₁)
    (hB : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hn : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    V.map (MulAut.conj (a*g)).toMonoidHom ≤ E.R₁ ∧
      ⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ ≤
        V ⊓ V.map (MulAut.conj (a*g)).toMonoidHom := by
  have hv : V.map (MulAut.conj a).toMonoidHom = V :=
    mem_normalizer_iff_map_conj_eq.mp (D.normalizes (E.L₁_le ha))
  have hrn : E.L₁ ≤ normalizer (E.R₁ : Set G) :=
    (le_sup_left.trans (E.L₁ ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hr : E.R₁.map (MulAut.conj a).toMonoidHom = E.R₁ :=
    mem_normalizer_iff_map_conj_eq.mp (hrn ha)
  rw [map_conj_mul]
  refine ⟨?_, ?_, ?_⟩
  · exact hr ▸ map_mono hB
  · intro hz
    apply hn
    apply (map_eq_bot_iff_of_injective (f := (MulAut.conj a).toMonoidHom)
      _ (MulAut.conj a).injective).mp
    rw [map_commutator, hv, hz]
  · have hh := map_mono (f := (MulAut.conj a).toMonoidHom) hi
    rw [map_commutator, map_inf _ _ _ (MulAut.conj a).injective, hv] at hh
    exact hh

include m p hc in
/-- The literal point-or-plane alternatives, conditional only on the earlier
point-radical coordinates. The reverse field-line calculation is separate. -/
theorem forward_alternatives (g : G)
    (hB : V.map (MulAut.conj g).toMonoidHom ≤ E.R₁)
    (hn : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥)
    (hi : ⁅V,V.map (MulAut.conj g).toMonoidHom⁆ ≤
      V ⊓ V.map (MulAut.conj g).toMonoidHom) :
    ∃ a ∈ E.L₁, V.map (MulAut.conj (a*g)).toMonoidHom ≤ E.R₁ ∧
      ⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ ≠ ⊥ ∧
      ⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ ≤
        V ⊓ V.map (MulAut.conj (a*g)).toMonoidHom ∧
      (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁ ∨
        (⁅V,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₂ ∧
          ⁅E.V₃,V.map (MulAut.conj (a*g)).toMonoidHom⁆ = E.V₁)) := by
  let B := V.map (MulAut.conj g).toMonoidHom
  by_cases hz : B ≤ centralizer (E.V₃ : Set G)
  · refine ⟨1, E.L₁.one_mem, ?_⟩
    simp only [one_mul]
    exact ⟨hB,hn,hi,Or.inl (le_antisymm (p.commutator_le_point B hB hz)
      (point_le_commutator m p hc B hB hn))⟩
  · obtain ⟨a,ha,hfix,hmove⟩ := p.align hc B hB hz
    have hp := corrected_pair g a ha hB hn hi
    have he : V.map (MulAut.conj (a*g)).toMonoidHom =
      B.map (MulAut.conj a).toMonoidHom := map_conj_mul V a g
    rw [← he] at hfix hmove
    let B' := V.map (MulAut.conj (a*g)).toMonoidHom
    let := D.elementary
    let : IsElementaryAbelian 2 B' := IsElementaryAbelian.map _
    have hplane : ⁅V,B'⁆ = E.V₂ := le_antisymm
      (hp.2.2.trans ((inf_le_inf_left V B'.le_centralizer).trans hfix)) hmove
    have hbad : ¬ B' ≤ centralizer (E.V₃ : Set G) := by
      intro h
      have hh := p.commutator_le_point B' hp.1 h
      rw [hplane, m.plane_preimage, m.point_preimage] at hh
      have hs := (LocalGeometry.Coordinates.sp4 m.action).preimage_le_iff _ _ |>.mp hh
      let : Module.Finite E.input.field.Carrier (LocalGeometry.Coordinates.sp4 m.action).Space :=
        inferInstanceAs (Module.Finite E.input.field.Carrier (Vector E.input.field.Carrier))
      have hd := Submodule.finrank_mono hs
      rw [m.flag.dimension 1, m.flag.dimension 0] at hd
      norm_num at hd
    exact ⟨a,ha,hp.1,hp.2.1,hp.2.2,Or.inr ⟨hplane,
      threeSpace_commutator_eq_point m p hc B' hp.1 hbad⟩⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Amalgam.Even.Symplectic
