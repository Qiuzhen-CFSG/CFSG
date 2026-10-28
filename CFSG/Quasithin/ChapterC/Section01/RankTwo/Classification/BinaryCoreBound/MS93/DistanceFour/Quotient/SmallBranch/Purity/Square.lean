module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Purity.FixedKernel
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.AbelianCore.QuotientRecognition.Multiplicity

/-!
# Removing the fixed kernel through the binary square obstruction

Fixed lifts lie in Z by the starred-intersection argument. They are central
in the core and have exponent two, so squares descend through a quotient by the
full fixed space. Their values lie in the actual natural U-layer.

For one homogeneous copy, normalize its original marking relative to U.
The natural-to-natural square map is additive, while the dual-to-natural map
vanishes. Either conclusion makes the core abelian, contradicting the proved
geometric noncommutativity. Thus the FF multiplicity is two. The dimension-six
bound then forces its fixed kernel to be zero.

This proves fixed-space purity for the supplied CoreModule and ModuleQuotient.
It does not establish the small-intersection branch: its geometric argument
must still exclude the two-copy case. No quotient order or fixed-space equality
is assumed here.

Source: Meierfrankenfeld--Stellmacher (1993), (1.4), p.842, and the binary
square-map argument of (4.6.11), p.909. The six-dimensional FF bound is the
proved binary module estimate in AbelianCore.QuotientRecognition.ExtensionControl.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (d : CoreModule source)

omit [Finite M] in
private theorem multiplicity_one_or_two (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m) :
    m = 1 ∨ m = 2 := q.multiplicity_cases d.faithful d.offending


open Linear

include common radius in
private theorem central_quotient_impossible
    (q : core R (alpha R) →* Multiplicative W) (hq : Function.Surjective q)
    (hk : q.ker ≤ (Z R (alpha R)).subgroupOf (core R (alpha R)))
    (ha : (∀ (m : M) (x : core R (alpha R)),
        (q (coreAction (R := R) m x)).toAdd =
          (common.natural.marking (source.projection m)).val.mulVec (q x).toAdd) ∨
      (∀ (m : M) (x : core R (alpha R)),
        (q (coreAction (R := R) m x)).toAdd =
          dual (common.natural.marking (source.projection m)) (q x).toAdd)) : False := by
  let K := (U R (alpha R)).subgroupOf (core R (alpha R))
  let e : K ≃* Multiplicative W :=
    (subgroupOfEquivOfLe (U_le_core source geometry common)).trans common.natural.equiv
  have hs (x : core R (alpha R)) : x ^ 2 ∈ K :=
    core_square_mem_U geometry radius (alpha R) rfl x
  have he (m : M) (x y : K) (hy : (y : core R (alpha R)) = coreAction (R := R) m x) :
      (e y).toAdd = (common.natural.marking (source.projection m)).val.mulVec (e x).toAdd := by
    apply common.natural.action
    exact congrArg Subtype.val hy
  have hk2 (x : q.ker) : (x : core R (alpha R)) ^ 2 = 1 := by
    apply Subtype.ext
    have hz := hk x.property
    change ((x : core R (alpha R)) : FreeAmalgam R) ∈ Z R (alpha R) at hz
    rw [← common.X_eq_Z (alpha R) rfl] at hz
    exact (mem_omegaCenter_iff.mp hz).2.1
  have hkc : q.ker ≤ center (core R (alpha R)) := by
    intro x hx
    have hb := Flags.Z_le_B geometry (alpha R)
      (geometry.V_local _ rfl common.large_distance) (hk hx)
    rw [radius.B_eq_center (alpha R) rfl] at hb
    obtain ⟨z, hz, hzx⟩ := hb
    change (z : FreeAmalgam R) = (x : FreeAmalgam R) at hzx
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    have hh := congrArg Subtype.val ((mem_center_iff.mp hz)
      ⟨y, radius.core_le_radius _ rfl y.property⟩)
    simpa only [coe_mul, hzx] using hh
  have hconst {x y : core R (alpha R)} (h : q x = q y) : x ^ 2 = y ^ 2 := by
    let c := x * y⁻¹
    have hc : c ∈ q.ker := by
      change q (x * y⁻¹) = 1
      rw [map_mul, map_inv, h, mul_inv_cancel]
    have hc2 := hk2 ⟨c, hc⟩
    have hcomm : Commute c y := (mem_center_iff.mp (hkc hc) y).symm
    have hxy : x = c * y := by simp [c]
    rw [hxy, hcomm.mul_pow, hc2, one_mul]
  let f : W → W := fun v =>
    (e ⟨(Classical.choose (hq (Multiplicative.ofAdd v))) ^ 2, hs _⟩).toAdd
  have hf (x : core R (alpha R)) : f (q x).toAdd = (e ⟨x ^ 2, hs x⟩).toAdd := by
    dsimp only [f]
    congr 2
    apply Subtype.ext
    exact hconst (Classical.choose_spec (hq _))
  apply core_not_commutative source geometry common radius
  rcases ha with ha | ha
  · have heq (g : S) (v : W) : f (g.val.mulVec v) = g.val.mulVec (f v) := by
      obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
      have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
      obtain ⟨x, hx⟩ := hq (Multiplicative.ofAdd v)
      have hv : (q x).toAdd = v := congrArg Multiplicative.toAdd hx
      have hact := ha m x
      rw [hmg] at hact
      rw [← hv, ← hact, hf, hf, ← hmg]
      apply he
      exact (map_pow (coreAction (R := R) m) x 2).symm
    exact ⟨⟨commutative_of_natural_square_map q K e hs f hf heq⟩⟩
  · have heq (g : S) (v : W) : f (dual g v) = g.val.mulVec (f v) := by
      obtain ⟨m, hm⟩ := source.projection_surjective (common.natural.marking.symm g)
      have hmg : common.natural.marking (source.projection m) = g := by simp [hm]
      obtain ⟨x, hx⟩ := hq (Multiplicative.ofAdd v)
      have hv : (q x).toAdd = v := congrArg Multiplicative.toAdd hx
      have hact := ha m x
      rw [hmg] at hact
      rw [← hv, ← hact, hf, hf, ← hmg]
      apply he
      exact (map_pow (coreAction (R := R) m) x 2).symm
    have hsq1 (x : core R (alpha R)) : x ^ 2 = 1 := by
      have hz := equivariantDualMap_zero f heq (q x).toAdd
      rw [hf] at hz
      have hh : e ⟨x ^ 2, hs x⟩ = 1 := congrArg Multiplicative.ofAdd hz
      exact congrArg Subtype.val (e.injective (hh.trans e.map_one.symm))
    refine ⟨⟨fun x y => ?_⟩⟩
    have hinv (z : core R (alpha R)) : z⁻¹ = z :=
      inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hsq1 z)
    calc
      x * y = (x * y)⁻¹ := (hinv (x * y)).symm
      _ = y * x := by rw [mul_inv_rev, hinv x, hinv y]

include common radius in
/-- Even allowing a fixed kernel, a single homogeneous copy contradicts the
actual noncommutativity of the radius-four core. Both markings are retained. -/
theorem one_copy_impossible
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation 1) : False := by
  let ev : (Fin 1 → W) ≃ₗ[ZMod 2] W := LinearEquiv.funUnique (Fin 1) (ZMod 2) W
  let f : d.Space →ₗ[ZMod 2] W := ev.toLinearMap.comp q.projection
  let qm : core R (alpha R) →* Multiplicative W :=
    f.toAddMonoidHom.toMultiplicative.comp d.projection
  have hqm : Function.Surjective qm := ev.surjective.comp (q.surjective.comp d.onto)
  have hker : qm.ker ≤ (Z R (alpha R)).subgroupOf (core R (alpha R)) := by
    intro x hx
    apply fixed_lift_mem_Z source geometry common radius d x
    rw [← q.kernel]
    apply ev.injective
    change f (d.projection x).toAdd = ev 0
    rw [map_zero]
    exact congrArg Multiplicative.toAdd hx
  have hact (m : M) (x : core R (alpha R)) :
      (qm (coreAction (R := R) m x)).toAdd =
        (q.marking (source.projection m)).val.mulVec (qm x).toAdd := by
    change q.projection (d.projection (coreAction (R := R) m x)).toAdd 0 =
      (q.marking (source.projection m)).val.mulVec (q.projection (d.projection x).toAdd 0)
    rw [d.action m x _ rfl]
    exact q.equivariant _ _ 0
  let a : SL ≃* SL := common.natural.marking.symm.trans q.marking
  obtain ⟨e, he⟩ := marking_coordinates a
  let em : Multiplicative W ≃* Multiplicative W := e.toAddEquiv.toMultiplicative
  let qm' := em.toMonoidHom.comp qm
  have hqm' : Function.Surjective qm' := em.surjective.comp hqm
  have hker' : qm'.ker ≤ (Z R (alpha R)).subgroupOf (core R (alpha R)) := by
    rw [MonoidHom.ker_comp_of_injective qm em.toMonoidHom em.injective]
    exact hker
  have heq (m : M) : a (common.natural.marking (source.projection m)) =
      q.marking (source.projection m) := by simp [a]
  apply central_quotient_impossible source geometry common radius qm' hqm' hker'
  rcases he with he | he
  · left
    intro m x
    change e (qm (coreAction (R := R) m x)).toAdd =
      (common.natural.marking (source.projection m)).val.mulVec (e (qm x).toAdd)
    rw [hact, ← heq]
    exact he _ _
  · right
    intro m x
    change e (qm (coreAction (R := R) m x)).toAdd =
      dual (common.natural.marking (source.projection m)) (e (qm x).toAdd)
    rw [hact, ← heq]
    exact he _ _

include common radius in
/-- The one-or-two FF bound and the square obstruction leave exactly two copies.
This uses no small-intersection hypothesis. -/
theorem multiplicity_eq_two (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m) : m = 2 := by
  rcases multiplicity_one_or_two source d m q with rfl | hm
  · exact (one_copy_impossible source geometry common radius d q).elim
  · exact hm


include common radius in
/-- The six-dimensional FF bound removes the fixed kernel after the geometric
square argument has forced two natural copies. -/
theorem no_fixed (m : ℕ)
    (q : AbelianCore.QuotientRecognition.ModuleQuotient d.representation m) :
    fixedSpace d.representation ⊤ = ⊥ := by
  have hm := multiplicity_eq_two source geometry common radius d m q
  subst m
  have hd := AbelianCore.QuotientRecognition.ExtensionControl.finrank_le_six
    d.representation d.full d.offending
  have hr := LinearMap.finrank_range_add_finrank_ker q.projection
  rw [LinearMap.range_eq_top.mpr q.surjective, finrank_top, q.kernel] at hr
  have hw : Module.finrank (ZMod 2) (Fin 2 → W) = 6 := by
    simp [W, Module.finrank_pi_fintype]
  rw [hw] at hr
  exact Submodule.finrank_eq_zero.mp (by omega)


end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
