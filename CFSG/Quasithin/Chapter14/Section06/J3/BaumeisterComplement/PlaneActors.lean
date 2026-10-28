module
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.LocalSixteen.PlaneNatural
public import Theory.SpecificGroups.GL2.DiagonalSwap
public import CFSG.Quasithin.ChapterI.Section04To05.Janko23.J3Recognition.Ambient.CubicCentralizer

/-!
# Cubic fusion witnesses in the original natural plane complement

For a central cubic scalar a in GL₂(4), take the independent cubic
σ = diag(a,a⁻¹) and its coordinate-swap inverter. The product aσ fixes
the second basis vector, which is an involution in the additive plane.
Transport through the literal natural-action equation supplies all three
source actors in G, with the original cubic unchanged. No complement in
an H-type involution centralizer is assumed.

Source: Baumeister, A geometry for groups of J₃-type (2007), final
paragraph of Lemma 2.4, printed pp.495–496.
-/


open Subgroup
open Representation.CentralCubicNaturalFour
open Matrix.GeneralLinearGroup
namespace CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
public noncomputable section

private theorem scalar_injective : Function.Injective
    (scalar (Fin 2) : Representation.SL2FourNatural.Fˣ →* LinearGroup) := by
  intro a b h
  apply Units.ext
  simpa using congrArg (fun A : LinearGroup => A.val 0 0) h

/-- Diagonal and swap matrices supply exactly the actors used in Baumeister 2.4. -/
theorem natural_cubic_actors (z : LinearGroup) (hz : z ∈ center LinearGroup)
    (hz3 : orderOf z = 3) :
    ∃ σ r : LinearGroup, ∃ x : Plane,
      orderOf σ = 3 ∧ orderOf r = 2 ∧ orderOf x = 2 ∧
      Commute z σ ∧ Commute r z ∧ r * σ * r⁻¹ = σ⁻¹ ∧
      naturalAction (z * σ) x = x := by
  let F := Representation.SL2FourNatural.F
  rw [center_eq_range_scalar] at hz
  obtain ⟨a,rfl⟩ := hz
  have ha : orderOf a = 3 := (orderOf_injective _ scalar_injective a).symm.trans hz3
  let σ := diagonalPair F (a,a⁻¹)
  let r := coordinateSwap F
  let x : Plane := Multiplicative.ofAdd ![0,1]
  have hσ : orderOf σ = 3 := by
    apply orderOf_eq_prime
    · change diagonalPair F (a,a⁻¹) ^ 3 = 1
      rw [← map_pow]
      have hp : (a,a⁻¹) ^ 3 = (1 : Fˣ × Fˣ) := by
        ext <;> simp [← ha, pow_orderOf_eq_one]
      rw [hp,map_one]
    · intro h
      have hh : a = 1 := congrArg Prod.fst
        ((diagonalPair_injective F) (h.trans (map_one _).symm))
      simp [hh] at ha
  refine ⟨σ,r,x,hσ,?_,?_,?_,?_,?_,?_⟩
  · apply orderOf_eq_prime (coordinateSwap_sq F)
    intro h
    have hh := congrArg (fun A : LinearGroup => A.val 0 1) h
    exact one_ne_zero hh
  · apply orderOf_eq_prime <;> decide +kernel
  · exact scalar_commute a σ
  · exact (scalar_commute a r).symm
  · change coordinateSwap F * diagonalPair F (a,a⁻¹) * (coordinateSwap F)⁻¹ = _
    rw [coordinateSwap_conj_diagonalPair,← map_inv]
    simp only [Prod.inv_mk, inv_inv]
  · change naturalAction (scalar (Fin 2) a * diagonalPair F (a,a⁻¹))
        (Multiplicative.ofAdd ![0,1]) = _
    apply Multiplicative.toAdd.injective
    change (((scalar (Fin 2) a * diagonalPair F (a,a⁻¹)).val).mulVec ![0,1]) = ![0,1]
    funext i
    fin_cases i <;>
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        diagonalPair, scalar, Matrix.mul_apply, Matrix.scalar_apply]

variable {G : Type*} [Group G]

/-- Transport these actors through the actual natural action of a plane complement. -/
theorem plane_complement_cubic_actors
    (A : Subgroup G) (C : Subgroup (normalizer (A : Set G)))
    (f : C ≃* LinearGroup) (a : A ≃* Plane)
    (ha : ∀ (c : C) (x : A),
      a (A.normalizerMonoidHom c x) = naturalAction (f c) (a x))
    (s : C) (hsc : s ∈ center C) (hs : orderOf s = 3) :
    let u : G := ((s : normalizer (A : Set G)) : G)
    ∃ (σ : centralizer ({u} : Set G)) (r t : G),
      orderOf σ = 3 ∧ σ ∉ cubicKernel u ∧ orderOf r = 2 ∧ orderOf t = 2 ∧
      Commute r u ∧ r * (σ : G) * r⁻¹ = (σ : G)⁻¹ ∧
      Commute (u * (σ : G)) t := by
  let j : C →* G := (normalizer (A : Set G)).subtype.comp C.subtype
  have hj : Function.Injective j :=
    (normalizer (A : Set G)).subtype_injective.comp C.subtype_injective
  have hfs : f s ∈ center LinearGroup := by
    apply mem_center_iff.mpr
    intro y
    obtain ⟨c,rfl⟩ := f.surjective y
    rw [← map_mul,← map_mul,mem_center_iff.mp hsc c]
  obtain ⟨σ,r,x,hσ,hr,hx,hcomm,hrz,hri,hfix⟩ :=
    natural_cubic_actors (f s) hfs ((f.orderOf_eq s).trans hs)
  let b := f.symm σ
  let v := f.symm r
  have hbs : Commute (j b) (j s) := by
    apply Commute.map
    exact mem_center_iff.mp hsc b
  let σG : centralizer ({j s} : Set G) :=
    ⟨j b,mem_centralizer_singleton_iff.mpr hbs.eq⟩
  have hb3 : orderOf σG = 3 := (orderOf_coe σG).symm.trans
    ((orderOf_injective j hj b).trans ((f.symm.orderOf_eq σ).trans hσ))
  have hv2 : orderOf (j v) = 2 :=
    (orderOf_injective j hj v).trans ((f.symm.orderOf_eq r).trans hr)
  have hvs : Commute (j v) (j s) := by
    apply Commute.map
    apply f.injective
    simpa only [map_mul,v,f.apply_symm_apply] using hrz.eq
  have hvi : j v * j b * (j v)⁻¹ = (j b)⁻¹ := by
    have hh : v * b * v⁻¹ = b⁻¹ := by
      apply f.injective
      simpa only [map_mul,map_inv,v,b,f.apply_symm_apply] using hri
    simpa only [map_mul,map_inv] using congrArg j hh
  refine ⟨σG,j v,(a.symm x : G),hb3,?_,hv2,?_,hvs,hvi,?_⟩
  · intro hK
    have hle : zpowers (j s) ≤ centralizer ({j v} : Set G) :=
      zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hvs.symm.eq)
    have hcb := mem_centralizer_singleton_iff.mp (hle hK)
    change j b * j v = j v * j b at hcb
    have hbeq : j b = (j b)⁻¹ := by
      rw [hcb.symm,mul_inv_cancel_right] at hvi
      exact hvi
    have hb2 : (j b)^2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hbeq]
      exact inv_mul_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hb2
    have hbG : orderOf (j b) = 3 := (orderOf_coe σG).trans hb3
    norm_num [hbG] at hd
  · exact (orderOf_coe _).trans ((a.symm.orderOf_eq x).trans hx)
  · have hh : A.normalizerMonoidHom (s*b) (a.symm x) = a.symm x := by
      apply a.injective
      calc
        a (A.normalizerMonoidHom (s*b) (a.symm x)) =
            naturalAction (f (s*b)) (a (a.symm x)) := ha (s*b) (a.symm x)
        _ = a (a.symm x) := by
          simpa only [map_mul,b,f.apply_symm_apply,a.apply_symm_apply] using hfix
    have hhG := congrArg Subtype.val hh
    change (j s * j b) * (a.symm x : G) * (j s * j b)⁻¹ = (a.symm x : G) at hhG
    exact mul_inv_eq_iff_eq_mul.mp hhG
end
end CFSG.Quasithin.Janko23.J3Recognition.Ambient.BaumeisterComplement
