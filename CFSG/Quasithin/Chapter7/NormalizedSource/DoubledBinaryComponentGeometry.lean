module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
public import Theory.Representation.BinaryNaturalDual.ModelOrbits.Coordinate
-- Internal coordinate transport uses the dot-product implementation and the
-- paired-plane coordinate subspace; neither enters the public statements.
import all Theory.Representation.PSL3Two.AutomorphismAction.NaturalDual
import all CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryPlanes
/-!
# Singular points above a paired plane in the binary doubled orbit

Any subspace properly containing a paired natural–dual plane contains a
singular vector with both coordinates nonzero. These 21 vectors form one
orbit under the original SL₃(2) action. Every two-group of implementing
operators fixes one, and transitivity transports this to any marked singular
vector. On the literal ambient orbit, each such vector is centralized by a
Sylow two-subgroup of G.

The chosen-module application supplies the singular point and its ambient
characteristic-two centralizer in `NonFFSourceDoubledBinaryComponentGeometry`.
The characteristic-two intersection with the escaping H in 7.7.5 and the
component elimination in 7.7.6 remain with qt-d-1222-nonff-doubled.
Source: Aschbacher–Smith, H.4.2 and the component paragraph of 7.7.6,
printed pp.380 and 706, refs/quasithin.pdf.
-/

open Subgroup Representation Representation.BinaryOffender
open BinaryLinearThree NaturalDual
public noncomputable section
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentGeometry

/-- Both marked coordinates are nonzero and have zero evaluation pairing. -/
@[expose] def IsSingular (x : Space) : Prop := x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.2 x.1 = 0

/-- The singular diagonal class has 21 points. -/
theorem singular_card : Nat.card {x : Space // IsSingular x} = 21 := by
  let e := (LinearEquiv.refl (ZMod 2) Vector).prodCongr
    (dotProductEquiv (ZMod 2) (Fin 3)).symm
  have he (x : Space) : IsSingular x ↔
      (e x).1 ≠ 0 ∧ (e x).2 ≠ 0 ∧ (e x).2 ⬝ᵥ (e x).1 = 0 := by
    have hp : ((dotProductEquiv (ZMod 2) (Fin 3)).symm x.2) ⬝ᵥ x.1 = x.2 x.1 := by
      exact LinearMap.congr_fun ((dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply x.2) x.1
    simp [IsSingular,e,hp]
  rw [Nat.card_congr (e.toEquiv.subtypeEquiv (p := IsSingular)
    (q := fun x : Vector × Vector => x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.2 ⬝ᵥ x.1 = 0) he),Nat.card_eq_fintype_card]
  decide

theorem singular_inner (g : Group) (x : Space) (hx : IsSingular x) :
    IsSingular (action g x) := by
  refine ⟨?_,?_,?_⟩
  · intro hz
    apply hx.1
    change W g x.1 = 0 at hz
    have hh := congrArg (W g⁻¹) hz
    simpa only [inv_self_apply,map_zero] using hh
  · intro hz
    apply hx.2.1
    change W.dual g x.2 = 0 at hz
    have hh := congrArg (W.dual g⁻¹) hz
    simpa only [inv_self_apply,map_zero] using hh
  · change x.2 (W g⁻¹ (W g x.1)) = 0
    rw [inv_self_apply,hx.2.2]

theorem singular_graph (x : Space) (hx : IsSingular x) : IsSingular (graphSwap x) := by
  refine ⟨?_,?_,?_⟩
  · change AutomorphismAction.graphNaturalDual.symm.toLinearEquiv x.2 ≠ 0
    exact fun he => hx.2.1 (AutomorphismAction.graphNaturalDual.symm.toLinearEquiv.injective
      (he.trans (map_zero _).symm))
  · change AutomorphismAction.graphNaturalDual.toLinearEquiv x.1 ≠ 0
    exact fun he => hx.1 (AutomorphismAction.graphNaturalDual.toLinearEquiv.injective
      (he.trans (map_zero _).symm))
  · change x.1 ⬝ᵥ ((dotProductEquiv (ZMod 2) (Fin 3)).symm x.2) = 0
    rw [dotProduct_comm]
    have hp := LinearMap.congr_fun
      ((dotProductEquiv (ZMod 2) (Fin 3)).apply_symm_apply x.2) x.1
    exact hp.trans hx.2.2

theorem singular_implementer (α : MulAut Group) (e : Space ≃ₗ[ZMod 2] Space)
    (he : ∀ g x, e (action g x) = action (α g) (e x))
    (x : Space) (hx : IsSingular x) : IsSingular (e x) := by
  by_cases hα : α ∈ MulAut.innerSubgroup Group
  · obtain ⟨g,rfl⟩ := inner_operator α e he hα
    exact singular_inner g x hx
  · obtain ⟨g,rfl⟩ := outer_operator α e he hα
    exact singular_inner g (graphSwap x) (singular_graph x hx)

/-- The original component is transitive on singular diagonal vectors. -/
theorem singular_transitive (x y : Space) (hx : IsSingular x) (hy : IsSingular y) :
    ∃ g : Group, action g x = y := by
  obtain ⟨e,he⟩ := BinaryNaturalDual.ModelOrbits.exists_naturalDual_eq
    hx.1 hy.1 hx.2.1 hy.2.1 (hx.2.2.trans hy.2.2.symm)
  rw [BinaryNaturalDual.naturalDualRepresentation_apply] at he
  have hdet : (LinearMap.toMatrix' e.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ e.isUnit_det'.ne_zero
  let g : Group := ⟨LinearMap.toMatrix' e.toLinearMap,hdet⟩
  have hg (v : Vector) : W g v = e v := by
    change Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap) v = e v
    rw [Matrix.toLin'_toMatrix']
    rfl
  refine ⟨g,?_⟩
  apply Prod.ext
  · exact (hg x.1).trans (congrArg Prod.fst he)
  · apply LinearMap.ext
    intro v
    have hgi : W g⁻¹ v = e.symm v := by
      apply e.injective
      rw [← hg,self_inv_apply,e.apply_symm_apply]
    change x.2 (W g⁻¹ v) = y.2 v
    rw [hgi]
    exact LinearMap.congr_fun (congrArg Prod.snd he) v

/-- Odd cardinality produces a singular point fixed by a two-group of implementers. -/
theorem twoGroup_fixes_singular {P : Type*} [_root_.Group P]
    (hp : IsPGroup 2 P) (ρ : Representation (ZMod 2) P Space)
    (a : P →* MulAut Group)
    (hcov : ∀ p g x, ρ p (action g x) = action (a p g) (ρ p x)) :
    ∃ x : Space, IsSingular x ∧ ∀ p, ρ p x = x := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinv (p : P) (x : Space) (hx : IsSingular x) : IsSingular (ρ p x) :=
    singular_implementer (a p)
      (LinearMap.GeneralLinearGroup.toLinearEquiv (ρ.asGroupHom p)) (hcov p) x hx
  let : MulAction P {x : Space // IsSingular x} := {
    smul p x := ⟨ρ p x,hinv p x x.property⟩
    one_smul x := Subtype.ext (by change ρ 1 x.val = x.val; rw [map_one]; rfl)
    mul_smul p q x := Subtype.ext (by change ρ (p*q) x.val = ρ p (ρ q x.val); rw [map_mul]; rfl) }
  obtain ⟨x,hx⟩ := hp.nonempty_fixed_point_of_prime_not_dvd_card
    {x : Space // IsSingular x} (by rw [singular_card]; decide)
  exact ⟨x,x.property,fun p => congrArg Subtype.val (hx p)⟩

open DoubledBinaryPlanes
/-- Every proper extension of a paired plane contains a singular diagonal vector. -/
theorem pairedPlane_lt_singular (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (S : Submodule (ZMod 2) Space) (hUS : pairedPlane v f < S) :
    ∃ x ∈ S, x.1 ≠ 0 ∧ x.2 ≠ 0 ∧ x.2 x.1 = 0 := by
  obtain ⟨x,hx,hxU⟩ := SetLike.exists_of_lt hUS
  have hvS : (v,0) ∈ S := hUS.le (Submodule.subset_span (by simp))
  have hfS : (0,f) ∈ S := hUS.le (Submodule.subset_span (by simp))
  let z : Space := x - f x.1 • (v,0) - x.2 v • (0,f)
  have hzS : z ∈ S := S.sub_mem (S.sub_mem hx (S.smul_mem _ hvS)) (S.smul_mem _ hfS)
  have hz1 : f z.1 = 0 := by simp [z,hfv]
  have hz2 : z.2 v = 0 := by simp [z,hfv]
  have hz : z ≠ 0 := by
    intro he
    apply hxU
    rw [pairedPlane,Submodule.mem_span_pair]
    refine ⟨f x.1,x.2 v,?_⟩
    change x - f x.1 • (v,0) - x.2 v • (0,f) = 0 at he
    simpa [add_comm] using (sub_eq_iff_eq_add.mp (sub_eq_zero.mp he)).symm
  have hv : v ≠ 0 := by intro he; simp [he] at hfv
  have hf : f ≠ 0 := by intro he; simp [he] at hfv
  by_cases h1 : z.1 = 0
  · have h2 : z.2 ≠ 0 := by intro h2; exact hz (Prod.ext h1 h2)
    refine ⟨z+(v,0),S.add_mem hzS hvS,?_,?_,?_⟩
    · simpa [h1] using hv
    · simpa using h2
    · simpa [h1] using hz2
  by_cases h2 : z.2 = 0
  · refine ⟨z+(0,f),S.add_mem hzS hfS,?_,?_,?_⟩
    · simpa using h1
    · simpa [h2] using hf
    · simpa [h2] using hz1
  by_cases hp : z.2 z.1 = 0
  · exact ⟨z,hzS,h1,h2,hp⟩
  have hp1 : z.2 z.1 = 1 := (by decide : ∀ a : ZMod 2, a ≠ 0 → a = 1) _ hp
  refine ⟨z+(v,0)+(0,f),S.add_mem (S.add_mem hzS hvS) hfS,?_,?_,?_⟩
  · intro he
    have hh := congrArg f he
    simp [hz1,hfv] at hh
  · intro he
    have hh := LinearMap.congr_fun he v
    simp [hz2,hfv] at hh
  · norm_num [map_add,hp1,hz1,hz2,hfv]; decide

open scoped IsMulCommutative

/-- Transport the paired-plane calculation to an intersection in the original group. -/
theorem ambientPlane_lt_singular {G : Type*} [_root_.Group G]
    (W₀ : Subgroup G) [IsElementaryAbelian 2 W₀]
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (v : Vector) (f : Module.Dual (ZMod 2) Vector) (hfv : f v = 1)
    (X : Subgroup G) (hlt : ambientPlane W₀ E v f < W₀ ⊓ X) :
    ∃ w : Additive W₀, (w.toMul : G) ∈ X ∧
      (E w).1 ≠ 0 ∧ (E w).2 ≠ 0 ∧ (E w).2 (E w).1 = 0 := by
  have hle : pairedPlane v f ≤ coordinateSubspace W₀ E (W₀ ⊓ X) := by
    obtain ⟨hv,hf⟩ := (ambientPlane_le_iff W₀ E v f _).mp hlt.le
    rw [pairedPlane_le_iff]
    constructor
    · simpa only [E.apply_symm_apply] using
        (coordinate_mem W₀ E (W₀ ⊓ X) (E.symm (v,0))).mpr hv
    · simpa only [E.apply_symm_apply] using
        (coordinate_mem W₀ E (W₀ ⊓ X) (E.symm (0,f))).mpr hf
  have hs : pairedPlane v f < coordinateSubspace W₀ E (W₀ ⊓ X) := by
    apply lt_of_le_not_ge hle
    intro hback
    apply hlt.not_ge
    intro x hx
    refine ⟨⟨x,hx.1⟩,?_,rfl⟩
    change E (Additive.ofMul ⟨x,hx.1⟩) ∈ pairedPlane v f
    exact hback ((coordinate_mem W₀ E (W₀ ⊓ X) _).mpr hx)
  obtain ⟨z,hz,hz1,hz2,hzz⟩ := pairedPlane_lt_singular v f hfv _ hs
  have hm : ((E.symm z).toMul : G) ∈ W₀ ⊓ X := by
    apply (coordinate_mem W₀ E (W₀ ⊓ X) _).mp
    simpa only [E.apply_symm_apply] using hz
  exact ⟨E.symm z,hm.2,by simpa only [E.apply_symm_apply] using hz1,
    by simpa only [E.apply_symm_apply] using hz2,
    by simpa only [E.apply_symm_apply] using hzz⟩

open CFSG.Quasithin.ChapterE
open scoped Pointwise

/-- A singular diagonal point in the literal orbit is centralized by an ambient Sylow subgroup. -/
theorem ambient_singular_sylow {G : Type*} [_root_.Group G]
    (W₀ L : Subgroup G) [IsElementaryAbelian 2 W₀]
    (T : Sylow 2 G) (hTN : (T : Subgroup G) ≤ normalizer (W₀ : Set G))
    (hLN : L ≤ normalizer (W₀ : Set G)) (q : L →* Group) (hq : Function.Surjective q)
    (E : Additive W₀ ≃ₗ[ZMod 2] Space)
    (hE : ∀ l w, E (automizerRepresentation W₀
      (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) w) = action (q l) (E w))
    (a : Automizer W₀ ≃* MulAut Group)
    (hcov : ∀ b g w, E (automizerRepresentation W₀ b (E.symm (action g (E w)))) =
      action (a b g) (E (automizerRepresentation W₀ b w)))
    (w : Additive W₀) (hw : IsSingular (E w)) :
    ∃ S : Sylow 2 G, (S : Subgroup G) ≤ centralizer ({(w.toMul : G)} : Set G) := by
  let j := W₀.normalizerMonoidHom.rangeRestrict.comp (inclusion hTN)
  let ρ : Representation (ZMod 2) (T : Subgroup G) Space :=
    E.conjRingEquiv.toMonoidHom.comp ((automizerRepresentation W₀).comp j)
  obtain ⟨x,hx,hfix⟩ := twoGroup_fixes_singular T.2 ρ
    (a.toMonoidHom.comp j) (by
      intro p g x
      change E (automizerRepresentation W₀ (j p) (E.symm (action g x))) =
        action (a (j p) g) (E (automizerRepresentation W₀ (j p) (E.symm x)))
      simpa only [E.apply_symm_apply] using hcov (j p) g (E.symm x))
  let z := E.symm x
  have hzc (t : T) : (t : G) * (z.toMul : G) = (z.toMul : G) * (t : G) := by
    have hh : automizerRepresentation W₀ (j t) z = z := by
      apply E.injective
      exact (hfix t).trans (E.apply_symm_apply x).symm
    have hc := congrArg (fun y : Additive W₀ => (y.toMul : G)) hh
    change (t : G) * (z.toMul : G) * (t : G)⁻¹ = (z.toMul : G) at hc
    exact mul_inv_eq_iff_eq_mul.mp hc
  obtain ⟨g,hg⟩ := singular_transitive x (E w) hx hw
  obtain ⟨l,hl⟩ := hq g
  have hlw : (MulAut.conj (l : G)) (z.toMul : G) = (w.toMul : G) := by
    have hh : automizerRepresentation W₀
        (W₀.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) z = w := by
      apply E.injective
      rw [hE,hl]
      change action g (E (E.symm x)) = E w
      rwa [E.apply_symm_apply]
    exact congrArg (fun y : Additive W₀ => (y.toMul : G)) hh
  refine ⟨(l : G) • T,?_⟩
  intro t ht
  change t ∈ MulAut.conj (l : G) • (T : Set G) at ht
  obtain ⟨s,hs,rfl⟩ := Set.mem_smul_set.mp ht
  apply mem_centralizer_singleton_iff.mpr
  have hh := congrArg (MulAut.conj (l : G)) (hzc ⟨s,hs⟩)
  change (MulAut.conj (l : G)) s * (w.toMul : G) =
    (w.toMul : G) * (MulAut.conj (l : G)) s
  simpa only [map_mul,hlw] using hh

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryComponentGeometry
