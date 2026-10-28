module
public import Theory.Representation.SL3.NaturalDualElementaryLift

/-!
# Element centralizers in a natural-center, doubled-dual two-group

A proper additive subgroup of the natural module invariant under a vector
stabilizer lies on that vector's line. Inverse transpose transfers this
calculation to the dual. Apply it to the second-axis images of elements
commuting with a noncentral first-axis lift. That image is proper, since
otherwise the lift is central, and the elementary diagonal lifts supply
exactly the whole scalar line. Thus its centralizer has quotient coordinates
Dual(F³) × F, and order |F|⁴ |Z(Q)|.

The source application preserves the original MS quotient in
NonblockMSElementCentralizers. This is the element-centralizer calculation
used in the rank argument for the larger two-core, not that core theorem.
Source: Aschbacher--Smith, C.1.35(2), printed pp.137--139.
-/

@[expose] public section

open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups
open Matrix.PSL3.LinearThree
namespace Representation.SL3ParabolicNatural
variable {F : Type*} [Field F]

private theorem point_invariant_line (W : AddSubgroup (Fin 3 → F)) (hW : W ≠ ⊤)
    (hi : ∀ g ∈ pointLocalSL F, ∀ v ∈ W, g.val.mulVec v ∈ W)
    (v : Fin 3 → F) (hv : v ∈ W) : ∃ a : F, v = a • Pi.single 0 1 := by
  have hh := point_invariant_fixed W hW hi
  have ht {i : Fin 3} (hi : i ≠ 0) :
      transvection (Ne.symm hi) (1:F) ∈ pointLocalSL F := by
    rw [mem_pointLocalSL_iff]
    simp [transvection_coe, hi]
  have h1 := congrFun (hh _ (ht (by decide : (1 : Fin 3) ≠ 0)) v hv) 0
  have h2 := congrFun (hh _ (ht (by decide : (2 : Fin 3) ≠ 0)) v hv) 0
  change specialLinearNatural 3 (transvection (by decide : (0 : Fin 3) ≠ 1) 1) v 0 = v 0 at h1
  change specialLinearNatural 3 (transvection (by decide : (0 : Fin 3) ≠ 2) 1) v 0 = v 0 at h2
  rw [OneCohomology.SLHigherNatural.action_transvection] at h1 h2
  have hv1 : v 1 = 0 := by simpa using h1
  have hv2 : v 2 = 0 := by simpa using h2
  refine ⟨v 0, ?_⟩
  ext i
  fin_cases i <;> simp [hv1,hv2]

theorem vector_stabilizer_invariant_le_line (v : Fin 3 → F) (hv : v ≠ 0)
    (W : AddSubgroup (Fin 3 → F)) (hW : W ≠ ⊤)
    (hi : ∀ g : SL(3,F), specialLinearNatural 3 g v = v →
      ∀ w ∈ W, specialLinearNatural 3 g w ∈ W)
    (w : Fin 3 → F) (hw : w ∈ W) : ∃ a : F, w = a • v := by
  let ρ := specialLinearNatural (k := F) 3
  obtain ⟨b,hb⟩ := exists_mulVec_eq_three (Pi.single 0 1) v (by simp) hv
  change ρ b (Pi.single 0 1) = v at hb
  let W' := W.comap (ρ b).toAddMonoidHom
  have hW' : W' ≠ ⊤ := by
    intro he
    apply hW
    apply top_unique
    intro y _
    have hy : ρ b⁻¹ y ∈ W' := he ▸ AddSubgroup.mem_top _
    change ρ b (ρ b⁻¹ y) ∈ W at hy
    rwa [ρ.self_inv_apply] at hy
  have hi' : ∀ g ∈ pointLocalSL F, ∀ z ∈ W', g.val.mulVec z ∈ W' := by
    intro g hg z hz
    have hfix : ρ g (Pi.single 0 1) = Pi.single 0 1 := by
      obtain ⟨h0,h1,h2⟩ := (mem_pointLocalSL_iff F g).mp hg
      ext i
      fin_cases i <;> simp [ρ,specialLinearNatural_apply,Matrix.mulVec,dotProduct,
        Fin.sum_univ_three,h0,h1,h2]
    have hh := hi (b*g*b⁻¹) (by
      rw [←hb,map_mul,map_mul,Module.End.mul_apply,Module.End.mul_apply,
        ρ.inv_self_apply,hfix]) (ρ b z) hz
    change ρ b (ρ g z) ∈ W
    change ρ (b*g*b⁻¹) (ρ b z) ∈ W at hh
    simpa only [map_mul,Module.End.mul_apply,ρ.inv_self_apply] using hh
  have hw' : ρ b⁻¹ w ∈ W' := by
    change ρ b (ρ b⁻¹ w) ∈ W
    rwa [ρ.self_inv_apply]
  obtain ⟨a,ha⟩ := point_invariant_line W' hW' hi' _ hw'
  refine ⟨a, ?_⟩
  have hh := congrArg (ρ b) ha
  simpa only [ρ.self_inv_apply,map_smul,hb] using hh

noncomputable def dualVectorCoordinates : Module.Dual F (Fin 3 → F) ≃ₗ[F] (Fin 3 → F) :=
  (Pi.basisFun F (Fin 3)).dualBasis.equivFun

theorem dualVectorCoordinates_apply (f : Module.Dual F (Fin 3 → F)) (i : Fin 3) :
    dualVectorCoordinates f i = f (Pi.single i 1) := by
  simp [dualVectorCoordinates,Module.Basis.equivFun_apply]

theorem dualVectorCoordinates_action (g : SL(3,F)) (f : Module.Dual F (Fin 3 → F)) :
    dualVectorCoordinates ((specialLinearNatural 3).dual g f) =
      g⁻¹.val.transpose.mulVec (dualVectorCoordinates f) := by
  ext i
  rw [dualVectorCoordinates_apply]
  change f (specialLinearNatural 3 g⁻¹ (Pi.single i 1)) = _
  have he : specialLinearNatural 3 g⁻¹ (Pi.single i 1) =
      ∑ j : Fin 3, g⁻¹.val j i • Pi.single j 1 := by
    ext j
    fin_cases i <;> fin_cases j <;>
      simp [specialLinearNatural_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [he,map_sum]
  simp [Matrix.mulVec, dotProduct,dualVectorCoordinates_apply,Fin.sum_univ_three]

theorem dual_stabilizer_invariant_le_line (f : Module.Dual F (Fin 3 → F)) (hf : f ≠ 0)
    (W : AddSubgroup (Module.Dual F (Fin 3 → F))) (hW : W ≠ ⊤)
    (hi : ∀ g : SL(3,F), (specialLinearNatural 3).dual g f = f →
      ∀ w ∈ W, (specialLinearNatural 3).dual g w ∈ W)
    (w : Module.Dual F (Fin 3 → F)) (hw : w ∈ W) : ∃ a : F, w = a • f := by
  let e := dualVectorCoordinates (F := F)
  let W' := W.map e.toAddEquiv.toAddMonoidHom
  have he (g : SL(3,F)) (z : Module.Dual F (Fin 3 → F)) :
      e ((specialLinearNatural 3).dual (g.transpose)⁻¹ z) = specialLinearNatural 3 g (e z) := by
    rw [dualVectorCoordinates_action,inv_inv]
    rfl
  have hf' : e f ≠ 0 := fun hz => hf (e.injective (hz.trans (map_zero e).symm))
  have hW' : W' ≠ ⊤ := by
    intro hh
    apply hW
    apply top_unique
    intro z _
    obtain ⟨y,hy,hyz⟩ := show e z ∈ W' from hh ▸ AddSubgroup.mem_top _
    exact (e.injective hyz) ▸ hy
  obtain ⟨a,ha⟩ := vector_stabilizer_invariant_le_line (e f) hf' W' hW' (by
    intro g hg z hz
    obtain ⟨y,hy,rfl⟩ := hz
    change specialLinearNatural 3 g (e y) ∈ W'
    rw [←he]
    exact AddSubgroup.mem_map.mpr ⟨_,hi (g.transpose)⁻¹
      (e.injective ((he g f).trans hg)) y hy,rfl⟩) (e w) (AddSubgroup.mem_map.mpr ⟨w,hw,rfl⟩)
  exact ⟨a,e.injective (ha.trans (map_smul e a f).symm)⟩
end Representation.SL3ParabolicNatural

namespace Representation.SL3ParabolicNatural
open Subgroup
variable {F A Q : Type*} [Field F] [Group A] [Group Q] [MulDistribMulAction A Q]

private theorem commute_of_equal_image
    {M : Type*} [Group M] (p : Q →* M) (hc : p.ker ≤ center Q)
    {x y z : Q} (hxy : p x = p y) (hy : Commute y z) : Commute x z := by
  have hk : x / y ∈ p.ker := p.div_mem_ker_iff.mpr hxy
  have hh : Commute (x/y) z := (mem_center_iff.mp (hc hk) z).symm
  simpa only [div_mul_cancel] using hh.mul_left hy

private theorem elementary_commute
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    {a b : F} {x y : Q} (hx : p x ∈ (dualDiagonal a b).range)
    (hy : p y ∈ (dualDiagonal a b).range) : Commute x y := by
  let := hel a b
  exact congrArg Subtype.val (mul_comm' (⟨x,hx⟩ : (dualDiagonal a b).range.comap p) ⟨y,hy⟩)

private theorem axis_proportional_commute
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    {x y : Q} (f : Module.Dual F (Fin 3 → F)) (a : F)
    (hx : (p x).toAdd = (f,0)) (hy : (p y).toAdd = (0,a • f)) : Commute x y := by
  have hsq (a b : F) (z : Q) (hz : p z ∈ (dualDiagonal a b).range) : z^2 = 1 := by
    let := hel a b
    exact elemPow_eq_one_of_isElementaryAbelian (A := (dualDiagonal a b).range.comap p) z hz
  have hx2 : x^2 = 1 := hsq 1 0 x ⟨Multiplicative.ofAdd f,by
    apply Multiplicative.toAdd.injective
    change (1 • f,0 • f) = (p x).toAdd
    simp only [one_smul,zero_smul,hx]⟩
  have hy2 : y^2 = 1 := hsq 0 1 y ⟨Multiplicative.ofAdd (a • f),by
    apply Multiplicative.toAdd.injective
    change (0 • (a • f),1 • (a • f)) = (p y).toAdd
    simp only [one_smul,zero_smul,hy]⟩
  have hxy2 : (x*y)^2 = 1 := hsq 1 a (x*y) ⟨Multiplicative.ofAdd f,by
    apply Multiplicative.toAdd.injective
    change (1 • f,a • f) = (p (x*y)).toAdd
    rw [map_mul]
    change (1 • f,a • f) = (p x).toAdd + (p y).toAdd
    simp only [hx,hy,one_smul,Prod.mk_add_mk,add_zero,zero_add]⟩
  have hi (z : Q) (hz : z^2 = 1) : z⁻¹ = z :=
    inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hz)
  change x*y = y*x
  rw [←hi (x*y) hxy2,_root_.mul_inv_rev,hi x hx2,hi y hy2]

/-- The centralizer in the other dual axis projects onto exactly the line
through a nonzero first-axis vector. Only additive invariance is used. -/
theorem dual_axes_commute_iff
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (_hp : Function.Surjective p) (hc : p.ker = center Q)
    (he : ∀ a q, (p (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p q).toAdd)
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    (w z : Q) (f g : Module.Dual F (Fin 3 → F)) (hf : f ≠ 0)
    (hw : (p w).toAdd = (f,0)) (hz : (p z).toAdd = (0,g)) :
    Commute w z ↔ ∃ a : F, g = a • f := by
  let W : AddSubgroup (Module.Dual F (Fin 3 → F)) := {
    carrier := {v | ∃ q : Q, (p q).toAdd = (0,v) ∧ Commute w q}
    zero_mem' := ⟨1,by rw [map_one]; rfl,Commute.one_right _⟩
    add_mem' := by
      rintro a b ⟨x,hx,hxc⟩ ⟨y,hy,hyc⟩
      refine ⟨x*y,?_,hxc.mul_right hyc⟩
      rw [map_mul]
      change (p x).toAdd + (p y).toAdd = _
      simp only [hx,hy,Prod.mk_add_mk,zero_add]
    neg_mem' := by
      rintro a ⟨x,hx,hxc⟩
      refine ⟨x⁻¹,?_,hxc.inv_right⟩
      rw [map_inv]
      change -(p x).toAdd = _
      simp only [hx,Prod.neg_mk,neg_zero] }
  have hproper : W ≠ ⊤ := by
    intro htop
    have hwC : w ∈ center Q := by
      apply Subgroup.mem_center_iff.mpr
      intro q
      obtain ⟨b,hb,hwb⟩ := show (p q).toAdd.2 ∈ W from htop ▸ AddSubgroup.mem_top _
      have hqa : p (q/b) ∈ (dualDiagonal (1:F) 0).range := by
        refine ⟨Multiplicative.ofAdd (p q).toAdd.1,?_⟩
        apply Multiplicative.toAdd.injective
        rw [map_div]
        change (1 • (p q).toAdd.1,0 • (p q).toAdd.1) = (p q).toAdd - (p b).toAdd
        simp only [hb,one_smul,zero_smul]
        exact Prod.ext (sub_zero _).symm (sub_self _).symm
      have hwa : p w ∈ (dualDiagonal (1:F) 0).range := ⟨Multiplicative.ofAdd f,by
        apply Multiplicative.toAdd.injective
        change (1 • f,0 • f) = (p w).toAdd
        simp only [hw,one_smul,zero_smul]⟩
      have hcomm := (elementary_commute p hel hwa hqa).mul_right hwb
      simpa only [div_mul_cancel] using hcomm.symm.eq
    have hwk : p w = 1 := show w ∈ p.ker from hc ▸ hwC
    have hh := congrArg (fun x => x.toAdd.1) hwk
    rw [hw] at hh
    exact hf hh
  have hstable : ∀ a : SL(3,F), (specialLinearNatural 3).dual a f = f →
      ∀ v ∈ W, (specialLinearNatural 3).dual a v ∈ W := by
    intro a ha v hv
    obtain ⟨q,hq,hwq⟩ := hv
    obtain ⟨k,rfl⟩ := hα a
    refine ⟨k • q,?_,?_⟩
    · rw [he,hq]
      change ((specialLinearNatural 3).dual (α k) 0,
        (specialLinearNatural 3).dual (α k) v) = _
      rw [map_zero]
    · have hkw : p w = p (k • w) := by
        apply Multiplicative.toAdd.injective
        rw [he,hw]
        change (f,0) = ((specialLinearNatural 3).dual (α k) f,
          (specialLinearNatural 3).dual (α k) 0)
        rw [ha,map_zero]
      apply commute_of_equal_image p hc.le hkw
      change (k • w)*(k • q) = (k • q)*(k • w)
      rw [←smul_mul',←smul_mul',hwq.eq]
  constructor
  · intro hcomm
    exact dual_stabilizer_invariant_le_line f hf W hproper hstable g ⟨z,hz,hcomm⟩
  · rintro ⟨a,rfl⟩
    exact axis_proportional_commute p hel f a hw hz

end Representation.SL3ParabolicNatural

namespace Representation.SL3ParabolicNatural
open Subgroup
variable {F A Q : Type*} [Field F] [Group A] [Group Q] [MulDistribMulAction A Q]

/-- For a noncentral vector in the first dual lift, the full centralizer is
cut out by one line condition on the second quotient coordinate. -/
theorem dual_first_axis_centralizer_iff
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hp : Function.Surjective p) (hc : p.ker = center Q)
    (he : ∀ a q, (p (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p q).toAdd)
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    (w z : Q) (f : Module.Dual F (Fin 3 → F)) (hf : f ≠ 0)
    (hw : (p w).toAdd = (f,0)) :
    Commute w z ↔ ∃ a : F, (p z).toAdd.2 = a • f := by
  obtain ⟨y,hy⟩ := hp (Multiplicative.ofAdd (0,(p z).toAdd.2))
  have hy' : (p y).toAdd = (0,(p z).toAdd.2) := congrArg Multiplicative.toAdd hy
  have hza : p (z/y) ∈ (dualDiagonal (1:F) 0).range := by
    refine ⟨Multiplicative.ofAdd (p z).toAdd.1,?_⟩
    apply Multiplicative.toAdd.injective
    rw [map_div]
    change (1 • (p z).toAdd.1,0 • (p z).toAdd.1) = (p z).toAdd - (p y).toAdd
    simp only [hy',one_smul,zero_smul]
    exact Prod.ext (sub_zero _).symm (sub_self _).symm
  have hwa : p w ∈ (dualDiagonal (1:F) 0).range := ⟨Multiplicative.ofAdd f,by
    apply Multiplicative.toAdd.injective
    change (1 • f,0 • f) = (p w).toAdd
    simp only [hw,one_smul,zero_smul]⟩
  have hh := elementary_commute p hel hwa hza
  rw [←dual_axes_commute_iff α hα p hp hc he hel w y f (p z).toAdd.2 hf hw hy']
  constructor
  · intro hz
    have hc := hh.inv_right.mul_right hz
    simpa only [div_eq_mul_inv,_root_.mul_inv_rev,inv_inv,mul_assoc,inv_mul_cancel,
      mul_one] using hc
  · intro hy
    simpa only [div_mul_cancel] using hh.mul_right hy
end Representation.SL3ParabolicNatural

namespace Representation.SL3ParabolicNatural
open Subgroup
variable {F : Type*} [Field F]

/-- Parameters for the quotient of a first-axis element centralizer. -/
def dualCentralizerMap (f : Module.Dual F (Fin 3 → F)) :
    Multiplicative (Module.Dual F (Fin 3 → F) × F) →*
      Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)) where
  toFun z := Multiplicative.ofAdd (z.toAdd.1,z.toAdd.2 • f)
  map_one' := by apply Multiplicative.toAdd.injective; exact Prod.ext rfl (zero_smul _ _)
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    exact Prod.ext rfl (add_smul _ _ _)

theorem dualCentralizerMap_injective {f : Module.Dual F (Fin 3 → F)} (hf : f ≠ 0) :
    Function.Injective (dualCentralizerMap f) := by
  intro x y he
  have h := congrArg Multiplicative.toAdd he
  change (x.toAdd.1,x.toAdd.2 • f) = (y.toAdd.1,y.toAdd.2 • f) at h
  apply Multiplicative.toAdd.injective
  have h1 : x.toAdd.1 = y.toAdd.1 := congrArg (fun z => z.1) h
  have h2 : x.toAdd.2 • f = y.toAdd.2 • f := congrArg (fun z => z.2) h
  exact Prod.ext h1 ((smul_left_injective F hf) h2)

theorem mem_dualCentralizerMap_range (f : Module.Dual F (Fin 3 → F))
    (z : Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F))) :
    z ∈ (dualCentralizerMap f).range ↔ ∃ a : F, z.toAdd.2 = a • f := by
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.toAdd.2,rfl⟩
  · rintro ⟨a,ha⟩
    refine ⟨Multiplicative.ofAdd (z.toAdd.1,a),?_⟩
    apply Multiplicative.toAdd.injective
    exact Prod.ext rfl ha.symm

theorem dualCentralizerMap_range_card {f : Module.Dual F (Fin 3 → F)} (hf : f ≠ 0) :
    Nat.card (dualCentralizerMap f).range = (Nat.card F)^4 := by
  rw [←Nat.card_congr (MonoidHom.ofInjective (dualCentralizerMap_injective hf)).toEquiv]
  change Nat.card (Module.Dual F (Fin 3 → F) × F) = _
  rw [Nat.card_prod,Module.natCard_eq_pow_finrank (K := F),Subspace.dual_finrank_eq,
    Module.finrank_fin_fun]
  exact (pow_succ _ _).symm

private theorem card_preimage {J H : Type*} [Group J] [Group H]
    (p : J →* H) (hp : Function.Surjective p) (B : Subgroup H) :
    Nat.card (B.comap p) = Nat.card B * Nat.card p.ker := by
  let W := B.comap p
  let f := p.comp W.subtype
  have hr : f.range = B := by
    ext y
    constructor
    · rintro ⟨x,rfl⟩
      exact x.property
    · intro hy
      obtain ⟨x,hx⟩ := hp y
      exact ⟨⟨x,show p x ∈ B from hx.symm ▸ hy⟩,hx⟩
  have hk : f.ker = p.ker.subgroupOf W := rfl
  have hle : p.ker ≤ W := by
    intro x hx
    change p x ∈ B
    rw [show p x = 1 from hx]
    exact B.one_mem
  have hc := f.ker.index_mul_card
  rw [index_ker,hr,hk,Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv] at hc
  exact hc.symm

variable {A Q : Type*} [Group A] [Group Q] [MulDistribMulAction A Q]

theorem dual_first_axis_centralizer_eq
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hp : Function.Surjective p) (hc : p.ker = center Q)
    (he : ∀ a q, (p (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p q).toAdd)
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    (w : Q) (f : Module.Dual F (Fin 3 → F)) (hf : f ≠ 0)
    (hw : (p w).toAdd = (f,0)) :
    centralizer ({w} : Set Q) = (dualCentralizerMap f).range.comap p := by
  ext z
  change (∀ x ∈ ({w} : Set Q), x*z = z*x) ↔ _
  simp only [Set.mem_singleton_iff,forall_eq]
  change Commute w z ↔ p z ∈ (dualCentralizerMap f).range
  rw [mem_dualCentralizerMap_range]
  exact dual_first_axis_centralizer_iff α hα p hp hc he hel w z f hf hw

/-- The element centralizer has order |F|⁴|Z(Q)|, hence |F|⁷ for the
natural central kernel in C.1.35. -/
theorem dual_first_axis_centralizer_card
    (α : A →* SL(3,F)) (hα : Function.Surjective α)
    (p : Q →* Multiplicative (Module.Dual F (Fin 3 → F) × Module.Dual F (Fin 3 → F)))
    (hp : Function.Surjective p) (hc : p.ker = center Q)
    (he : ∀ a q, (p (a • q)).toAdd =
      ((specialLinearNatural 3).dual.prod (specialLinearNatural 3).dual) (α a) (p q).toAdd)
    (hel : ∀ a b : F, IsElementaryAbelian 2 ((dualDiagonal a b).range.comap p))
    (w : Q) (f : Module.Dual F (Fin 3 → F)) (hf : f ≠ 0)
    (hw : (p w).toAdd = (f,0)) :
    Nat.card (centralizer ({w} : Set Q)) = (Nat.card F)^4 * Nat.card (center Q) := by
  rw [dual_first_axis_centralizer_eq α hα p hp hc he hel w f hf hw,
    card_preimage p hp,dualCentralizerMap_range_card hf,hc]
end Representation.SL3ParabolicNatural
