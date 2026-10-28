module
public import Theory.Representation.SL3DoubledNaturalOffenders.Centralizer
public import Theory.Representation.PSL3Two.OrbitStabilizers
public import Theory.Representation.SLThreeCentralExtension.Stabilizers
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Binary doubled-natural orbits and the multiplicity involution

Independent ordered columns form the 42-point orbit with elementary
four-group stabilizer. The actual swap of the two columns joins the two
axis orbits into a 14-point orbit with S₄ component stabilizer. The diagonal
has seven nonzero vectors. The additive commutant calculation classifies
all embedded natural copies and proves uniqueness of the swap-invariant
copy. A commuting actor fixing a vector outside that copy is trivial.

These are the concrete action calculations for Aschbacher--Smith,
13.1.10(3) and 13.1.12, printed pp.872--873.
-/

public noncomputable section
open Subgroup Representation Matrix
namespace Representation.SL3DoubledNaturalOffenders.BinaryOrbits
open BinaryLinearThree
open Representation.OneCohomology.SLThreeCentralExtension
abbrev V := Space (ZMod 2)
abbrev rho := representation (ZMod 2)

theorem pair_transitive
    (a b c d : BinaryLinearThree.Vector)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (hc : c ≠ 0) (hd : d ≠ 0) (hcd : c ≠ d) :
    ∃ g : BinaryLinearThree.Group,
      BinaryLinearThree.W g a = c ∧ BinaryLinearThree.W g b = d := by
  rw [show BinaryLinearThree.W = Representation.specialLinearNatural 3 from rfl]
  let ba := (by
    rw [linearIndependent_fin2]
    refine ⟨hb, ?_⟩
    intro r
    have hr : r = 0 ∨ r = 1 := by revert r; decide
    rcases hr with rfl | rfl
    · simpa using ha.symm
    · simpa using hab.symm : LinearIndependent (ZMod 2) ![a,b]
  ).linearCombinationEquiv
  let bc := (by
    rw [linearIndependent_fin2]
    refine ⟨hd, ?_⟩
    intro r
    have hr : r = 0 ∨ r = 1 := by revert r; decide
    rcases hr with rfl | rfl
    · simpa using hc.symm
    · simpa using hcd.symm : LinearIndependent (ZMod 2) ![c,d]
  ).linearCombinationEquiv
  let f := ba.symm.trans bc
  obtain ⟨e, he⟩ := Submodule.exists_linearEquiv_restrict_eq f
  have h0 : e a = c := by
    have h := he (ba (Finsupp.single 0 1))
    simpa [f, ba, bc] using h.symm
  have h1 : e b = d := by
    have h := he (ba (Finsupp.single 1 1))
    simpa [f, ba, bc] using h.symm
  have hdet : (LinearMap.toMatrix' e.toLinearMap).det = 1 := by
    rw [LinearMap.det_toMatrix']
    exact (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ e.isUnit_det'.ne_zero
  refine ⟨⟨LinearMap.toMatrix' e.toLinearMap, hdet⟩, ?_, ?_⟩
  · change Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap) a = c
    rwa [Matrix.toLin'_toMatrix']
  · change Matrix.toLin' (LinearMap.toMatrix' e.toLinearMap) b = d
    rwa [Matrix.toLin'_toMatrix']

/-- The rank-two tensors, written as independent ordered columns. -/
@[expose] def independent : Set V := {v | v 0 ≠ 0 ∧ v 1 ≠ 0 ∧ v 0 ≠ v 1}

theorem independent_orbit (v : V) (hv : v ∈ independent) :
    Set.range (fun g => rho g v) = independent := by
  ext w
  constructor
  · rintro ⟨g,rfl⟩
    rcases hv with ⟨h0,h1,h01⟩
    change W g (v 0) ≠ 0 ∧ W g (v 1) ≠ 0 ∧ W g (v 0) ≠ W g (v 1)
    exact ⟨fun h => h0 (by simpa using congrArg (W g⁻¹) h),
      fun h => h1 (by simpa using congrArg (W g⁻¹) h),
      fun h => h01 (by simpa using congrArg (W g⁻¹) h)⟩
  · rintro ⟨h0,h1,h01⟩
    obtain ⟨g,hg0,hg1⟩ := pair_transitive (v 0) (v 1) (w 0) (w 1)
      hv.1 hv.2.1 hv.2.2 h0 h1 h01
    refine ⟨g,?_⟩
    funext i
    fin_cases i
    · exact hg0
    · exact hg1

theorem independent_card : Nat.card independent = 42 := by
  change Nat.card {v : V // v 0 ≠ 0 ∧ v 1 ≠ 0 ∧ v 0 ≠ v 1} = 42
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem independent_stabilizer_index (v : V) (hv : v ∈ independent) :
    (vectorStabilizer rho v).index = 42 := by
  rw [vectorStabilizer_index, independent_orbit v hv, independent_card]

private theorem standard_stabilizer :
    vectorStabilizer rho ![![1,0,0],![0,1,0]] = BinaryLinearThree.R := by
  ext g
  constructor
  · intro hg
    have hh : rho g ![![1,0,0],![0,1,0]] = ![![1,0,0],![0,1,0]] := hg
    have h0 : g.val.mulVec ![1,0,0] = ![1,0,0] := congrFun hh 0
    have h1 : g.val.mulVec ![0,1,0] = ![0,1,0] := congrFun hh 1
    have hc0 : ∀ i, g.val i 0 = (![1,0,0] : Vector) i := by
      intro i
      simpa [mulVec,dotProduct,Fin.sum_univ_three] using congrFun h0 i
    have hc1 : ∀ i, g.val i 1 = (![0,1,0] : Vector) i := by
      intro i
      simpa [mulVec,dotProduct,Fin.sum_univ_three] using congrFun h1 i
    have h22 : g.val 2 2 = 1 := by
      have hd := g.property
      rw [det_fin_three] at hd
      simpa [hc0,hc1] using hd
    refine ⟨Multiplicative.ofAdd (g.val 0 2,g.val 1 2),?_⟩
    apply Subtype.ext
    change !![1,0,g.val 0 2; 0,1,g.val 1 2; 0,0,1] = g.val
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hc0,hc1,h22]
  · rintro ⟨c,rfl⟩
    change rho (shear c) ![![1,0,0],![0,1,0]] = ![![1,0,0],![0,1,0]]
    have hs : (shear c).val = !![1,0,c.toAdd.1;0,1,c.toAdd.2;0,0,1] := rfl
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [rho,representation_apply,hs,mulVec,dotProduct,Fin.sum_univ_three]

/-- The independent-pair stabilizer is a concrete elementary four-group. -/
def independentStabilizerEquiv (v : V) (hv : v ∈ independent) :
    vectorStabilizer rho v ≃* Multiplicative (ZMod 2 × ZMod 2) := by
  let : MulAction BinaryLinearThree.Group V := {
    smul := fun g w => rho g w
    one_smul := fun w => LinearMap.congr_fun rho.map_one w
    mul_smul := fun g h w => LinearMap.congr_fun (rho.map_mul g h) w }
  have hex : ∃ g, rho g ![![1,0,0],![0,1,0]] = v := by
    rw [← Set.mem_range, independent_orbit _ (by decide +kernel :
      (![![1,0,0],![0,1,0]] : V) 0 ≠ 0 ∧
      (![![1,0,0],![0,1,0]] : V) 1 ≠ 0 ∧
      (![![1,0,0],![0,1,0]] : V) 0 ≠ (![![1,0,0],![0,1,0]] : V) 1)]
    exact hv
  let g := Classical.choose hex
  have hg := Classical.choose_spec hex
  exact (MulAction.stabilizerEquivStabilizer (show v = g • (![![1,0,0],![0,1,0]] : V)
    from hg.symm)).symm.trans ((MulEquiv.subgroupCongr standard_stabilizer).trans
      (MonoidHom.ofInjective shear_injective).symm)

/-- The original multiplicity involution interchanges the two columns. -/
@[expose] def outerRepresentation : Representation (ZMod 2)
    (BinaryLinearThree.Group × Equiv.Perm (Fin 2)) V where
  toFun g :=
    { toFun v i := W g.1 (v (g.2.symm i))
      map_add' v w := by funext i; exact map_add (W g.1) _ _
      map_smul' a v := by funext i; exact map_smul (W g.1) a _ }
  map_one' := by apply LinearMap.ext; intro v; funext i; exact LinearMap.congr_fun W.map_one (v i)
  map_mul' g h := by apply LinearMap.ext; intro v; funext i; exact LinearMap.congr_fun (W.map_mul g.1 h.1) _

theorem outer_apply (g : BinaryLinearThree.Group) (s : Equiv.Perm (Fin 2))
    (v : V) (i : Fin 2) : outerRepresentation (g,s) v i = W g (v (s.symm i)) := rfl

theorem outer_inner (g : BinaryLinearThree.Group) (v : V) :
    outerRepresentation (g,1) v = rho g v := rfl

/-- The two moved rank-one summands, excluding the fixed diagonal copy. -/
@[expose] def rankOne : Set V := {v | (v 0 ≠ 0 ∧ v 1 = 0) ∨ (v 0 = 0 ∧ v 1 ≠ 0)}

theorem rankOne_card : Nat.card rankOne = 14 := by
  change Nat.card {v : V // (v 0 ≠ 0 ∧ v 1 = 0) ∨ (v 0 = 0 ∧ v 1 ≠ 0)} = 14
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem perm_two (s : Equiv.Perm (Fin 2)) : s = 1 ∨ s = Equiv.swap 0 1 := by
  revert s
  decide +kernel

/-- The genuine outer action joins the two seven-point natural orbits. -/
theorem rankOne_orbit (v : V) (hv : v ∈ rankOne) :
    Set.range (fun g => outerRepresentation g v) = rankOne := by
  have hinner (g : BinaryLinearThree.Group) (w : V) (hw : w ∈ rankOne) :
      rho g w ∈ rankOne := by
    rcases hw with hh | hh
    · left
      exact ⟨fun h => hh.1 (by change W g (w 0) = 0 at h; simpa using congrArg (W g⁻¹) h),
        by change W g (w 1) = 0; rw [hh.2,map_zero]⟩
    · right
      exact ⟨by change W g (w 0) = 0; rw [hh.1,map_zero],
        fun h => hh.2 (by change W g (w 1) = 0 at h; simpa using congrArg (W g⁻¹) h)⟩
  ext w
  constructor
  · rintro ⟨⟨g,s⟩,rfl⟩
    rcases perm_two s with rfl | rfl
    · exact hinner g v hv
    · change rho g (fun i => v ((Equiv.swap (0 : Fin 2) 1).symm i)) ∈ rankOne
      apply hinner
      change (v 1 ≠ 0 ∧ v 0 = 0) ∨ (v 1 = 0 ∧ v 0 ≠ 0)
      exact hv.elim (fun hh => Or.inr ⟨hh.2,hh.1⟩) (fun hh => Or.inl ⟨hh.2,hh.1⟩)
  · intro hw
    rcases hv with hv | hv <;> rcases hw with hw | hw
    · obtain ⟨g,hg⟩ := natural_transitive_nonzero (v 0) (w 0) hv.1 hw.1
      refine ⟨(g,1),?_⟩
      funext i
      fin_cases i
      · exact hg
      · change W g (v 1) = w 1; rw [hv.2,hw.2,map_zero]
    · obtain ⟨g,hg⟩ := natural_transitive_nonzero (v 0) (w 1) hv.1 hw.2
      refine ⟨(g,Equiv.swap 0 1),?_⟩
      funext i
      fin_cases i
      · change W g (v 1) = w 0; rw [hv.2,hw.1,map_zero]
      · exact hg
    · obtain ⟨g,hg⟩ := natural_transitive_nonzero (v 1) (w 0) hv.2 hw.1
      refine ⟨(g,Equiv.swap 0 1),?_⟩
      funext i
      fin_cases i
      · exact hg
      · change W g (v 0) = w 1; rw [hv.1,hw.2,map_zero]
    · obtain ⟨g,hg⟩ := natural_transitive_nonzero (v 1) (w 1) hv.2 hw.2
      refine ⟨(g,1),?_⟩
      funext i
      fin_cases i
      · change W g (v 0) = w 0; rw [hv.1,hw.1,map_zero]
      · exact hg

/-- The component stabilizer in the selected rank-one orbit is S₄. -/
def rankOneStabilizerEquiv (v : V) (hv : v ∈ rankOne) :
    vectorStabilizer rho v ≃* Equiv.Perm (Fin 4) := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := (hv.resolve_left (fun h => h.1 h0)).2
    have he : vectorStabilizer rho v = BinaryLinearThree.OrbitStabilizers.natural (v 1) := by
      ext g
      rw [BinaryLinearThree.OrbitStabilizers.mem_natural]
      constructor
      · intro hg; exact congrFun hg 1
      · intro hg
        change rho g v = v
        funext i
        fin_cases i
        · change W g (v 0) = v 0; rw [h0,map_zero]
        · exact hg
    exact (MulEquiv.subgroupCongr he).trans
      (BinaryLinearThree.OrbitStabilizers.naturalEquivSymmetric (v 1) h1)
  · have h1 : v 1 = 0 := (hv.resolve_right (fun h => h0 h.1)).2
    have he : vectorStabilizer rho v = BinaryLinearThree.OrbitStabilizers.natural (v 0) := by
      ext g
      rw [BinaryLinearThree.OrbitStabilizers.mem_natural]
      constructor
      · intro hg; exact congrFun hg 0
      · intro hg
        change rho g v = v
        funext i
        fin_cases i
        · exact hg
        · change W g (v 1) = v 1; rw [h1,map_zero]
    exact (MulEquiv.subgroupCongr he).trans
      (BinaryLinearThree.OrbitStabilizers.naturalEquivSymmetric (v 0) h0)

/-- The stabilizer for the actual component times multiplicity involution. -/
@[expose] def outerStabilizer (v : V) : Subgroup (BinaryLinearThree.Group × Equiv.Perm (Fin 2)) where
  carrier := {g | outerRepresentation g v = v}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    change outerRepresentation (g*h) v = v
    rw [map_mul,Module.End.mul_apply,hh,hg]
  inv_mem' := by
    intro g hg
    have he := congrArg (outerRepresentation g⁻¹) hg
    simpa using he.symm

theorem outer_stabilizer_index (v : V) :
    (outerStabilizer v).index = Nat.card (Set.range (fun g => outerRepresentation g v)) := by
  let : MulAction (BinaryLinearThree.Group × Equiv.Perm (Fin 2)) V := {
    smul := fun g w => outerRepresentation g w
    one_smul := fun w => LinearMap.congr_fun outerRepresentation.map_one w
    mul_smul := fun g h w => LinearMap.congr_fun (outerRepresentation.map_mul g h) w }
  exact MulAction.index_stabilizer (BinaryLinearThree.Group × Equiv.Perm (Fin 2)) v

theorem independent_outer_orbit (v : V) (hv : v ∈ independent) :
    Set.range (fun g => outerRepresentation g v) = independent := by
  apply Set.Subset.antisymm
  · rintro w ⟨⟨g,s⟩,rfl⟩
    have hswap : (fun i => v (s.symm i)) ∈ independent := by
      rcases perm_two s with rfl | rfl
      · exact hv
      · exact ⟨hv.2.1,hv.1,Ne.symm hv.2.2⟩
    rw [← independent_orbit _ hswap]
    exact ⟨g,rfl⟩
  · intro w hw
    obtain ⟨g,hg⟩ := (independent_orbit v hv).symm ▸ hw
    exact ⟨(g,1),hg⟩

theorem independent_outer_index (v : V) (hv : v ∈ independent) :
    (outerStabilizer v).index = 42 := by
  rw [outer_stabilizer_index,independent_outer_orbit v hv,independent_card]

theorem rankOne_outer_index (v : V) (hv : v ∈ rankOne) :
    (outerStabilizer v).index = 14 := by
  rw [outer_stabilizer_index,rankOne_orbit v hv,rankOne_card]

/-- The diagonal natural copy is preserved by both the component and the swap. -/
@[expose] def diagonal : Submodule (ZMod 2) V where
  carrier := {v | v 0 = v 1}
  zero_mem' := rfl
  add_mem' := by intro v w hv hw; change v 0 + w 0 = v 1 + w 1; rw [hv,hw]
  smul_mem' := by intro c v hv; change c • v 0 = c • v 1; rw [hv]

/-- The nonzero diagonal vectors form one seven-point orbit. -/
theorem diagonal_orbit (v : V) (hv : v ∈ diagonal) (h0 : v ≠ 0) :
    Set.range (fun g => outerRepresentation g v) = {w : V | w ∈ diagonal ∧ w ≠ 0} := by
  have hv0 : v 0 ≠ 0 := by
    intro hh
    apply h0
    funext i
    fin_cases i
    · exact hh
    · exact hv.symm.trans hh
  have hc (s : Equiv.Perm (Fin 2)) : (fun i => v (s.symm i)) = v := by
    rcases perm_two s with rfl | rfl
    · rfl
    · funext i; fin_cases i; exact hv.symm; exact hv
  ext w
  constructor
  · rintro ⟨⟨g,s⟩,rfl⟩
    change (rho g (fun i => v (s.symm i))) ∈ diagonal ∧
      rho g (fun i => v (s.symm i)) ≠ 0
    rw [hc]
    refine ⟨congrArg (W g) hv,?_⟩
    intro he
    have hh := congrFun he 0
    change W g (v 0) = 0 at hh
    apply hv0
    simpa using congrArg (W g⁻¹) hh
  · rintro ⟨hw,hw0⟩
    have hww : w 0 ≠ 0 := by
      intro hh
      apply hw0
      funext i
      fin_cases i
      · exact hh
      · exact hw.symm.trans hh
    obtain ⟨g,hg⟩ := natural_transitive_nonzero (v 0) (w 0) hv0 hww
    refine ⟨(g,1),?_⟩
    funext i
    fin_cases i
    · exact hg
    · change W g (v 1) = w 1
      rw [← hv,← hw,hg]

theorem diagonal_outer_index (v : V) (hv : v ∈ diagonal) (h0 : v ≠ 0) :
    (outerStabilizer v).index = 7 := by
  rw [outer_stabilizer_index,diagonal_orbit v hv h0]
  change Nat.card {w : V // w 0 = w 1 ∧ w ≠ 0} = 7
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem vector_cases (v : V) :
    v = 0 ∨ v ∈ diagonal ∨ v ∈ rankOne ∨ v ∈ independent := by
  by_cases h0 : v 0 = 0
  · by_cases h1 : v 1 = 0
    · left; funext i; fin_cases i; exact h0; exact h1
    · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨h0,h1⟩)))
  · by_cases h1 : v 1 = 0
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨h0,h1⟩)))
    · by_cases he : v 0 = v 1
      · exact Or.inr (Or.inl he)
      · exact Or.inr (Or.inr (Or.inr ⟨h0,h1,he⟩))

theorem outer_index_not_four (v : V) : ¬ 4 ∣ (outerStabilizer v).index := by
  rcases vector_cases v with rfl | hd | hr | hi
  · have he : outerStabilizer 0 = ⊤ := by ext g; simp [outerStabilizer]
    rw [he,index_top]
    decide
  · by_cases hz : v = 0
    · subst v; have he : outerStabilizer 0 = ⊤ := by ext g; simp [outerStabilizer]
      rw [he,index_top]; decide
    · rw [diagonal_outer_index v hd hz]; decide
  · rw [rankOne_outer_index v hr]; decide
  · rw [independent_outer_index v hi]; decide

@[expose] def firstCopy : Submodule (ZMod 2) V where
  carrier := {v | v 1 = 0}
  zero_mem' := rfl
  add_mem' := by intro v w hv hw; change v 1 + w 1 = 0; rw [hv,hw,add_zero]
  smul_mem' := by intro c v hv; change c • v 1 = 0; rw [hv,smul_zero]

@[expose] def secondCopy : Submodule (ZMod 2) V where
  carrier := {v | v 0 = 0}
  zero_mem' := rfl
  add_mem' := by intro v w hv hw; change v 0 + w 0 = 0; rw [hv,hw,add_zero]
  smul_mem' := by intro c v hv; change c • v 0 = 0; rw [hv,smul_zero]

/-- Every embedded natural module is one of the three actual natural copies. -/
theorem natural_copy_classification (e : W.IntertwiningMap rho)
    (he : Function.Injective e) :
    e.toLinearMap.range = firstCopy ∨ e.toLinearMap.range = secondCopy ∨
      e.toLinearMap.range = diagonal := by
  let f (i : Fin 2) : Vector →+ Vector := {
    toFun v := e v i
    map_zero' := by simp
    map_add' x y := congrFun (map_add e x y) i }
  have hf (i : Fin 2) (g : BinaryLinearThree.Group) (v : Vector) :
      f i (g.val.mulVec v) = g.val.mulVec (f i v) := by
    exact congrFun (congrArg (fun f : Vector →ₗ[ZMod 2] V => f v) (e.isIntertwining' g)) i
  obtain ⟨a,ha⟩ := natural_centralizer_scalar (f 0) (hf 0)
  obtain ⟨b,hb⟩ := natural_centralizer_scalar (f 1) (hf 1)
  have ha' (v : Vector) : e v 0 = a • v := ha v
  have hb' (v : Vector) : e v 1 = b • v := hb v
  have ha2 : a = 0 ∨ a = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) a
  have hb2 : b = 0 ∨ b = 1 := (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) b
  rcases ha2 with rfl | rfl <;> rcases hb2 with rfl | rfl
  · have he0 : e (![1,0,0] : Vector) = e 0 := by
      funext i
      fin_cases i <;> simp [ha',hb']
    exact False.elim ((by decide : (![1,0,0] : Vector) ≠ 0) (he he0))
  · right; left
    ext v
    change (∃ w, e w = v) ↔ v 0 = 0
    constructor
    · rintro ⟨w,rfl⟩; simp [ha']
    · intro hv
      refine ⟨v 1,?_⟩
      funext i
      fin_cases i <;> simp [ha',hb',hv]
  · left
    ext v
    change (∃ w, e w = v) ↔ v 1 = 0
    constructor
    · rintro ⟨w,rfl⟩; simp [hb']
    · intro hv
      refine ⟨v 0,?_⟩
      funext i
      fin_cases i <;> simp [ha',hb',hv]
  · right; right
    ext v
    change (∃ w, e w = v) ↔ v 0 = v 1
    constructor
    · rintro ⟨w,rfl⟩; simp [ha',hb']
    · intro hv
      refine ⟨v 0,?_⟩
      funext i
      fin_cases i <;> simp [ha',hb',hv]

/-- Among the natural copies, only the diagonal is invariant under an actor
whose multiplicity part is the original column swap. -/
theorem unique_swap_invariant_copy (g : BinaryLinearThree.Group)
    (e : W.IntertwiningMap rho) (he : Function.Injective e)
    (hi : ∀ v ∈ e.toLinearMap.range,
      outerRepresentation (g,Equiv.swap 0 1) v ∈ e.toLinearMap.range) :
    e.toLinearMap.range = diagonal := by
  rcases natural_copy_classification e he with hc | hc | hc
  · have hv : (![![1,0,0],0] : V) ∈ e.toLinearMap.range := by rw [hc]; rfl
    have hh := hi _ hv
    rw [hc] at hh
    change W g (![1,0,0] : Vector) = 0 at hh
    have hzero := congrArg (W g⁻¹) hh
    simp at hzero
  · have hv : (![0,![1,0,0]] : V) ∈ e.toLinearMap.range := by rw [hc]; rfl
    have hh := hi _ hv
    rw [hc] at hh
    change W g (![1,0,0] : Vector) = 0 at hh
    have hzero := congrArg (W g⁻¹) hh
    simp at hzero
  · exact hc

/-- The diagonal embedding is an actual natural-module isomorphism onto its range. -/
@[expose] def diagonalEmbedding : W.IntertwiningMap rho where
  toFun v _ := v
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

theorem diagonalEmbedding_injective : Function.Injective diagonalEmbedding := by
  intro v w h
  exact congrFun h 0

theorem diagonalEmbedding_range : diagonalEmbedding.toLinearMap.range = diagonal := by
  ext v
  change (∃ w, (fun _ : Fin 2 => w) = v) ↔ v 0 = v 1
  constructor
  · rintro ⟨w,rfl⟩; rfl
  · intro hv
    refine ⟨v 0,?_⟩
    funext i
    fin_cases i
    · rfl
    · exact hv

theorem diagonal_invariant (g : BinaryLinearThree.Group × Equiv.Perm (Fin 2))
    (v : V) (hv : v ∈ diagonal) : outerRepresentation g v ∈ diagonal := by
  rcases g with ⟨g,s⟩
  rcases perm_two s with rfl | rfl
  · exact congrArg (W g) hv
  · exact congrArg (W g) hv.symm

/-- A commuting actor has trivial SL₃ component; only the marked swap can remain. -/
theorem commuting_actor_component (g : BinaryLinearThree.Group) (s : Equiv.Perm (Fin 2))
    (hc : ∀ k v, outerRepresentation (g,s) (rho k v) = rho k (outerRepresentation (g,s) v)) :
    g = 1 := by
  have hg : g ∈ Subgroup.center BinaryLinearThree.Group := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Representation.SL3DoubledNaturalOffenders.representation_injective (ZMod 2)
    rw [map_mul,map_mul]
    apply LinearMap.ext
    intro v
    funext i
    have he := congrFun (hc k (fun _ : Fin 2 => v i)) 0
    change W k (W g (v i)) = W g (W k (v i))
    exact he.symm
  rw [Matrix.PSL3Two.center_eq_bot] at hg
  exact hg

/-- Away from the diagonal copy, a commuting point fixer is the identity actor. -/
theorem commuting_fixer_trivial (g : BinaryLinearThree.Group) (s : Equiv.Perm (Fin 2))
    (hc : ∀ k v, outerRepresentation (g,s) (rho k v) = rho k (outerRepresentation (g,s) v))
    (v : V) (hv : v ∉ diagonal) (hf : outerRepresentation (g,s) v = v) :
    (g,s) = 1 := by
  have hg := commuting_actor_component g s hc
  subst g
  rcases perm_two s with rfl | rfl
  · rfl
  · apply False.elim
    apply hv
    have he := congrFun hf 0
    change W 1 (v 1) = v 0 at he
    change v 0 = v 1
    simpa using he.symm

/-- The nonzero diagonal copy has the same component stabilizer S₄. -/
def diagonalStabilizerEquiv (v : V) (hv : v ∈ diagonal) (h0 : v ≠ 0) :
    vectorStabilizer rho v ≃* Equiv.Perm (Fin 4) := by
  have hv0 : v 0 ≠ 0 := by
    intro hh
    apply h0
    funext i
    fin_cases i
    · exact hh
    · exact hv.symm.trans hh
  have he : vectorStabilizer rho v = BinaryLinearThree.OrbitStabilizers.natural (v 0) := by
    ext g
    rw [BinaryLinearThree.OrbitStabilizers.mem_natural]
    constructor
    · intro hg; exact congrFun hg 0
    · intro hg
      change rho g v = v
      funext i
      fin_cases i
      · exact hg
      · change W g (v 1) = v 1
        rw [← hv,hg]
  exact (MulEquiv.subgroupCongr he).trans
    (BinaryLinearThree.OrbitStabilizers.naturalEquivSymmetric (v 0) hv0)

def dependentStabilizerEquiv (v : V) (h0 : v ≠ 0) (hi : v ∉ independent) :
    vectorStabilizer rho v ≃* Equiv.Perm (Fin 4) := by
  by_cases hd : v ∈ diagonal
  · exact diagonalStabilizerEquiv v hd h0
  · have hr := (((vector_cases v).resolve_left h0).resolve_left hd).resolve_right hi
    exact rankOneStabilizerEquiv v hr

theorem dependent_inner_index (v : V) (h0 : v ≠ 0) (hi : v ∉ independent) :
    (vectorStabilizer rho v).index = 7 := by
  have hc := (vectorStabilizer rho v).card_mul_index
  rw [Nat.card_congr (dependentStabilizerEquiv v h0 hi).toEquiv,
    Nat.card_perm,Nat.card_fin,Matrix.PSL3Two.card_SL] at hc
  norm_num [Nat.factorial] at hc
  omega

theorem inner_index_not_four (v : V) : ¬ 4 ∣ (vectorStabilizer rho v).index := by
  by_cases hz : v = 0
  · subst v
    have he : vectorStabilizer rho 0 = ⊤ := by ext g; simp [vectorStabilizer]
    rw [he,index_top]
    decide
  · by_cases hi : v ∈ independent
    · rw [independent_stabilizer_index v hi]; decide
    · rw [dependent_inner_index v hz hi]; decide

end Representation.SL3DoubledNaturalOffenders.BinaryOrbits
