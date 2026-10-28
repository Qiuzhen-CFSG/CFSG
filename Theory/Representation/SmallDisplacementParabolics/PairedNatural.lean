module
public import Theory.Representation.SmallDisplacementParabolics.PairedAction
public import Theory.Representation.SmallDisplacementParabolics.Transport
public import Theory.GroupTheory.RegularWreathSubgroup
public import Theory.SpecificGroups.PSL3Two.Parabolics.Subgroups.Bruhat

/-!
# Moving plane parabolics in the paired binary natural module

Use the upper triangular Sylow and plane stabilizer in each SL₃(2) factor,
with the same factor swap. The upper triangular subgroup is maximal and
self-normalizing inside the plane stabilizer. The regular-wreath subgroup
lemma therefore proves the required absence of intermediate overgroups.
Two root matrices force Sylow-fixed vectors onto the first coordinate line;
the plane reflection moves every nonzero such paired vector. The Sylow
supplement theorem passes this movement to the literal embedded two-residual.

The matrix-to-linear isomorphism and Sylow conjugacy preserve the inverse
shift in `pairedRepresentation`. Actual actor and module markings then give
the third `ActionModel` branch on an arbitrary source carrier.

Source: Aschbacher--Smith, original 15.2.27(2), printed p.1119 (PDF p.1136).
-/

public noncomputable section
open Subgroup
namespace Representation.SmallDisplacementParabolics.PairedNatural
open Matrix.PSL3Two
open BinaryLinear.OuterCyclic

private abbrev B := borelSL.subgroupOf lineParabolicSL

private theorem borel_index : B.index = 3 := by
  have hc : Nat.card B = 8 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe (show borelSL ≤ lineParabolicSL from inf_le_right)).toEquiv,
      card_borelSL]
  have h := B.card_mul_index
  rw [hc, card_lineParabolicSL] at h
  omega

private theorem borel_maximal : IsCoatom B := by
  refine ⟨?_, ?_⟩
  · intro h
    have := borel_index
    rw [h, index_top] at this
    omega
  · intro K hK
    have hprod := relIndex_mul_index hK.le
    have hp : (B.relIndex K * K.index).Prime := by
      rw [hprod, borel_index]
      decide
    rcases Nat.prime_mul_iff.mp hp with ⟨_, hKi⟩ | ⟨_, hBi⟩
    · exact index_eq_one.mp hKi
    · exact (hK.not_ge (relIndex_eq_one.mp hBi)).elim

private def planeSwap : SL := ⟨!![0,1,0; 1,0,0; 0,0,1], by decide +kernel⟩
private theorem planeSwap_mem : planeSwap ∈ lineParabolicSL := by decide +kernel

private theorem planeSwap_not_normalizes :
    planeSwap * Bruhat.upper 1 * planeSwap⁻¹ ∉ borelSL := by
  rw [mem_borelSL_iff]
  decide +kernel

private theorem coatom_self_normalizing {D : Type*} [Group D] (C : Subgroup D)
    (hC : IsCoatom C) (a x : D) (hx : x ∈ C) (ha : a * x * a⁻¹ ∉ C) :
    normalizer (C : Set D) = C := by
  apply le_antisymm _ C.le_normalizer
  by_contra hn
  have ht := hC.2 _ (lt_of_le_not_ge C.le_normalizer hn)
  have hm : a ∈ normalizer (C : Set D) := ht ▸ mem_top _
  exact ha ((mem_normalizer_iff.mp hm x).mp hx)

private theorem borel_self_normalizing : normalizer (B : Set lineParabolicSL) = B := by
  let a : lineParabolicSL := ⟨planeSwap, planeSwap_mem⟩
  let x : lineParabolicSL := ⟨Bruhat.upper 1,
    (show borelSL ≤ lineParabolicSL from inf_le_right) (Bruhat.upper_mem 1)⟩
  exact coatom_self_normalizing B borel_maximal a x (Bruhat.upper_mem 1)
    planeSwap_not_normalizes

private abbrev MatrixActor := RegularWreathProduct SL PairIndex
private abbrev matrixSylowGroup : Subgroup MatrixActor :=
  RegularWreathProduct.coordinateSubgroup borelSL
private abbrev matrixParabolic : Subgroup MatrixActor :=
  RegularWreathProduct.coordinateSubgroup lineParabolicSL

private theorem sylow_le_parabolic : matrixSylowGroup ≤ matrixParabolic :=
  fun _ hg i => (show borelSL ≤ lineParabolicSL from inf_le_right) (hg i)

private theorem standard_maximal : IsCoatom (matrixSylowGroup.subgroupOf matrixParabolic) := by
  let e : matrixParabolic ≃* RegularWreathProduct lineParabolicSL PairIndex := {
    toFun g := ⟨fun i => ⟨g.val.left i, g.property i⟩, g.val.right⟩
    invFun g := ⟨⟨fun i => (g.left i).val, g.right⟩, fun i => (g.left i).property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_mul' _ _ := rfl }
  have he : matrixSylowGroup.subgroupOf matrixParabolic =
      (RegularWreathProduct.coordinateSubgroup (Q := PairIndex) B).comap e.toMonoidHom := rfl
  rw [he]
  exact isCoatom_comap_of_surjective e.surjective
    (RegularWreathProduct.coordinateSubgroup_isCoatom B borel_maximal borel_self_normalizing)

private theorem matrixSylow_card : Nat.card matrixSylowGroup = 128 := by
  rw [Nat.card_congr (RegularWreathProduct.coordinateSubgroupEquiv (Q := PairIndex) borelSL).toEquiv,
    RegularWreathProduct.card, card_borelSL]
  norm_num [Nat.card_eq_fintype_card]

private def matrixSylow : Sylow 2 MatrixActor := Sylow.ofCard matrixSylowGroup (by
  rw [matrixSylow_card, RegularWreathProduct.card, card_SL]
  norm_num [Nat.card_eq_fintype_card]
  decide +kernel)

private def actorEquiv : MatrixActor ≃* PairedActor where
  toFun g := ⟨fun i => slEquivLinear 3 (g.left i), g.right⟩
  invFun g := ⟨fun i => (slEquivLinear 3).symm (g.left i), g.right⟩
  left_inv g := by ext <;> simp
  right_inv g := by ext <;> simp
  map_mul' g h := by ext <;> simp

private instance : Finite PairedActor := Finite.of_equiv MatrixActor actorEquiv.toEquiv

private abbrev matrixRepresentation := pairedRepresentation.comp actorEquiv.toMonoidHom

private theorem matrix_apply (g : MatrixActor) (w : PairIndex → ThreeSpace) (i : PairIndex) :
    matrixRepresentation g w i = (g.left i).val.mulVec (w (g.right⁻¹ * i)) := by
  change (slEquivLinear 3 (g.left i)) (w (g.right⁻¹ * i)) = _
  exact slEquivLinear_apply 3 _ _

private theorem standard_proper (Y : Subgroup MatrixActor)
    (hSY : matrixSylowGroup ≤ Y) (hYP : Y < matrixParabolic) :
    Y ≤ normalizer (matrixSylowGroup : Set MatrixActor) := by
  have he : Y = matrixSylowGroup := by
    by_contra hn
    have hlt : matrixSylowGroup.subgroupOf matrixParabolic < Y.subgroupOf matrixParabolic := by
      apply lt_of_le_not_ge (comap_mono hSY)
      intro hh
      apply hn
      exact le_antisymm (by
        intro y hy
        exact hh (show (⟨y,hYP.le hy⟩ : matrixParabolic) ∈ Y.subgroupOf matrixParabolic from hy)) hSY
    have ht := standard_maximal.2 _ hlt
    apply hYP.ne
    apply le_antisymm hYP.le
    intro y hy
    have hh : (⟨y,hy⟩ : matrixParabolic) ∈ Y.subgroupOf matrixParabolic := ht ▸ mem_top _
    exact hh
  rw [he]
  exact matrixSylowGroup.le_normalizer


private theorem standard_exists (w : PairIndex → ThreeSpace) (hw : w ≠ 0)
    (hfix : ∀ g ∈ matrixSylowGroup, matrixRepresentation g w = w) :
    Nonempty (MovingParabolic matrixRepresentation matrixSylow w) := by
  refine ⟨⟨matrixParabolic, sylow_le_parabolic, standard_proper, ?_⟩⟩
  apply residual_moves_of_moves _ matrixSylow w matrixParabolic sylow_le_parabolic hfix
  let g : MatrixActor := ⟨fun _ => planeSwap, 1⟩
  refine ⟨g, fun _ => planeSwap_mem, ?_⟩
  intro hm
  apply hw
  funext i
  have h1 : w i 1 = 0 := by
    have hh := congrArg (fun v : ThreeSpace => v 0)
      (congrFun (hfix (⟨fun _ => Bruhat.upper 1, 1⟩ : MatrixActor)
        (fun _ => Bruhat.upper_mem 1)) i)
    rw [matrix_apply] at hh
    simpa [Bruhat.upper, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hh
  have h2 : w i 2 = 0 := by
    have hh := congrArg (fun v : ThreeSpace => v 1)
      (congrFun (hfix (⟨fun _ => Bruhat.upper 4, 1⟩ : MatrixActor)
        (fun _ => Bruhat.upper_mem 4)) i)
    rw [matrix_apply] at hh
    simpa [Bruhat.upper, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using hh
  have hh := congrArg (fun v : ThreeSpace => v 1) (congrFun hm i)
  rw [matrix_apply] at hh
  change (planeSwap.val.mulVec (w (1⁻¹ * i))) 1 = w i 1 at hh
  simp only [inv_one, one_mul] at hh
  have h0 : w i 0 = 0 := by
    simpa [planeSwap, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1] using hh
  ext j
  fin_cases j <;> simp [h0, h1, h2]

/-- Every nonzero vector fixed by a Sylow in the paired natural action has
an actual moving plane parabolic. -/
theorem exists_moving (S : Sylow 2 PairedActor) (w : PairIndex → ThreeSpace)
    (hw : w ≠ 0) (hfix : ∀ g ∈ (S : Subgroup PairedActor), pairedRepresentation g w = w) :
    Nonempty (MovingParabolic pairedRepresentation S w) := by
  let e0 := actorEquiv.symm
  let S0 := S.mapSurjective (f := e0.toMonoidHom) e0.surjective
  obtain ⟨r,hr⟩ := MulAction.exists_smul_eq MatrixActor S0 matrixSylow
  let e := e0.trans (MulAut.conj r)
  let ρ := matrixRepresentation
  have hS : S.mapSurjective (f := e.toMonoidHom) e.surjective = matrixSylow := by
    apply Sylow.ext
    change (S : Subgroup PairedActor).map
      ((MulAut.conj r).toMonoidHom.comp e0.toMonoidHom) = _
    rw [← Subgroup.map_map]
    change ((r • S0 : Sylow 2 MatrixActor) : Subgroup MatrixActor) = _
    rw [hr]
  let f : (PairIndex → ThreeSpace) ≃ₗ[ZMod 2] (PairIndex → ThreeSpace) :=
    LinearEquiv.ofLinearMap (ρ r) (ρ r⁻¹)
      (by change ρ r * ρ r⁻¹ = 1; rw [← map_mul,mul_inv_cancel,map_one])
      (by change ρ r⁻¹ * ρ r = 1; rw [← map_mul,inv_mul_cancel,map_one])
  have hf (g : PairedActor) (v : PairIndex → ThreeSpace) :
      f (pairedRepresentation g v) = ρ (e g) (f v) := by
    have hρ : pairedRepresentation g = ρ (e0 g) := by
      change pairedRepresentation g = pairedRepresentation (actorEquiv (actorEquiv.symm g))
      rw [MulEquiv.apply_symm_apply]
    change ρ r (pairedRepresentation g v) = ρ (r * e0 g * r⁻¹) (ρ r v)
    rw [hρ]
    simp only [← Module.End.mul_apply, ← map_mul]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hw' : f w ≠ 0 := fun he => hw (f.injective (he.trans (map_zero f).symm))
  have hfix' : ∀ g ∈ matrixSylowGroup, ρ g (f w) = f w := by
    intro g hg
    have hm : g ∈ (S : Subgroup PairedActor).map e.toMonoidHom := by
      change g ∈ ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 MatrixActor) :
        Subgroup MatrixActor)
      rw [hS]
      exact hg
    obtain ⟨a,ha,rfl⟩ := hm
    exact (hf a w).symm.trans (congrArg f (hfix a ha))
  obtain ⟨d⟩ := standard_exists (f w) hw' hfix'
  have d' : MovingParabolic ρ (S.mapSurjective (f := e.toMonoidHom) e.surjective) (f w) :=
    hS.symm ▸ d
  exact ⟨MovingParabolic.comap pairedRepresentation ρ e f hf S w d'⟩

/-- Transfer of the paired calculation through the actual actor and module
markings used by `ActionModel`. -/
theorem exists_of_equiv {D W : Type*} [Group D] [Finite D] [AddCommGroup W]
    [Module (ZMod 2) W] (ρ : Representation (ZMod 2) D W)
    (e : D ≃* PairedActor) (E : W ≃ₗ[ZMod 2] (PairIndex → ThreeSpace))
    (hE : ∀ g w i, E (ρ g w) i = (e g).left i (E w ((e g).right⁻¹ * i)))
    (S : Sylow 2 D) (w : W) (hw : w ≠ 0)
    (hfix : ∀ g ∈ (S : Subgroup D), ρ g w = w) :
    Nonempty (MovingParabolic ρ S w) := by
  have hf (g : D) (v : W) : E (ρ g v) = pairedRepresentation (e g) (E v) :=
    funext (hE g v)
  have hw' : E w ≠ 0 := fun he => hw (E.injective (he.trans (map_zero E).symm))
  have hfix' : ∀ g ∈ ((S.mapSurjective (f := e.toMonoidHom) e.surjective : Sylow 2 PairedActor) :
      Subgroup PairedActor), pairedRepresentation g (E w) = E w := by
    rintro g ⟨a,ha,rfl⟩
    exact (hf a w).symm.trans (congrArg E (hfix a ha))
  obtain ⟨d⟩ := exists_moving _ (E w) hw' hfix'
  exact ⟨MovingParabolic.comap ρ pairedRepresentation e E hf S w d⟩

end Representation.SmallDisplacementParabolics.PairedNatural
