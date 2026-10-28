module
public import Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylowCensus
public import Theory.GroupTheory.CharacteristicCentralizerFusion
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceRow
import all Theory.GroupTheory.Recognition.TransvectionFive.UniquenessLinearSourceSylowCensus

/-!
# The mixed-core common centralizer in the binary degree-five model

The common centralizer of I+E₀₄ and I+E₀₃+E₁₄ is a proper subgroup of
the literal unitriangular Sylow. Its second derived subgroup is exactly
⟨I+E₀₄⟩. First-superdiagonal coordinates bound the Sylow's second derived
subgroup; three explicit root words produce the reverse containment for
the common centralizer. Entry equations give its Sylow containment.

These are the model facts in Aschbacher, *Sporadic Groups* (1994),
39.1(6) and 39.4, pp.213–214. `CoreFusionSeparation` transports this
characteristic line through the original marking to exclude ambient fusion.
-/

public noncomputable section
open Subgroup BinaryLinear.TransvectionFiveLocal
open scoped commutatorElement
namespace Theory.GroupTheory.TransvectionFive.CoreFusionModel
open UniquenessLinear SylowCoordinates
open Theory.SpecificGroups.LinearSylowNormalizers

private def firstDiagonal : upper →* Multiplicative (Fin 4 → ZMod 2) where
  toFun g := Multiplicative.ofAdd (fun i => (g : SL) i.castSucc i.succ)
  map_one' := by apply Multiplicative.toAdd.injective; funext i; fin_cases i <;> rfl
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    funext i
    change ((g : SL).val * (h : SL).val) i.castSucc i.succ = _
    fin_cases i <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, upper_entry, add_comm]

private theorem derived_entries (g : upper) (hg : g ∈ _root_.commutator upper) :
    (g : SL) 0 1 = 0 ∧ (g : SL) 1 2 = 0 ∧ (g : SL) 2 3 = 0 ∧ (g : SL) 3 4 = 0 := by
  have he := Abelianization.commutator_subset_ker firstDiagonal hg
  have he' : (fun i : Fin 4 => (g : SL) i.castSucc i.succ) = 0 :=
    congrArg Multiplicative.toAdd he
  exact ⟨congrFun he' 0, congrFun he' 1, congrFun he' 2, congrFun he' 3⟩

private theorem upper_matrix (g : upper) : (g : SL).val =
    !![1, (g : SL) 0 1, (g : SL) 0 2, (g : SL) 0 3, (g : SL) 0 4;
       0, 1, (g : SL) 1 2, (g : SL) 1 3, (g : SL) 1 4;
       0, 0, 1, (g : SL) 2 3, (g : SL) 2 4;
       0, 0, 0, 1, (g : SL) 3 4;
       0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [upper_entry]

private theorem derived_commutator (g h : upper)
    (hg : g ∈ _root_.commutator upper) (hh : h ∈ _root_.commutator upper) :
    (⁅g,h⁆ : upper).val ∈ zpowers transvection := by
  obtain ⟨hg01,hg12,hg23,hg34⟩ := derived_entries g hg
  obtain ⟨hh01,hh12,hh23,hh34⟩ := derived_entries h hh
  let a : ZMod 2 := (g : SL) 0 2 * (h : SL) 2 4 + (h : SL) 0 2 * (g : SL) 2 4
  let r : SL := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 5) ≠ 4) a
  have he : (g : SL) * h = r * ((h : SL) * g) := by
    apply Subtype.ext
    change (g : SL).val * (h : SL).val = r.val * ((h : SL).val * (g : SL).val)
    rw [upper_matrix g, upper_matrix h]
    simp only [hg01,hg12,hg23,hg34,hh01,hh12,hh23,hh34]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [r,a,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_apply,
        Fin.sum_univ_succ,Matrix.single,Matrix.one_apply]
    all_goals ring_nf
    all_goals simp [show (2 : ZMod 2) = 0 from rfl]
  have hc : (⁅g,h⁆ : upper).val = r := by
    change (g : SL) * h * (g : SL)⁻¹ * (h : SL)⁻¹ = r
    rw [he]
    group
  rw [hc]
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with ha | ha
  · simp [r,ha]
  · change Matrix.SpecialLinearGroup.transvection _ a ∈ zpowers transvection
    rw [ha]
    exact mem_zpowers transvection

/-- The second derived subgroup of the root Sylow lies in the marked point line. -/
theorem upper_second_derived_le : (derivedSeries upper 2).map upper.subtype ≤ zpowers transvection := by
  rw [derivedSeries_succ, map_commutator]
  apply commutator_le.mpr
  rintro _ ⟨g,hg,rfl⟩ _ ⟨h,hh,rfl⟩
  exact derived_commutator g h hg hh

/-- A representative of the mixed core orbit. -/
@[expose] def mixed : SL := root (by decide : (0 : Fin 5) < 3) * root (by decide : (1 : Fin 5) < 4)
@[expose] def common : Subgroup SL := centralizer ⊓ Subgroup.centralizer ({mixed} : Set SL)

private theorem mixed_matrix : mixed.val = 1 + Matrix.single 0 3 1 + Matrix.single 1 4 1 := by
  simp [mixed,root,Matrix.SpecialLinearGroup.transvection_coe,Matrix.mul_add,Matrix.add_mul,
    Matrix.single_mul_single_of_ne,add_assoc]

private theorem single_right (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (i j k l : Fin 5) :
    (M * Matrix.single i j 1 : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l = if l = j then M k i else 0 := by
  by_cases he : l = j
  · subst l; simp
  · simp [he]

private theorem single_left (M : Matrix (Fin 5) (Fin 5) (ZMod 2)) (i j k l : Fin 5) :
    (Matrix.single i j 1 * M : Matrix (Fin 5) (Fin 5) (ZMod 2)) k l = if k = i then M j l else 0 := by
  by_cases he : k = i
  · subst k; simp
  · simp [he]

private theorem fin5_eq (i j : Fin 5) : i = j ↔ i.val = j.val := Fin.ext_iff

private theorem common_entries (g : common) :
    (g : SL) 1 0 = 0 ∧ (g : SL) 2 0 = 0 ∧ (g : SL) 3 0 = 0 ∧ (g : SL) 4 0 = 0 ∧
    (g : SL) 2 1 = 0 ∧ (g : SL) 3 1 = 0 ∧ (g : SL) 4 1 = 0 ∧
    (g : SL) 3 2 = 0 ∧ (g : SL) 4 2 = 0 ∧ (g : SL) 4 3 = 0 ∧
    (g : SL) 0 0 = 1 ∧ (g : SL) 1 1 = 1 ∧ (g : SL) 3 3 = 1 ∧ (g : SL) 4 4 = 1 ∧
    (g : SL) 0 1 = (g : SL) 3 4 := by
  have h0 := centralizer_firstColumn g g.property.1
  have ht := mem_centralizer_singleton_iff.mp g.property.1
  have hm := mem_centralizer_singleton_iff.mp g.property.2
  have et (i j : Fin 5) := congrArg (fun a : SL => a i j) ht
  have em (i j : Fin 5) := congrArg (fun a : SL => a i j) hm
  change ∀ i j, ((g : SL).val * transvection.val) i j = (transvection.val * (g : SL).val) i j at et
  change ∀ i j, ((g : SL).val * mixed.val) i j = (mixed.val * (g : SL).val) i j at em
  simp only [mixed_matrix] at em
  simp only [transvection,root,Matrix.SpecialLinearGroup.transvection_coe] at et
  have ht' := And.intro (et 0 1) (And.intro (et 0 2) (And.intro (et 0 3) (et 0 4)))
  have hm' := And.intro (em 2 4) (And.intro (em 3 4)
    (And.intro (em 4 4) (And.intro (em 0 2) (And.intro (em 0 3)
      (And.intro (em 1 4) (em 0 4))))))
  norm_num [Matrix.mul_add,Matrix.add_mul,single_left,single_right,fin5_eq] at ht' hm'
  have h00 : (g : SL) 0 0 = 1 := h0 0
  have h10 : (g : SL) 1 0 = 0 := h0 1
  have h20 : (g : SL) 2 0 = 0 := h0 2
  have h30 : (g : SL) 3 0 = 0 := h0 3
  have h40 : (g : SL) 4 0 = 0 := h0 4
  rcases ht' with ⟨e41,e42,e43,e44⟩
  rcases hm' with ⟨e21,e31,_,e32,e33,e11,e01⟩
  exact ⟨h10,h20,h30,h40,e21,e31,e41,e32,e42,e43,h00,
    e11.trans (e44.symm.trans h00),e33.symm.trans h00,e44.symm.trans h00,e01⟩

/-- The common centralizer lies in the literal marked root Sylow. -/
theorem common_le_upper : common ≤ upper := by
  intro g hg
  obtain ⟨h10,h20,h30,h40,h21,h31,h41,h32,h42,h43,h00,h11,h33,h44,_⟩ :=
    common_entries ⟨g,hg⟩
  dsimp only at h10 h20 h30 h40 h21 h31 h41 h32 h42 h43 h00 h11 h33 h44
  have hu : g.val.IsUpperTriangular := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  have h22 : g 2 2 = 1 := by
    have hd := g.property
    rw [Matrix.det_of_isUpperTriangular hu] at hd
    simp only [Fin.prod_univ_succ] at hd
    change g 0 0 * (g 1 1 * (g 2 2 * (g 3 3 * (g 4 4 * 1)))) = 1 at hd
    simpa only [h00,h11,h33,h44,mul_one,one_mul] using hd
  rw [model_upper_eq_unipotent,mem_unipotent]
  refine ⟨(mem_borel 5 (ZMod 2) g).mpr hu, ?_⟩
  intro i
  fin_cases i <;> assumption

/-- This common centralizer is proper in that Sylow. -/
theorem common_lt_upper : common < upper := by
  refine lt_of_le_of_ne common_le_upper ?_
  intro he
  have hm : root (by decide : (0 : Fin 5) < 1) ∈ common := by
    rw [he]
    exact subset_closure ⟨0,1,by decide,rfl⟩
  have hf := (common_entries ⟨_,hm⟩).2.2.2.2.2.2.2.2.2.2.2.2.2.2
  norm_num [root,Matrix.SpecialLinearGroup.transvection_coe,Matrix.single,Matrix.one_apply] at hf
  exact zero_ne_one hf.symm

private def a : SL := root (by decide : (0 : Fin 5) < 1) * root (by decide : (3 : Fin 5) < 4)
private def b : SL := root (by decide : (1 : Fin 5) < 2)
private def c : SL := root (by decide : (2 : Fin 5) < 3)

private theorem a_mem : a ∈ common := by
  constructor <;> apply mem_centralizer_singleton_iff.mpr <;> decide +kernel
private theorem b_mem : b ∈ common := by
  constructor <;> apply mem_centralizer_singleton_iff.mpr <;> decide +kernel
private theorem c_mem : c ∈ common := by
  constructor <;> apply mem_centralizer_singleton_iff.mpr <;> decide +kernel

private theorem comm_of_mul {x y r : SL} (h : x*y = r*(y*x)) : ⁅x,y⁆ = r := by
  rw [commutatorElement_def,h]
  group

private theorem ab : ⁅a,b⁆ = root (by decide : (0 : Fin 5) < 2) :=
  comm_of_mul (by decide +kernel)
private theorem ca : ⁅c,a⁆ = root (by decide : (2 : Fin 5) < 4) :=
  comm_of_mul (by decide +kernel)
private theorem abca : ⁅⁅a,b⁆,⁅c,a⁆⁆ = transvection := by
  rw [ab,ca]
  exact comm_of_mul (by decide +kernel)

/-- The second derived subgroup of the common centralizer is exactly the point line. -/
theorem common_second_derived :
    (derivedSeries common 2).map common.subtype = zpowers transvection := by
  apply le_antisymm
  · let f : common →* upper := inclusion common_le_upper
    have h := map_derivedSeries_le_derivedSeries f 2
    have h' := map_mono (f := upper.subtype) h
    rw [map_map] at h'
    exact h'.trans upper_second_derived_le
  · apply zpowers_le.mpr
    let aa : common := ⟨a,a_mem⟩
    let bb : common := ⟨b,b_mem⟩
    let cc : common := ⟨c,c_mem⟩
    have hd : ⁅⁅aa,bb⁆,⁅cc,aa⁆⁆ ∈ derivedSeries common 2 :=
      commutator_mem_commutator
        (commutator_mem_commutator (mem_top _) (mem_top _))
        (commutator_mem_commutator (mem_top _) (mem_top _))
    exact ⟨_,hd,abca⟩

end Theory.GroupTheory.TransvectionFive.CoreFusionModel
