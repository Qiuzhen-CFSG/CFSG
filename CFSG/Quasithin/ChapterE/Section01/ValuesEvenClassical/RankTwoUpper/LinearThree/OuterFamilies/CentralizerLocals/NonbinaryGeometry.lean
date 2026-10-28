module

public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.CentralizerLocals.Geometry
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.Action
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThree.LocalMembers
public import CFSG.Quasithin.ChapterE.Section01.ValuesEvenClassical.RankTwoUpper.LinearThreeCover
public import Theory.GroupTheory.ElementaryActorCentralizerSylow
public import Theory.SpecificGroups.PSL3Even.AutomorphismTwoRank.StandardRank
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.Models
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.StandardGeneration
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.Selection
public import Theory.SpecificGroups.PSL3Even.NonbinaryCentralizer.FixedGeneration
public import Theory.SpecificGroups.PSL3Even.OuterElementaryRank.FixedRanks

/-!
# Nonbinary outer-centralizer geometry: model transport and assembly

The literal relative centralizer L ∩ C_G(z), viewed inside C_G(z), is
isomorphic to the fixed subgroup of the marked PSL₃ action. The preimage
of T under the model embedding is exactly the standard unipotent Sylow;
hence every element of T preserves that subgroup. This transfers model
generation to the original marked T even after arranging a Sylow centralizer.
The whole elementary actor is retained. Its intersection with L is nontrivial
because its rank exceeds two and the actual outer image has two-rank at most two.

At exact actor rank f + 1, the mixed graph-field fixed-rank bound supplies
the graph/field selection. The actual fixed-group identifications prove
simplicity and perfectness, and marked conjugacy supplies generation with
the original unipotent subgroup. `simpleCentralizerGeometry_of_exact_rank`
discharges all model premises of the retained conditional assembly. This
geometry needs neither SQTK nor G = LT; the parent uses G = LT to derive
the E2 clauses from it.

Source: Aschbacher–Smith E.1.1–6 and E.1.14(1), printed pp.209–214;
GLS3, Theorem 2.5.12 and §2.7. The parent CentralizerLocals adapter derives
all E2 clauses from the resulting SimpleCentralizerGeometry.
-/

public section
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open scoped MatrixGroups

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.NonbinaryGeometry
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Finite G] [Finite F] in
private theorem embedding_injective (L : Subgroup G) (e : L ≃* PSL(3,F)) :
    Function.Injective (linearThreeEmbedding L e) :=
  Subtype.val_injective.comp e.symm.injective

omit [Finite F] in
theorem embedding_modelAction (e : generalizedFitting G ≃* PSL(3,F))
    (z : G) (x : PSL(3,F)) :
    linearThreeEmbedding _ e (modelAction e z x) =
      (MulAut.conj z) (linearThreeEmbedding _ e x) := by
  change (e.symm (e (MulAut.conjNormal z (e.symm x))) : G) = _
  rw [e.symm_apply_apply]
  rfl

omit [Finite F] in
theorem modelAction_fixed_iff (e : generalizedFitting G ≃* PSL(3,F))
    (z : G) (x : PSL(3,F)) :
    modelAction e z x = x ↔
      linearThreeEmbedding _ e x ∈ centralizer ({z} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro hx
    have h := congrArg (linearThreeEmbedding _ e) hx
    rw [embedding_modelAction, MulAut.conj_apply] at h
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  · intro hx
    apply embedding_injective _ e
    rw [embedding_modelAction, MulAut.conj_apply]
    exact mul_inv_eq_iff_eq_mul.mpr hx.symm

omit [Finite F] in
noncomputable def innerCentralizerEquivFixed (e : generalizedFitting G ≃* PSL(3,F))
    (z : G) : (generalizedFitting G).subgroupOf (centralizer ({z} : Set G)) ≃*
      (modelAction e z).fixedSubgroup where
  toFun x := ⟨e ⟨x.val.val, x.property⟩, by
    rw [MulAut.mem_fixedSubgroup, modelAction_fixed_iff]
    simpa only [linearThreeEmbedding, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply, Subgroup.coe_subtype] using x.val.property⟩
  invFun x := ⟨⟨linearThreeEmbedding _ e x.val,
    (modelAction_fixed_iff e z x.val).mp ((MulAut.mem_fixedSubgroup _ _).mp x.property)⟩,
    (e.symm x.val).property⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    change (e.symm (e ⟨x.val.val, x.property⟩) : G) = x.val.val
    rw [e.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    exact e.apply_symm_apply x.val
  map_mul' x y := by
    apply Subtype.ext
    exact e.map_mul ⟨x.val.val, x.property⟩ ⟨y.val.val, y.property⟩

omit [Finite F] in
theorem socle_le_centralizer_sup_of_fixed_generation
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Subgroup G) (z : G)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ T)
    (hgen : (modelAction e z).fixedSubgroup ⊔ unipotent F = ⊤) :
    generalizedFitting G ≤ centralizer ({z} : Set G) ⊔ T := by
  have hC : (modelAction e z).fixedSubgroup.map (linearThreeEmbedding _ e) ≤
      centralizer ({z} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (modelAction_fixed_iff e z x).mp ((MulAut.mem_fixedSubgroup _ _).mp hx)
  calc
    generalizedFitting G = (⊤ : Subgroup PSL(3,F)).map (linearThreeEmbedding _ e) := by
      rw [← MonoidHom.range_eq_map, linearThreeEmbedding_range]
    _ = ((modelAction e z).fixedSubgroup ⊔ unipotent F).map
        (linearThreeEmbedding _ e) := by rw [hgen]
    _ ≤ centralizer ({z} : Set G) ⊔ T := by
      rw [Subgroup.map_sup]
      exact sup_le_sup hC hUT

theorem modelAction_preserves_unipotent
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 0 < f) (hF : Nat.card F = 2 ^ f)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ (T : Subgroup G))
    (z : G) (hz : z ∈ T) :
    (unipotent F).map (modelAction e z).toMonoidHom = unipotent F := by
  let j := linearThreeEmbedding _ e
  have hpre : (T : Subgroup G).comap j = unipotent F :=
    (unipotentSylow F hf hF).is_maximal'
      (T.isPGroup'.comap_of_injective j (embedding_injective _ e))
      (map_le_iff_le_comap.mp hUT)
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rw [← hpre]
    change j (modelAction e z x) ∈ T
    rw [embedding_modelAction, MulAut.conj_apply]
    have hxT : j x ∈ T := by
      change x ∈ (T : Subgroup G).comap j
      rwa [hpre]
    exact T.mul_mem (T.mul_mem hz hxT) (T.inv_mem hz)
  · intro x hx
    refine ⟨(modelAction e z)⁻¹ x, ?_, by simp⟩
    rw [← hpre]
    change j ((modelAction e z)⁻¹ x) ∈ T
    rw [← map_inv, embedding_modelAction, MulAut.conj_apply]
    have hxT : j x ∈ T := by
      change x ∈ (T : Subgroup G).comap j
      rwa [hpre]
    exact T.mul_mem (T.mul_mem (T.inv_mem hz) hxT) (T.inv_mem (T.inv_mem hz))

variable [IsSimpleGroup (generalizedFitting G)]

theorem inner_actor_ne_bot (e : generalizedFitting G ≃* PSL(3,F)) {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A) (hr : Group.rank A = f + 1) :
    A ⊓ generalizedFitting G ≠ ⊥ := by
  let := hA
  let q := QuotientGroup.mk' (MulAut.innerSubgroup PSL(3,F))
  let φ := q.comp (modelAction e)
  have hker : φ.ker = generalizedFitting G := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', modelAction_comap_inner]
  let ψ : A →* Matrix.PSL3.OuterSolvable.standardOuter F :=
    (φ.comp A.subtype).codRestrict _ (fun x =>
      mem_map_of_mem q ((modelAction_range_le_standard e (by omega) hF)
        ⟨x.val, rfl⟩))
  intro hbot
  have hinj : Function.Injective ψ := by
    apply (MonoidHom.ker_eq_bot_iff _).mp
    apply eq_bot_iff.mpr
    intro x hx
    have hφ : φ x.val = 1 := congrArg Subtype.val hx
    have hxL : x.val ∈ generalizedFitting G := by
      rw [← hker]
      exact hφ
    exact Subgroup.mem_bot.mpr (Subtype.ext
      (show x.val = 1 from (Subgroup.mem_bot.mp (hbot ▸ ⟨x.property, hxL⟩))))
  have hAr : Group.rank A ≤ primeRank 2 A := by
    have h := (⊤ : Subgroup A).rank_le_primeRank 2
      ((IsElementaryAbelian.isPGroup 2 A).to_subgroup ⊤)
    rwa [Group.rank_congr Subgroup.topEquiv] at h
  have hh := hAr.trans ((primeRank_le_of_injective 2 ψ hinj).trans
    (Matrix.PSL3.OuterSolvable.standardOuter_two_rank_le_of_two_power_card F
      (by omega) hF))
  omega
end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.NonbinaryGeometry

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.NonbinaryGeometry
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open Matrix.PSL3Even.NonbinaryCentralizer
open scoped MatrixGroups
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F]

omit [Finite F] in
/-- The standard graph calculation gives generation with the marked ambient Sylow. -/
theorem socle_le_centralizer_sup_of_graph [CharP F 2]
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Subgroup G) (z : G)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ T)
    (hz : modelAction e z = Matrix.PSL3.OuterSolvable.graph F) :
    generalizedFitting G ≤ centralizer ({z} : Set G) ⊔ T :=
  socle_le_centralizer_sup_of_fixed_generation e T z hUT (by rw [hz]; exact graph_fixed_sup_unipotent)

omit [Finite F] in
/-- The coefficient-action calculation gives generation with the same marked Sylow. -/
theorem socle_le_centralizer_sup_of_field [CharP F 2]
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Subgroup G) (z : G)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ T)
    (σ : F ≃+* F) (hz : modelAction e z = Matrix.PSL3.OuterSolvable.fieldAction F σ) :
    generalizedFitting G ≤ centralizer ({z} : Set G) ⊔ T :=
  socle_le_centralizer_sup_of_fixed_generation e T z hUT (by rw [hz]; exact field_fixed_sup_unipotent σ)

variable [IsSimpleGroup (generalizedFitting G)]

/-- Conditional assembly from two actual automorphism calculations: selecting
an outer graph/field actor, and its fixed-group structure and generation.
Every Sylow, literal-centralizer and whole-actor clause is proved here. -/
theorem simpleCentralizerGeometry_of_model_calculations
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ (T : Subgroup G))
    (hselect : ∀ E : Subgroup (MulAut PSL(3,F)), IsElementaryAbelian 2 E →
      E ≤ Matrix.PSL3.OuterSolvable.standard F →
      ¬ E ≤ MulAut.innerSubgroup PSL(3,F) → Group.rank E = f + 1 →
      ∃ a ∈ E, a ∉ MulAut.innerSubgroup PSL(3,F) ∧ IsGraphOrField a)
    (hfixed : ∀ a : MulAut PSL(3,F), IsGraphOrField a →
      IsSimpleGroup a.fixedSubgroup ∧ Group.IsPerfect a.fixedSubgroup)
    (hgenerate : ∀ a : MulAut PSL(3,F), IsGraphOrField a →
      (unipotent F).map a.toMonoidHom = unipotent F →
      a.fixedSubgroup ⊔ unipotent F = ⊤)
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (houter : ¬ A ≤ generalizedFitting G)
    (hrank : Group.rank A = f + 1) :
    SimpleCentralizerGeometry (generalizedFitting G) T A := by
  let := hA
  let E := A.map (modelAction e)
  have hE : IsElementaryAbelian 2 E := IsElementaryAbelian.map _
  have hES : E ≤ Matrix.PSL3.OuterSolvable.standard F :=
    (A.map_le_range _).trans (modelAction_range_le_standard e (by omega) hF)
  have hEO : ¬ E ≤ MulAut.innerSubgroup PSL(3,F) := by
    intro h
    apply houter
    have hh := map_le_iff_le_comap.mp h
    rwa [modelAction_comap_inner] at hh
  have hEr : Group.rank E = f + 1 :=
    (Group.rank_congr (A.equivMapOfInjective _ (modelAction_injective e))).symm.trans hrank
  obtain ⟨a, ha, haO, haM⟩ := hselect E hE hES hEO hEr
  obtain ⟨z, hzA, rfl⟩ := ha
  have hzL : z ∉ generalizedFitting G := by
    intro hz
    apply haO
    change z ∈ (MulAut.innerSubgroup PSL(3,F)).comap (modelAction e)
    rwa [modelAction_comap_inner]
  have hAC : A ≤ centralizer ({z} : Set G) := by
    intro x hx
    exact mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mul_comm' (⟨x,hx⟩ : A) ⟨z,hzA⟩))
  obtain ⟨g, hBT, S, hS⟩ := T.exists_conj_actor_with_sylow_centralizer A
    (IsElementaryAbelian.isPGroup 2 A) z (hAT hzA) hAC
  let B := A.map (MulAut.conj g).toMonoidHom
  let w := MulAut.conj g z
  have hwB : w ∈ B := mem_map_of_mem _ hzA
  have hwL : w ∉ generalizedFitting G := by
    intro hw
    have h := (inferInstance : (generalizedFitting G).Normal).conj_mem w hw g⁻¹
    apply hzL
    simpa [w, MulAut.conj_apply, mul_assoc] using h
  have hwM : IsGraphOrField (modelAction e w) := by
    have h := haM.conj (modelAction e g)
    simpa only [w, MulAut.conj_apply, map_mul, map_inv] using h
  obtain ⟨hsimple, hperfect⟩ := hfixed (modelAction e w) hwM
  let := hsimple
  let := hperfect
  let ef := innerCentralizerEquivFixed e w
  have hB : IsElementaryAbelian 2 B := IsElementaryAbelian.map _
  have hBr : Group.rank B = f + 1 :=
    (Group.rank_congr ((MulAut.conj g).subgroupMap A)).symm.trans hrank
  refine ⟨g, w, hBT, hwB, hwL, ⟨S, hS⟩, ef.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := ef.symm.toMonoidHom) ef.symm.surjective,
    inner_actor_ne_bot e hf hF B hB hBr, ?_⟩
  apply socle_le_centralizer_sup_of_fixed_generation e (T : Subgroup G) w hUT
  exact hgenerate (modelAction e w) hwM
    (modelAction_preserves_unipotent e T (by omega) hF hUT w (hBT hwB))

/-- The nonbinary geometry at exact rank, with actor selection, whole fixed-group
structure and marked generation all proved. This supplies the simple geometry
premise of the parent's E2 centralizer adapter under the source hypotheses of
E.1.14(1); SQTK and the supplement equation are not needed for this step. -/
theorem simpleCentralizerGeometry_of_exact_rank
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Sylow 2 G) {f : ℕ}
    (hf : 1 < f) (hF : Nat.card F = 2 ^ f)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ (T : Subgroup G))
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (hAT : A ≤ (T : Subgroup G)) (houter : ¬ A ≤ generalizedFitting G)
    (hrank : Group.rank A = f + 1) :
    SimpleCentralizerGeometry (generalizedFitting G) T A :=
  simpleCentralizerGeometry_of_model_calculations e T hf hF hUT
    (Selection.exists_graph_or_field_of_exact_rank hf hF
      (Matrix.PSL3Even.OuterElementaryRank.FixedRanks.graphField_involution_fixed_rank_le
        (by omega) hF))
    (fixed_simple_perfect_of_isGraphOrField hf hF)
    (fixed_sup_unipotent_of_isGraphOrField hf hF)
    A hA hAT houter hrank
end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.NonbinaryGeometry

namespace CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.NonbinaryGeometry
open Subgroup Theory.GroupTheory Matrix.PSL3.LinearThree
open Matrix.PSL3Even.NonbinaryCentralizer
open scoped MatrixGroups
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

/-- Actual graph conjugacy proves the structure of the literal relative centralizer. -/
theorem innerCentralizer_simple_perfect_of_graph
    (e : generalizedFitting G ≃* PSL(3,F)) (z : G) (hF : 4 ≤ Nat.card F)
    (hz : IsConj (modelAction e z) (Matrix.PSL3.OuterSolvable.graph F)) :
    IsSimpleGroup ((generalizedFitting G).subgroupOf (centralizer ({z} : Set G))) ∧
      Group.IsPerfect ((generalizedFitting G).subgroupOf (centralizer ({z} : Set G))) := by
  obtain ⟨hs, hp⟩ := graph_fixed_simple_perfect_of_isConj hF (modelAction e z) hz
  let := hs
  let := hp
  let ef := innerCentralizerEquivFixed e z
  exact ⟨ef.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := ef.symm.toMonoidHom) ef.symm.surjective⟩

omit [Finite F] in
/-- Generation for the graph representative which preserves the standard Borel. -/
theorem socle_le_centralizer_sup_of_oppositionGraph
    (e : generalizedFitting G ≃* PSL(3,F)) (T : Subgroup G) (z : G)
    (hUT : (unipotent F).map (linearThreeEmbedding _ e) ≤ T)
    (hz : modelAction e z = Matrix.PSL3.OuterSolvable.OddPrimeCoverage.oppositionGraph F) :
    generalizedFitting G ≤ centralizer ({z} : Set G) ⊔ T :=
  socle_le_centralizer_sup_of_fixed_generation e T z hUT
    (by rw [hz]; exact oppositionGraph_fixed_sup_unipotent)
end CFSG.Quasithin.ChapterE.ValuesEvenClassical.RankTwoUpper.LinearThree.OuterFamilies.NonbinaryGeometry
