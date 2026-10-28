module
public import CFSG.Quasithin.ChapterG.Section11.OrthogonalDouble
public import CFSG.Quasithin.ChapterG.Section11.Transvection
public import Theory.GroupTheory.PerfectSymmetricNormal
public import Theory.Representation.IrreducibleFixedPoints

/-!
# The five-point row of the actual constituent-kernel quotient

The component orbit embeds in the literal HX-action quotient because its
constituent action is faithful. In the natural S₅ row its image is a
nontrivial perfect normal subgroup, hence precisely A₅. The same linear
coordinates then identify the constituent with the orthogonal A₅ module.
The double-module reconstruction identifies the original whole action.

The final reduction applies G.6.4 and removes this row without assuming a
classification callback. The even augmentation-core rows are excluded by
their fixed constant vector, and degree two is excluded by the constituent
dimension bound. The surviving models and original marked witness
remain explicit; exhaustive G.11.2 assembly is still open.
Source: Aschbacher--Smith G.10.16(4), G.11.7--8, printed pp.363--368.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11

private theorem not_even_core_constituent
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G)
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hi : IsIrreducible (invariantSubspace ρ H I hH).toRepresentation)
    (hd : 2 ≤ finrank (ZMod 2) I)
    (n : ℕ) (hn : 0 < n) (he : Even n)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H X I hH hX)) ⊤ ⊤
      (BinaryPermutation.coreRepresentation (Fin n))) : False := by
  let R := (invariantSubspace ρ H I hH).toRepresentation
  let := hi
  let σ := Section09.constituentAction ρ H X I hH hX
  let q := QuotientGroup.mk' σ.ker
  let ι := Subgroup.inclusion (show H ≤ H ⊔ X from le_sup_left)
  let r := q.comp ι
  obtain ⟨e,c,stable,hc⟩ := hm
  have hOne : BinaryPermutation.allOne (Fin n) ∈ BinaryPermutation.core (Fin n) := by
    change BinaryPermutation.augmentation (Fin n) (BinaryPermutation.allOne (Fin n)) = 0
    rw [BinaryPermutation.augmentation_allOne,Fintype.card_fin]
    obtain ⟨k,hk⟩ := he
    rw [hk,Nat.cast_add]
    rw [← two_mul,show (2 : ZMod 2) = 0 by decide,zero_mul]
  let u : BinaryPermutation.core (Fin n) := ⟨BinaryPermutation.allOne (Fin n),hOne⟩
  have hu : u ≠ 0 := by
    intro hz
    have hh := congrArg (fun w : BinaryPermutation.core (Fin n) => w.val ⟨0,hn⟩) hz
    exact (by decide : (1 : ZMod 2) ≠ 0) hh
  let w : I := (c.symm u).val
  have hw (g : H) : R g w = w := by
    have hh := hc ⟨r g,mem_top _⟩ (c.symm u)
    rw [c.apply_symm_apply] at hh
    have huFix (s : Equiv.Perm (Fin n)) : BinaryPermutation.coreRepresentation (Fin n) s u = u := by
      apply Subtype.ext
      exact BinaryPermutation.permute_allOne (Fin n) s
    rw [huFix] at hh
    have hh' := c.injective (hh.trans (c.apply_symm_apply u).symm)
    exact congrArg Subtype.val hh'
  have hw0 : w = 0 := by
    have hmem : w ∈ Representation.OneCohomology.fixed R := hw
    rw [Representation.OneCohomology.fixed_eq_bot_of_irreducible_finrank R hd] at hmem
    exact hmem
  apply hu
  have hw' : c.symm u = 0 := Subtype.ext hw0
  have hh := congrArg c hw'
  simpa only [c.apply_symm_apply,map_zero] using hh

private theorem constituent_five_restriction
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G) [H.Normal]
    [Group.IsPerfect H] [Nontrivial H]
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hf : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H X I hH hX)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 5))) :
    Section09.Quasiequivalent (invariantSubspace ρ H I hH).toRepresentation
      (BinaryPermutation.alternatingCoreRepresentation (Fin 5)) := by
  let P := H ⊔ X
  let σ := Section09.constituentAction ρ H X I hH hX
  let q := QuotientGroup.mk' σ.ker
  let ι := Subgroup.inclusion (show H ≤ P from le_sup_left)
  let r := q.comp ι
  have hr : Function.Injective r := by
    intro a b hab
    apply hf
    exact congrArg (kerRepresentation σ) hab
  have hrange : r.range = (H.subgroupOf P).map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨a,rfl⟩
      exact a.property
    · intro hx
      exact ⟨⟨x,hx⟩,rfl⟩
  let : r.range.Normal := hrange ▸ Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  obtain ⟨e,c,stable,hc⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let f := (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) I) ≃ₗ[ZMod 2] I).symm.trans c
  have hfd (g : P ⧸ σ.ker) (w : I) : f (kerRepresentation σ g w) =
      BinaryPermutation.naturalRepresentation (Fin 5) (d g) (f w) := by
    exact hc ⟨g,mem_top _⟩ ⟨w,Submodule.mem_top⟩
  let j := d.toMonoidHom.comp r
  have hj : Function.Injective j := d.injective.comp hr
  have hjrange : j.range = r.range.map d.toMonoidHom := MonoidHom.range_comp _ _
  let : j.range.Normal := hjrange ▸ Subgroup.Normal.map inferInstance d.toMonoidHom d.surjective
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  let : Nontrivial j.range := (MonoidHom.ofInjective hj).injective.nontrivial
  have hA : j.range = alternatingGroup (Fin 5) :=
    Equiv.Perm.eq_alternatingGroup_of_perfect_normal (by simp) j.range
  let eH := (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hA)
  let E := RankTwo.TensorModels.Orthogonal.naturalEquiv
  let t := f.trans E.symm.toLinearEquiv
  refine ⟨eH,t,?_⟩
  intro g w
  have he : (eH g).val = j g := rfl
  apply E.toLinearEquiv.injective
  change E (E.symm (f ((invariantSubspace ρ H I hH).toRepresentation g w))) = _
  rw [E.apply_symm_apply]
  have hE := LinearMap.congr_fun (E.isIntertwining' (j g)) (t w)
  change E (RankTwo.TensorModels.Orthogonal.representation (j g) (t w)) =
    BinaryPermutation.naturalRepresentation (Fin 5) (j g) (E (t w)) at hE
  change f ((invariantSubspace ρ H I hH).toRepresentation g w) =
    E (RankTwo.TensorModels.Orthogonal.representation (eH g).val (t w))
  rw [he,hE]
  change f (kerRepresentation σ (r g) w) =
    BinaryPermutation.naturalRepresentation (Fin 5) (j g) (E (E.symm (f w)))
  rw [E.apply_symm_apply]
  exact hfd (r g) w

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- The natural symmetric-five row of the actual G.6.4 quotient reconstructs
G.11.2(9) for the original group and action. The component image is proved to
be A₅; it is not an extra recognition hypothesis. -/
theorem proper_marked_five_quotient_conclusion
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hv : v ∈ I) (hp : I ≠ ⊤)
    (hfive :
      let H := componentOrbit L ⊤
      letI := componentOrbit_top_normal L
      let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
      let σ := Section09.constituentAction ρ H X I hI.choose hXI
      Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤
        (BinaryPermutation.naturalRepresentation (Fin 5))) :
    Conclusion ρ B X := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hL.componentOrbit_top_ne_bot
  let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
  have hdata := marked_constituent_alternative h cover hw hS hn hL hm hI hv
  exact proper_marked_orthogonal_conclusion h cover hw hS hn hL hm hI hv hp
    (constituent_five_restriction ρ H X I hI.choose hXI hdata.2.1 hfive)

/-- The remaining literal G.6.4 models after reconstructing the five-point
row. The two-factor alternative retains all its extension and action data. -/
def RemainingRankOneModels {D U : Type*} [Group D] [AddCommGroup U]
    [Module (ZMod 2) U] (σ : Representation (ZMod 2) D U) (a : D) : Prop :=
  (∃ n, 3 ≤ n ∧ n ≤ 5 ∧ Section06.HasModelOn σ ⊤ ⊤ (Section06.binaryLinearAction n)) ∨
  (∃ n, 6 ≤ n ∧ n ≤ 8 ∧
    Section06.HasModelOn σ ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin n))) ∨
  Nonempty (Section06.TwoFactors σ a)

/-- Apply G.6.4 to the proper marked constituent and close its symmetric-five
row in the original group. The surviving rows retain the complete G.6.4
conclusion, its original witness, and the same action-kernel quotient. -/
theorem proper_marked_constituent_remaining_models
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hv : v ∈ I) (hp : I ≠ ⊤) :
    Conclusion ρ B X ∨
      let H := componentOrbit L ⊤
      letI := componentOrbit_top_normal L
      let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
      let σ := Section09.constituentAction ρ H X I hI.choose hXI
      ∃ a : X, orderOf (a : G) = 2 ∧ v ∈ RankTwo.movedSpace ρ a ∧
        finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2 ∧
        let aP : (H ⊔ X : Subgroup G) := ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩
        finrank (ZMod 2) (LinearMap.range (σ aP - LinearMap.id)) = 1 ∧
        Section06.Conclusion (kerRepresentation σ) (QuotientGroup.mk' σ.ker aP) ∧
        RemainingRankOneModels (kerRepresentation σ) (QuotientGroup.mk' σ.ker aP) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
  let σ := Section09.constituentAction ρ H X I hI.choose hXI
  obtain ⟨a,ha,hav,har,hra,hc⟩ :=
    proper_marked_constituent_rankOne_classification h cover hw hS hn hL hm hI hv hp
  by_cases hfive : Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 5))
  · exact Or.inl (proper_marked_five_quotient_conclusion h cover hw hS
      hn hL hm hI hv hp hfive)
  · refine Or.inr ⟨a,ha,hav,har,hra,hc,?_⟩
    rcases hc.1 with ⟨_,hmodels,ht⟩ | ht
    · rw [ht] at hmodels
      rcases hmodels with hl | ⟨n,hnat,hne,hmodel⟩ | ho
      · obtain ⟨n,_,hnu,e,c,stable,hmodel⟩ := hl
        have hd := c.finrank_eq
        rw [finrank_top,Module.finrank_fin_fun] at hd
        have hgt := hI.finrank_gt_two ρ H
        exact Or.inl ⟨n,by omega,hnu,e,c,stable,hmodel⟩
      · have hn5 : n ≠ 5 := by
          rintro rfl
          exact hfive hmodel
        exact Or.inr (Or.inl ⟨n,by omega,hne,hmodel⟩)
      · obtain ⟨n,hnat,hmodel⟩ := ho
        have hi := hI.irreducible_of_normal_restriction ρ
          (h.irreducible_of_not_solvable hn) H
        have hgt := hI.finrank_gt_two ρ H
        exact (not_even_core_constituent ρ H X I hI.choose hXI hi (by omega) n
          (by rcases hnat with rfl | rfl <;> decide)
          (by rcases hnat with rfl | rfl <;> decide) hmodel).elim
    · exact Or.inr (Or.inr ht)

end CFSG.Quasithin.ChapterG.Section11
