module
public import CFSG.Quasithin.ChapterG.Section11.ExchangedLowRank
public import CFSG.Quasithin.ChapterG.Section11.Transvection
public import CFSG.Quasithin.ChapterG.Section11.PerfectConstituent
public import Theory.Representation.IrreducibleFixedPoints

/-!
# Rank-one models on the actual exchanged constituent

The original low-rank witness lies in the literal stabilizer
`X ∩ N_G(I)` and acts as a transvection on I. Restricting to the group
it generates with the component orbit and quotienting by that action's
kernel gives a faithful irreducible action covered by an actual subgroup
of the supplied SQTK cover. This discharges every input to G.6.4.

Perfect irreducibility excludes its two-factor row; fixed constant vectors
exclude the even augmentation-core rows. The quotient action is therefore
GL_n(2), n = 3,4,5, or natural S_n, n = 5,6,7,8, with the complete group
and module coordinates. The exchanged pair fills V, so dim(V) is at most
12. These are constituent-quotient models; recognizing or excluding the
original whole action remains a separate step in G.11.2.

Source: Aschbacher--Smith G.6.4, G.10.16(4), and G.11.6,
printed pp.345--346,363--366. Applied to the original reduction in
`ExchangedModelReduction` and to the strict quotient in `StrictExchangedModels`.
-/

public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

private theorem rankOne_classification (ρ : Representation (ZMod 2) G V)
    [IsIrreducible ρ] (hf : Function.Injective ρ)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (a : G) (ha : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (LinearMap.range (ρ a - LinearMap.id)) = 1) :
    Section06.Conclusion ρ a := by
  obtain ⟨c⟩ := cover
  have hne : a ≠ 1 := by
    intro he
    rw [he,map_one,Module.End.one_eq_id,sub_self,LinearMap.range_zero,finrank_bot] at hr
    omega
  have hcore : pCore 2 G = ⊥ := by
    exact le_bot_iff.mp ((normal_p_subgroup_le_ker ρ (pCore 2 G) pCore_isPGroup).trans
      ((MonoidHom.ker_eq_bot_iff ρ).mpr hf).le)
  have hN : normalClosure ({a} : Set G) ≠ ⊥ := by
    intro he
    have haN := subset_normalClosure (Set.mem_singleton a)
    exact hne (mem_bot.mp (he ▸ haN))
  have hgen : conjugateDisplacementSpan ρ a ⊤ = ⊤ := by
    rw [← commutator_conjugateSpanBy_zpowers,conjugateSpanBy_zpowers_top]
    exact subspaceCommutator_top_eq_top_of_normal_faithful_irreducible ρ hf inferInstance _ hN
  have hs : Section06.Hypotheses KnownSimple.IsKnownSimple ρ a c.projection := {
    finite_group := inferInstance
    finite_cover := inferInstance
    finite_displacement := inferInstance
    cover_sqtk := c.sqtk
    quotient_surjective := c.surjective
    twoCore := hcore
    faithful := hf
    involution := ha
    nonidentity := hne
    displacement_rank := by omega
    generated := hgen }
  exact Section06.lemma_G_6_4 hs hr

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem constituentAction_irreducible
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G)
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hi : IsIrreducible (invariantSubspace ρ H I hH).toRepresentation) :
    IsIrreducible (Section09.constituentAction ρ H X I hH hX) := by
  let P := H ⊔ X
  let e := subgroupOfEquivOfLe (show H ≤ P from le_sup_left)
  have he : (Section09.constituentAction ρ H X I hH hX).comp (H.subgroupOf P).subtype =
      (invariantSubspace ρ H I hH).toRepresentation.comp e.toMonoidHom := rfl
  apply irreducible_of_subgroup_restriction _ (H.subgroupOf P)
  rw [he]
  exact (irreducible_comp_surjective_iff e.toMonoidHom e.surjective _).mpr hi

omit [Finite G] [FiniteDimensional (ZMod 2) V] in
private theorem constituentAction_rank
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G)
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I) (a : X) :
    let σ := Section09.constituentAction ρ H X I hH hX
    let aP : (H ⊔ X : Subgroup G) := ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩
    finrank (ZMod 2) (LinearMap.range (σ aP - LinearMap.id)) =
      finrank (ZMod 2) (I.map (ρ a - LinearMap.id)) := by
  dsimp only
  have heq : (LinearMap.range
      (Section09.constituentAction ρ H X I hH hX
        ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩ - LinearMap.id)).map I.subtype =
      I.map (ρ a - LinearMap.id) := by
    rw [← LinearMap.range_comp]
    have he : I.subtype.comp
        (Section09.constituentAction ρ H X I hH hX
          ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩ - LinearMap.id) =
        (ρ a - LinearMap.id).comp I.subtype := by
      ext u
      rfl
    rw [he,LinearMap.range_comp,Submodule.range_subtype]
  have he := Submodule.finrank_map_subtype_eq I (LinearMap.range
    (Section09.constituentAction ρ H X I hH hX
      ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩ - LinearMap.id))
  rw [heq] at he
  exact he.symm

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


/-- The exact rank-one classifier on the exchanged constituent, using the
literal stabilizer intersection and its action kernel. -/
theorem exchanged_constituent_rankOne_classification
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v W X I) :
    let H := componentOrbit L ⊤
    let Y := X ⊓ subspaceStabilizer ρ I
    let σ := Section09.constituentAction ρ H Y I hI.invariant inf_le_right
    ∃ x : X, I.map (ρ x) ≠ I ∧ IsCompl I (I.map (ρ x)) ∧
      finrank (ZMod 2) V = 2 * finrank (ZMod 2) I ∧
      ∃ a : Y, orderOf (a : G) = 2 ∧ v ∈ RankTwo.movedSpace ρ a ∧
        finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2 ∧
        let aP : (H ⊔ Y : Subgroup G) := ⟨a,(le_sup_right : Y ≤ H ⊔ Y) a.property⟩
        finrank (ZMod 2) (LinearMap.range (σ aP - LinearMap.id)) = 1 ∧
        Section06.Conclusion (kerRepresentation σ) (QuotientGroup.mk' σ.ker aP) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let Y := X ⊓ subspaceStabilizer ρ I
  let σ := Section09.constituentAction ρ H Y I hI.invariant inf_le_right
  obtain ⟨x,hx,hcompl,hd,a,ha,hav,har,hstable,hra,_⟩ :=
    exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
  let b : Y := ⟨a,a.property,(subspace_map_eq_iff ρ I a).mp hstable⟩
  let bP : (H ⊔ Y : Subgroup G) := ⟨b,(le_sup_right : Y ≤ H ⊔ Y) b.property⟩
  have hrσ : finrank (ZMod 2) (LinearMap.range (σ bP - LinearMap.id)) = 1 :=
    (constituentAction_rank ρ H Y I hI.invariant inf_le_right b).trans hra
  refine ⟨x,hx,hcompl,hd,b,ha,hav,har,hrσ,?_⟩
  have hR := hI.isIrrPlus.irreducible_of_normal_restriction ρ
    (h.irreducible_of_not_solvable hn) H
  let : IsIrreducible σ := constituentAction_irreducible ρ H Y I hI.invariant inf_le_right hR
  apply rankOne_classification (kerRepresentation σ) (kerRepresentation_faithful σ)
    (cover.map (fun c => (c.subgroup (H ⊔ Y)).map (QuotientGroup.mk' σ.ker)
      (QuotientGroup.mk'_surjective σ.ker))) (QuotientGroup.mk' σ.ker bP)
  · rw [← map_pow]
    have hb2 : bP ^ 2 = 1 := by
      apply Subtype.ext
      change (a : G) ^ 2 = 1
      rw [← ha]
      exact pow_orderOf_eq_one (a : G)
    rw [hb2,map_one]
  · exact hrσ

/-- The surviving G.6.4 rows for the actual exchanged action quotient.
This is a conclusion predicate; its witnesses are constructed below. -/
@[expose] def ExchangedRankOneModels
    (ρ : Representation (ZMod 2) G V) (X L : Subgroup G)
    (I : Submodule (ZMod 2) V)
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I) : Prop :=
  let Y := X ⊓ subspaceStabilizer ρ I
  let σ := kerRepresentation
    (Section09.constituentAction ρ (componentOrbit L ⊤) Y I hI.invariant inf_le_right)
  (∃ n, 3 ≤ n ∧ n ≤ 5 ∧ Section06.HasModelOn σ ⊤ ⊤ (Section06.binaryLinearAction n)) ∨
  (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ Section06.HasModelOn σ ⊤ ⊤
    (BinaryPermutation.naturalRepresentation (Fin n)))

/-- Perfect irreducibility removes the two-factor row, and the fixed constant
vector removes the even augmentation-core rows. No self-duality is assumed. -/
theorem exchanged_constituent_models
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v W X I) :
    ExchangedRankOneModels ρ X L I hI := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let Y := X ⊓ subspaceStabilizer ρ I
  let σ := Section09.constituentAction ρ H Y I hI.invariant inf_le_right
  obtain ⟨x,hx,hcompl,hd,a,ha,hav,har,hra,hc⟩ :=
    exchanged_constituent_rankOne_classification h cover hw hS hn hL hm hI hgeo
  have hi := hI.isIrrPlus.irreducible_of_normal_restriction ρ
    (h.irreducible_of_not_solvable hn) H
  have hgt := hI.isIrrPlus.finrank_gt_two ρ H
  rcases hc.1 with ⟨_,hmodels,ht⟩ | ht
  · rw [ht] at hmodels
    rcases hmodels with hl | hnat | ho
    · obtain ⟨n,_,hnu,e,c,stable,hmodel⟩ := hl
      have hd := c.finrank_eq
      rw [finrank_top,Module.finrank_fin_fun] at hd
      exact Or.inl ⟨n,by omega,hnu,e,c,stable,hmodel⟩
    · exact Or.inr hnat
    · obtain ⟨n,hnat,hmodel⟩ := ho
      exact (not_even_core_constituent ρ H Y I hI.invariant inf_le_right hi (by omega) n
        (by rcases hnat with rfl | rfl <;> decide)
        (by rcases hnat with rfl | rfl <;> decide) hmodel).elim
  · obtain ⟨d⟩ := ht
    let r := (QuotientGroup.mk' σ.ker).comp
      (Subgroup.inclusion (show H ≤ H ⊔ Y from le_sup_left))
    exact (not_twoFactors_of_perfect_irreducible (kerRepresentation σ)
      (kerRepresentation_faithful σ) r hi _ d).elim

/-- The exchanged branch has whole-module degree six, eight, ten or twelve.
The bound follows from actual model coordinates on its selected constituent. -/
theorem exchanged_degree_le_twelve
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v W X I) :
    finrank (ZMod 2) V = 2 * finrank (ZMod 2) I ∧ finrank (ZMod 2) I ≤ 6 := by
  obtain ⟨x,hx,hcompl,hd,_⟩ := exchanged_lowRank_pair h cover hw hS hn hL hm hI hgeo
  refine ⟨hd,?_⟩
  rcases exchanged_constituent_models h cover hw hS hn hL hm hI hgeo with
    ⟨n,_,hnu,e,c,stable,hmodel⟩ | ⟨n,hnl,hnu,e,c,stable,hmodel⟩
  · have he := c.finrank_eq
    rw [finrank_top,Module.finrank_fin_fun] at he
    omega
  · have he := c.finrank_eq
    rw [finrank_top] at he
    have hn : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl | rfl
    all_goals simp only [BinaryPermutation.finrank_natural_even (Fin 6) (by decide),
      BinaryPermutation.finrank_natural_even (Fin 8) (by decide),
      BinaryPermutation.finrank_natural_odd (Fin 5) (by decide),
      BinaryPermutation.finrank_natural_odd (Fin 7) (by decide),Fintype.card_fin] at he
    all_goals omega

end CFSG.Quasithin.ChapterG.Section11
