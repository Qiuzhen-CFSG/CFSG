module
public import CFSG.Quasithin.ChapterG.Section11.NaturalConstituent
public import Theory.Representation.IrreducibleFixedPoints

/-!
# Natural models for a self-dual normal constituent with a transvection

Apply G.6.4 to the faithful action quotient on the constituent. Its SQTK
cover is the preimage of the literal acting subgroup. Perfect irreducibility
excludes the two-factor rows, the fixed constant vector excludes even cores,
and self-duality excludes full-linear rows. The surviving natural symmetric
model identifies the original normal perfect subgroup with the alternating
group in the same coordinates.

Source: Aschbacher--Smith, G.6.4 and G.11.9(3), printed pp.345--346,369.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
universe u v
variable {G : Type u} [Group G] [Finite G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

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


private theorem constituent_natural_restriction
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G) [H.Normal]
    [Group.IsPerfect H] [Nontrivial H]
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hf : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
    (n : ℕ) (hn : 5 ≤ n)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H X I hH hX)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    Section09.Quasiequivalent (invariantSubspace ρ H I hH).toRepresentation
      (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) := by
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
      BinaryPermutation.naturalRepresentation (Fin n) (d g) (f w) := by
    exact hc ⟨g,mem_top _⟩ ⟨w,Submodule.mem_top⟩
  let j := d.toMonoidHom.comp r
  have hj : Function.Injective j := d.injective.comp hr
  have hjrange : j.range = r.range.map d.toMonoidHom := MonoidHom.range_comp _ _
  let : j.range.Normal := hjrange ▸ Subgroup.Normal.map inferInstance d.toMonoidHom d.surjective
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  let : Nontrivial j.range := (MonoidHom.ofInjective hj).injective.nontrivial
  have hA : j.range = alternatingGroup (Fin n) :=
    Equiv.Perm.eq_alternatingGroup_of_perfect_normal (by simpa using hn) j.range
  let eH := (MonoidHom.ofInjective hj).trans (MulEquiv.subgroupCongr hA)
  refine ⟨eH,f,?_⟩
  intro g w
  exact hfd (r g) w

/-- A rank-one involution on a faithful self-dual normal perfect constituent
recognizes its actual orbit action as a natural alternating module. -/
theorem normal_constituent_natural_model
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G)
    [H.Normal] [Group.IsPerfect H] [Nontrivial H] [IsMulCommutative X]
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hi : IsIrreducible (invariantSubspace ρ H I hH).toRepresentation)
    (hf : Function.Injective (invariantSubspace ρ H I hH).toRepresentation)
    (hd : 3 ≤ finrank (ZMod 2) I)
    (hdual : Nonempty (Representation.Equiv
      (invariantSubspace ρ H I hH).toRepresentation
      (invariantSubspace ρ H I hH).toRepresentation.dual))
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (a : X) (ha : (a : G) ^ 2 = 1)
    (hr : finrank (ZMod 2) (LinearMap.range ((ρ a - 1).comp I.subtype)) = 1) :
    let σ := Section09.constituentAction ρ H X I hH hX
    ∃ n, 5 ≤ n ∧ n ≤ 8 ∧
      Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤
        (BinaryPermutation.naturalRepresentation (Fin n)) ∧
      Section09.Quasiequivalent (invariantSubspace ρ H I hH).toRepresentation
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n)) := by
  let σ := Section09.constituentAction ρ H X I hH hX
  let aP : (H ⊔ X : Subgroup G) := ⟨a,(le_sup_right : X ≤ H ⊔ X) a.property⟩
  let : IsIrreducible σ := constituentAction_irreducible ρ H X I hH hX hi
  have hrσ : finrank (ZMod 2) (LinearMap.range (σ aP - LinearMap.id)) = 1 := by
    have he := constituentAction_rank ρ H X I hH hX a
    have hr' := hr
    change finrank (ZMod 2) (LinearMap.range ((ρ a - LinearMap.id).comp I.subtype)) = 1 at hr'
    rw [LinearMap.range_comp,Submodule.range_subtype] at hr'
    exact he.trans hr'
  have hc : Section06.Conclusion (kerRepresentation σ) (QuotientGroup.mk' σ.ker aP) := by
    apply rankOne_classification (kerRepresentation σ) (kerRepresentation_faithful σ)
      (cover.map (fun c => (c.subgroup (H ⊔ X)).map (QuotientGroup.mk' σ.ker)
        (QuotientGroup.mk'_surjective σ.ker)))
    · rw [← map_pow,show aP ^ 2 = 1 from Subtype.ext ha,map_one]
    · exact hrσ
  let r := (QuotientGroup.mk' σ.ker).comp
    (Subgroup.inclusion (show H ≤ H ⊔ X from le_sup_left))
  have hir : IsIrreducible ((kerRepresentation σ).comp r) := hi
  rcases hc.1 with ⟨_,hm,ht⟩ | ht
  · rw [ht] at hm
    rcases hm with ⟨n,_,_,hm⟩ | ⟨n,hn5,hn8,hm⟩ | ⟨n,hn,hm⟩
    · exact (not_linear_model_of_selfDual_constituent ρ H X I hH hX hd hdual n hm).elim
    · exact ⟨n,hn5,hn8,hm,constituent_natural_restriction ρ H X I hH hX hf n hn5 hm⟩
    · exact (not_even_core_constituent ρ H X I hH hX hi (by omega) n
        (by rcases hn with rfl | rfl <;> decide)
        (by rcases hn with rfl | rfl <;> decide) hm).elim
  · obtain ⟨d⟩ := ht
    exact (not_twoFactors_of_perfect_irreducible (kerRepresentation σ)
      (kerRepresentation_faithful σ) r hir _ d).elim

end CFSG.Quasithin.ChapterG.Section11
