module
public import CFSG.Quasithin.ChapterG.Section11.FiveConstituent
public import CFSG.Quasithin.ChapterG.Section11.PerfectConstituent
/-!
# Natural constituent rows in the low-rank G.11 reduction

The faithful self-dual action of the normal component orbit excludes every
full-linear constituent quotient. Perfectness and irreducibility exclude the
two-factor G.6.4 row. Together with the preceding five-point recognition and
even-core exclusion, only the natural S₆, S₇ and S₈ quotient rows remain.

For each surviving row, the component orbit's actual image is Aₙ. The same
coordinates identify its action on the original whole module with two copies
of the natural Aₙ module. This does not yet recognize the ambient group G.
The final theorem applies these exclusions to the original source inputs,
retaining all marked, form and exchanged-constituent data.

Source: Aschbacher--Smith G.10.16(4), G.11.6--8, printed pp.363--368.
-/

@[expose] public section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11
private theorem surjective_of_linear_model {D U : Type*} [Group D] [AddCommGroup U] [Module (ZMod 2) U]
    (σ : Representation (ZMod 2) D U) (n : ℕ)
    (hm : Section06.HasModelOn σ ⊤ ⊤ (Section06.binaryLinearAction n)) :
    Function.Surjective σ.asGroupHom := by
  obtain ⟨e,c,stable,hc⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let f := (Submodule.topEquiv : (⊤ : Submodule (ZMod 2) U) ≃ₗ[ZMod 2] U).symm.trans c
  have hfd (g : D) (w : U) : f (σ g w) = d g (f w) :=
    hc ⟨g,mem_top _⟩ ⟨w,Submodule.mem_top⟩
  intro a
  let t := (f.symm.trans (LinearMap.GeneralLinearGroup.toLinearEquiv a)).trans f
  obtain ⟨g,hg⟩ := d.surjective t
  refine ⟨g,?_⟩
  apply Units.ext
  apply LinearMap.ext
  intro w
  apply f.injective
  change f (σ g w) = f (a.val w)
  rw [hfd,hg]
  change f (a.val (f.symm (f w))) = f (a.val w)
  rw [f.symm_apply_apply]

/-- A self-dual normal constituent with an abelian supplement cannot have a
full-linear HX action quotient in dimension at least three. -/
theorem not_linear_model_of_selfDual_constituent
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (H X : Subgroup G) [H.Normal] [IsMulCommutative X]
    (I : Submodule (ZMod 2) V) (hH : H ≤ subspaceStabilizer ρ I)
    (hX : X ≤ subspaceStabilizer ρ I)
    (hd : 3 ≤ finrank (ZMod 2) I)
    (hdual : Nonempty (Representation.Equiv
      (invariantSubspace ρ H I hH).toRepresentation
      (invariantSubspace ρ H I hH).toRepresentation.dual))
    (n : ℕ)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H X I hH hX)) ⊤ ⊤
      (Section06.binaryLinearAction n)) : False := by
  let P := H ⊔ X
  let σ := Section09.constituentAction ρ H X I hH hX
  let J := H.subgroupOf P
  let Y := X.subgroupOf P
  obtain ⟨e⟩ := hdual
  have he : Representation.Equiv (σ.comp J.subtype)
      (Representation.dual (σ.comp J.subtype)) :=
    .mk e.toLinearEquiv (fun g => e.isIntertwining' ⟨g.val.val,g.property⟩)
  apply Representation.binary_not_surjective_of_selfDual_normal_restriction σ J Y
    (Subgroup.codisjoint_subgroupOf_sup H X).eq_top hd he
  intro a
  obtain ⟨g,hg⟩ := surjective_of_linear_model (kerRepresentation σ) n hm a
  obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective σ.ker g
  exact ⟨p,hg⟩

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

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- A natural symmetric constituent quotient identifies the original normal
component orbit and its full double action in the same coordinates. -/
theorem proper_marked_natural_quotient_double
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hv : v ∈ I) (hp : I ≠ ⊤)
    (n : ℕ) (hnat : 5 ≤ n)
    (hmodel :
      let H := componentOrbit L ⊤
      letI := componentOrbit_top_normal L
      let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
      let σ := Section09.constituentAction ρ H X I hI.choose hXI
      Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤
        (BinaryPermutation.naturalRepresentation (Fin n))) :
    Section09.Quasiequivalent (ρ.comp (componentOrbit L ⊤).subtype)
      ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
        (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hL.componentOrbit_top_ne_bot
  let R := invariantSubspace ρ H I hI.choose
  let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
  have hdata := marked_constituent_alternative h cover hw hS hn hL hm hI hv
  obtain ⟨e,c,hc⟩ := constituent_natural_restriction ρ H X I hI.choose hXI
    hdata.2.1 n hnat hmodel
  obtain ⟨_,_,⟨d⟩,_⟩ := hdata.2.2.2.resolve_left (fun he => hp he.1)
  let f := d.toLinearEquiv.trans (c.prodCongr c)
  refine ⟨e,f,?_⟩
  intro k w
  have hh := LinearMap.congr_fun (d.isIntertwining' k) w
  change d (ρ k w) = (R.toRepresentation k (d w).1,R.toRepresentation k (d w).2) at hh
  change (c (d (ρ k w)).1,c (d (ρ k w)).2) = _
  rw [hh,hc,hc]
  rfl

/-- Only the natural symmetric-six, -seven and -eight rows remain on the
proper marked constituent after the full-linear and two-factor exclusions. -/
theorem proper_marked_constituent_natural_models
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
        ∃ n, 6 ≤ n ∧ n ≤ 8 ∧ Section06.HasModelOn (kerRepresentation σ) ⊤ ⊤
          (BinaryPermutation.naturalRepresentation (Fin n)) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let hXI := h.stabilizes_constituent_of_point_mem (h.irreducible_of_not_solvable hn) H hI hv
  let σ := Section09.constituentAction ρ H X I hI.choose hXI
  rcases proper_marked_constituent_remaining_models h cover hw hS hn hL hm hI hv hp
      with hc | ⟨a,ha,hav,har,hra,hc,hmodels⟩
  · exact Or.inl hc
  · refine Or.inr ⟨a,ha,hav,har,hra,hc,?_⟩
    change RemainingRankOneModels (kerRepresentation σ) _ at hmodels
    rcases hmodels with ⟨n,_,_,hmodel⟩ | hother
    · have hd := hI.finrank_gt_two ρ H
      have hdual := (marked_constituent_alternative h cover hw hS hn hL hm hI hv).2.2.1
      exact (not_linear_model_of_selfDual_constituent ρ H X I hI.choose hXI (by omega) hdual n hmodel).elim
    · rcases hother with hnat | ht
      · exact hnat
      · obtain ⟨d⟩ := ht
        let r := (QuotientGroup.mk' σ.ker).comp
          (Subgroup.inclusion (show H ≤ H ⊔ X from le_sup_left))
        have hi : IsIrreducible ((kerRepresentation σ).comp r) :=
          hI.irreducible_of_normal_restriction ρ (h.irreducible_of_not_solvable hn) H
        exact (not_twoFactors_of_perfect_irreducible (kerRepresentation σ)
          (kerRepresentation_faithful σ) r hi _ d).elim
/-- The remaining proper marked branch has the actual doubled alternating
natural action, of degree eight or twelve, on its original component orbit. -/
theorem proper_marked_constituent_natural_actions
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X)
    (hn : ¬ Group.IsSolvable G) {L : Subgroup G} (hL : IsComponent G L)
    (hm : ⁅L,X⁆ ≠ ⊥) {I : Submodule (ZMod 2) V}
    (hI : IsIrrPlus ρ (componentOrbit L ⊤) I) (hv : v ∈ I) (hp : I ≠ ⊤) :
    Conclusion ρ B X ∨
      ∃ n, 6 ≤ n ∧ n ≤ 8 ∧
        Section09.Quasiequivalent (ρ.comp (componentOrbit L ⊤).subtype)
          ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
            (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) ∧
        ((n = 6 ∧ finrank (ZMod 2) V = 8) ∨
          ((n = 7 ∨ n = 8) ∧ finrank (ZMod 2) V = 12)) := by
  rcases proper_marked_constituent_natural_models h cover hw hS hn hL hm hI hv hp
      with hc | ⟨a,ha,hav,har,hra,hc,n,hn6,hn8,hmodel⟩
  · exact Or.inl hc
  · have he := proper_marked_natural_quotient_double h cover hw hS hn hL hm hI hv hp
      n (by omega) hmodel
    refine Or.inr ⟨n,hn6,hn8,he,?_⟩
    obtain ⟨e,f,hf⟩ := he
    have hd := f.finrank_eq
    have hn : n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn with rfl | rfl | rfl
    · exact Or.inl ⟨rfl,by simpa only [Module.finrank_prod,
        BinaryPermutation.finrank_natural_even (Fin 6) (by decide),Fintype.card_fin] using hd⟩
    · exact Or.inr ⟨Or.inl rfl,by simpa only [Module.finrank_prod,
        BinaryPermutation.finrank_natural_odd (Fin 7) (by decide),Fintype.card_fin] using hd⟩
    · exact Or.inr ⟨Or.inr rfl,by simpa only [Module.finrank_prod,
        BinaryPermutation.finrank_natural_even (Fin 8) (by decide),Fintype.card_fin] using hd⟩

/-- The unrecognized component branches after applying G.6.4 and eliminating
its full-linear, even-core and two-factor rows on the proper marked constituent.
The original selected subspace, form data and actor are retained. -/
def NaturalComponentReduction (ρ : Representation (ZMod 2) G V)
    (B : LinearMap.BilinForm (ZMod 2) V) (v : V) (W : Submodule (ZMod 2) V)
    (X : Subgroup G) [IsElementaryAbelian 2 X] : Prop :=
    ∃ L : Subgroup G, IsComponent G L ∧ ⁅L,X⁆ ≠ ⊥ ∧
      Section10.ComponentOrthogonalData ρ B L ∧
      ∃ I : Submodule (ZMod 2) V, ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I,
        (v ∈ I ∧ MarkedConstituentAlternative ρ B v X L I hI.isIrrPlus ∧
          (I = ⊤ ∨ ∃ n, 6 ≤ n ∧ n ≤ 8 ∧
            Section09.Quasiequivalent (ρ.comp (componentOrbit L ⊤).subtype)
              ((BinaryPermutation.alternatingNaturalRepresentation (Fin n)).prod
                (BinaryPermutation.alternatingNaturalRepresentation (Fin n))) ∧
            ((n = 6 ∧ finrank (ZMod 2) V = 8) ∨
              ((n = 7 ∨ n = 8) ∧ finrank (ZMod 2) V = 12)))) ∨
          (v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I)

/-- Apply the proper-constituent recognition to the original G.11.1(3ii)
inputs. Final G.11.2 recognition is still required in the solvable degree-six,
whole marked, exchanged, and doubled A₆/A₇/A₈ branches. -/
theorem conclusion_or_natural_component_reduction
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hw : LowRankWitness ρ v X) (hS : NormalSylow ρ v X) :
    Conclusion ρ B X ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧
        ((Group.IsSolvable G ∧ finrank (ZMod 2) (Additive X) = 2 ∧
            finrank (ZMod 2) V = 6) ∨
          (¬ Group.IsSolvable G ∧ NaturalComponentReduction ρ B v W X))) := by
  rcases conclusion_or_component_reduction h cover hw hS with hc | ⟨hi,hd,hs | ⟨hn,hh⟩⟩
  · exact Or.inl hc
  · exact Or.inr ⟨hi,hd,Or.inl hs⟩
  · obtain ⟨L,hL,hm,horth,I,hI,hmarked | hexchanged⟩ := hh
    · obtain ⟨hv,hdata⟩ := hmarked
      by_cases hp : I = ⊤
      · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,Or.inl ⟨hv,hdata,Or.inl hp⟩⟩⟩
      · rcases proper_marked_constituent_natural_actions h cover hw hS hn hL hm
          hI.isIrrPlus hv hp with hc | hnat
        · exact Or.inl hc
        · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,Or.inl ⟨hv,hdata,Or.inr hnat⟩⟩⟩
    · exact Or.inr ⟨hi,hd,Or.inr ⟨hn,L,hL,hm,horth,I,hI,Or.inr hexchanged⟩⟩

end CFSG.Quasithin.ChapterG.Section11
