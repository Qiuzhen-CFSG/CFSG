module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable.ComponentCatalogueLargeActorDegreesExchanged
public import Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.TreeWreathModel
public import Theory.SpecificGroups.AlternatingSix.ShadowLocal.ElementaryRank
public import CFSG.Quasithin.ChapterG.Section10.Components.ExchangedCompletion
public import Theory.GroupTheory.WreathTwoElementaryRank
public import Theory.Representation.BinaryNaturalDual.FiveActors.ModuleGeometry.Rank

/-!
# The remaining natural exchanged constituent for the original larger actor

The literal index-two constituent stabilizer embeds in its symmetric model.
The larger-actor bound excludes the S₅, S₇ and S₈ natural constituents, leaving
S₆ in constituent degree four, whole degree eight, and actor rank four.
If the component orbit acted faithfully on that constituent, the full actor
would embed in Aut(A₆), whose elementary two-rank is at most three. A central
kernel also vanishes: the actual perfect normal image is the centerless A₆,
and ambient irreducibility kills the center of the component orbit. Thus
only the noncentral kernel with more than one component remains.

The marked full-linear-four alternative also has actor rank exactly four.
Both refined remainders feed the literal larger-actor component consumer;
the whole-component recognition, noncentral-kernel exclusion and ambient
full-linear-four exclusion remain necessary to discharge the degree premise.
The successful degree-six branch retains the full dotted-group G₂(2) equivalence.

Source: Aschbacher--Smith G.10.9--15, G.11.6--7 and 14.3.13--14, printed
pp.360--367,993--994. The exceptional full-four correction in
`docs/quasithin-proof-basis.md` is retained.
-/

public noncomputable section
open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11

private theorem symmetric_eight_two_rank : primeRank 2 (Equiv.Perm (Fin 8)) ≤ 4 := by
  let S := Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeSylow
  rw [S.primeRank_eq]
  change primeRank 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeGroup ≤ 4
  rw [primeRank_equiv 2 Theory.SpecificGroups.SymmetricEight.A6ShadowTwoLocals.treeWreathEquiv]
  apply WreathTwoElementaryRank.rank_bound (r := 2) _ (by decide)
  apply primeRank_le_of_noncommutative_card_prime_pow (n := 2)
  · norm_num [DihedralGroup.nat_card, DihedralGroup.card]
  · exact DihedralGroup.not_commutative (by decide) (by decide)

private theorem elementary_card (A : Type*) [Group A] [Finite A]
    [IsElementaryAbelian 2 A] : Nat.card A = 2 ^ finrank (ZMod 2) (Additive A) := by
  rw [Nat.card_congr Additive.ofMul]
  simpa only [Nat.card_zmod] using Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive A)

/-- The index-two stabilizer embeds in the literal natural symmetric model. -/
private theorem natural_stabilizer_embedding
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
    {v : U} {W I : Submodule (ZMod 2) U} {X H : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : Section10.Hypothesis ρ B v W X X₀)
    (hH : H ≤ subspaceStabilizer ρ I)
    (hgen : Homogeneous.orbitSpan ρ X I = ⊤) (n : ℕ)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H
        (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    ∃ j : (subspaceStabilizer ρ I).subgroupOf X →* Equiv.Perm (Fin n),
      Function.Injective j := by
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  let P := H ⊔ (X ⊓ subspaceStabilizer ρ I)
  let σ := Section09.constituentAction ρ H (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right
  obtain ⟨e,c,stable,hc⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let i : Y →* P := {
    toFun := fun y => ⟨y.val.val, (show X ⊓ subspaceStabilizer ρ I ≤ P from le_sup_right) ⟨y.val.property,y.property⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  let j := d.toMonoidHom.comp ((QuotientGroup.mk' σ.ker).comp i)
  refine ⟨j, (injective_iff_map_eq_one j).mpr ?_⟩
  intro y hy
  have hq : QuotientGroup.mk' σ.ker (i y) = 1 := by
    apply d.injective
    change d (QuotientGroup.mk' σ.ker (i y)) = 1 at hy
    simpa only [map_one] using hy
  have hk : σ (i y) = 1 := (QuotientGroup.eq_one_iff _).mp hq
  apply Subtype.ext
  apply Subtype.ext
  exact h.eq_one_of_fixes_spanning_constituent hgen y.val.property (fun u hu =>
    congrArg (fun a : Module.End (ZMod 2) I => (a ⟨u,hu⟩ : U)) hk)

/-- Adding the exchanged orbit contributes exactly one to the actor rank. -/
private theorem exchanged_natural_actor_bound
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    {ρ : Representation (ZMod 2) D U} {B : LinearMap.BilinForm (ZMod 2) U}
    {v : U} {W I : Submodule (ZMod 2) U} {X H : Subgroup D}
    [IsElementaryAbelian 2 X] {X₀ : Subgroup X}
    (h : Section10.Hypothesis ρ B v W X X₀)
    (hH : H ≤ subspaceStabilizer ρ I)
    (hgen : Homogeneous.orbitSpan ρ X I = ⊤)
    (hindex : (subspaceStabilizer ρ I).relIndex X = 2) (n r : ℕ)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H
        (X ⊓ subspaceStabilizer ρ I) I hH inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n)))
    (hr : primeRank 2 (Equiv.Perm (Fin n)) ≤ r) :
    finrank (ZMod 2) (Additive X) ≤ r + 1 := by
  let Y := (subspaceStabilizer ρ I).subgroupOf X
  let : IsElementaryAbelian 2 Y := IsElementaryAbelian.of_injective Y.subtype Y.subtype_injective
  obtain ⟨j,hj⟩ := natural_stabilizer_embedding h hH hgen n hm
  let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_injective (MonoidHom.ofInjective hj).symm.toMonoidHom
    (MonoidHom.ofInjective hj).symm.injective
  have hc := (primeRank_le_iff_elementary_card_le _).mp hr j.range inferInstance
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, elementary_card Y] at hc
  have hy := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hc
  have he := Y.card_mul_index
  change Y.index = 2 at hindex
  rw [hindex, elementary_card Y, elementary_card X, ← pow_succ] at he
  have he' := (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
  omega

private theorem faithful_natural_restriction
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

private theorem natural_central_kernel_faithful
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) G V) (hfaith : Function.Injective ρ) (hi : IsIrreducible ρ)
    (H X : Subgroup G) [H.Normal] [Group.IsPerfect H]
    (I : Submodule (ZMod 2) V) (hne : I ≠ ⊥)
    (hfix : fixedSpace ρ H = ⊥)
    (hH : H ≤ subspaceStabilizer ρ I) (hX : X ≤ subspaceStabilizer ρ I)
    (hk : (invariantSubspace ρ H I hH).toRepresentation.asGroupHom.ker ≤ center H)
    (n : ℕ) (hn : 5 ≤ n)
    (hm : Section06.HasModelOn
      (kerRepresentation (Section09.constituentAction ρ H X I hH hX)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    Function.Injective (invariantSubspace ρ H I hH).toRepresentation.asGroupHom := by
  let P := H ⊔ X
  let σ := Section09.constituentAction ρ H X I hH hX
  let q := QuotientGroup.mk' σ.ker
  let ι := Subgroup.inclusion (show H ≤ P from le_sup_left)
  let r := q.comp ι
  let R := (invariantSubspace ρ H I hH).toRepresentation.asGroupHom
  have hrange : r.range = (H.subgroupOf P).map q := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨a,rfl⟩; exact a.property
    · intro hx; exact ⟨⟨x,hx⟩,rfl⟩
  let : r.range.Normal := hrange ▸ Subgroup.Normal.map inferInstance q
    (QuotientGroup.mk'_surjective _)
  obtain ⟨e,_,_⟩ := hm
  let d := Subgroup.topEquiv.symm.trans e
  let j := d.toMonoidHom.comp r
  have hj (a : H) : j a = 1 ↔ R a = 1 := by
    constructor
    · intro ha
      have hq : q (ι a) = 1 := d.injective (by
        change d (q (ι a)) = 1 at ha
        simpa only [map_one] using ha)
      have hσ : σ (ι a) = 1 := (QuotientGroup.eq_one_iff _).mp hq
      exact Units.ext hσ
    · intro ha
      have hσ : ι a ∈ σ.ker := congrArg Units.val ha
      change d (q (ι a)) = 1
      have hq : q (ι a) = 1 := (QuotientGroup.eq_one_iff (ι a)).mpr hσ
      rw [hq,map_one]
  have hjrange : j.range = r.range.map d.toMonoidHom := MonoidHom.range_comp _ _
  let : j.range.Normal := hjrange ▸ Subgroup.Normal.map inferInstance d.toMonoidHom d.surjective
  let : Group.IsPerfect j.range := Group.IsPerfect.range j
  have hjne : j.range ≠ ⊥ := by
    intro hz
    apply hne
    apply bot_unique
    rw [← hfix]
    intro u hu a
    have ha : R a = 1 := (hj a).mp (mem_bot.mp (hz ▸ (show j a ∈ j.range from ⟨a,rfl⟩)))
    exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I => (f.val ⟨u,hu⟩ : V)) ha
  let : Nontrivial j.range := j.range.nontrivial_iff_ne_bot.mpr hjne
  have hA : j.range = alternatingGroup (Fin n) :=
    Equiv.Perm.eq_alternatingGroup_of_perfect_normal (by simpa using hn) j.range
  have hc : center j.range = ⊥ := by
    rw [hA]
    exact alternatingGroup.center_eq_bot (by simpa using (show 4 ≤ n by omega))
  let Z := (center H).map H.subtype
  let : Z.Normal := inferInstanceAs ((center H).map H.subtype).Normal
  have hZfix : I ≤ fixedSpace ρ Z := by
    intro u hu z
    obtain ⟨a,ha,he⟩ := z.property
    have hja : j.rangeRestrict a = 1 := by
      apply mem_bot.mp
      rw [← hc]
      apply mem_center_iff.mpr
      intro b
      obtain ⟨c,rfl⟩ := j.rangeRestrict_surjective b
      exact (map_mul j.rangeRestrict c a).symm.trans
        ((congrArg j.rangeRestrict (mem_center_iff.mp ha c)).trans (map_mul j.rangeRestrict a c))
    have hRa : R a = 1 := (hj a).mp (congrArg Subtype.val hja)
    have hh := congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I => (f.val ⟨u,hu⟩ : V)) hRa
    change ρ (z : G) u = u
    change ρ (a : G) u = u at hh
    change (a : G) = (z : G) at he
    rwa [he] at hh
  have hZ : Z = ⊥ := by
    by_contra hz
    have he := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ hfaith hi Z hz
    exact hne (bot_unique (he ▸ hZfix))
  apply (MonoidHom.ker_eq_bot_iff R).mp
  apply bot_unique
  intro a ha
  have hz : (a : G) ∈ Z := ⟨a,hk ha,rfl⟩
  rw [hZ,mem_bot] at hz
  exact mem_bot.mpr (Subtype.ext hz)

/-- The exchanged natural remainder is the four-dimensional S₆
constituent with noncentral kernel and more than one component in its orbit.
The original actor has rank four on an eight-dimensional module. -/
@[expose] def WholeOrNoncentralSixModels
    {D U : Type*} [Group D] [Finite D] [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U]
    (ρ : Representation (ZMod 2) D U) (B : LinearMap.BilinForm (ZMod 2) U)
    (v : U) (W : Submodule (ZMod 2) U) (X : Subgroup D)
    [IsElementaryAbelian 2 X] : Prop :=
  ∃ L : Subgroup D, IsComponent D L ∧ ⁅L,X⁆ ≠ ⊥ ∧
    Section10.ComponentOrthogonalData ρ B L ∧
    (Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L (componentOrbit L ⊤)
      (finrank (ZMod 2) (Additive X)) ∨
      ∃ I : Submodule (ZMod 2) U,
        ∃ hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I,
          v ∉ I ∧ Section10.ExchangedConstituentGeometry ρ B v W X I ∧
          (∃ x : X, I.map (ρ x) ≠ I ∧ IsCompl I (I.map (ρ x))) ∧
          finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) U = 8 ∧
          finrank (ZMod 2) (Additive X) = 4 ∧ (B.restrict I).Nondegenerate ∧
          componentOrbit L ⊤ ≠ L ∧
          ¬ (invariantSubspace ρ (componentOrbit L ⊤) I
            hI.invariant).toRepresentation.asGroupHom.ker ≤ center (componentOrbit L ⊤) ∧
          Section06.HasModelOn (kerRepresentation (Section09.constituentAction ρ
            (componentOrbit L ⊤) (X ⊓ subspaceStabilizer ρ I) I hI.invariant inf_le_right))
            ⊤ ⊤ (BinaryPermutation.naturalRepresentation (Fin 6)))

end CFSG.Quasithin.ChapterG.Section11
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter12.Section08.InvariantFlag.Symplectic
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ChapterG.Section11
namespace LargeActorSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {M Mc : Subgroup G}
  {F : InvariantFlag T (rankTwoSeed T M) 2}
  [IsElementaryAbelian 2 (rankTwoSeed T M)] [IsElementaryAbelian 2 F.Uhat]
  {g : G} [IsElementaryAbelian 2 (F.terminalDot (F.X g))]
  {B : LinearMap.BilinForm (ZMod 2) (Additive F.Uhat)} {v : Additive F.Uhat}
  (s : LargeActorSource T M Mc F g B v)
include s

/-- The only natural symmetric exchanged constituent for a larger actor is
S₆ in degree four; the literal whole module has degree eight and actor rank four. -/
theorem exchanged_natural_six
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (n : ℕ) (hn : 5 ≤ n) (hnu : n ≤ 8)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin n))) :
    n = 6 ∧ finrank (ZMod 2) I = 4 ∧ finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
      finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 := by
  obtain ⟨x,_,hc,hd,_⟩ := exchanged_lowRank_pair s.hypothesis s.classification_input.1
    s.low_rank_witness s.normal_sylow s.nonsolvable hL hm hI hgeo
  have hgen : Homogeneous.orbitSpan F.terminalRepresentation (F.terminalDot (F.X g)) I = ⊤ := by
    apply top_unique
    rw [← hc.sup_eq_top]
    exact sup_le (Homogeneous.le_orbitSpan _ _ I) (le_iSup (fun y : F.terminalDot (F.X g) => I.map (F.terminalRepresentation y)) x)
  obtain ⟨_,_,_,_,hi,_⟩ := hgeo
  have hb := exchanged_natural_actor_bound s.hypothesis hI.invariant hgen hi n
  obtain ⟨e,c,stable,hc'⟩ := hmodel
  have hdim := c.finrank_eq
  rw [finrank_top] at hdim
  have hm' := s.half_degree_le_actor
  have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
  rcases hn' with rfl | rfl | rfl | rfl
  · have hr := hb 2 ⟨e,c,stable,hc'⟩
      Sporadic.Mathieu.M22ValueBound.SmallQuotients.symmetricFive_primeRank_le_two
    simp only [BinaryPermutation.finrank_natural_odd (Fin 5) (by decide),Fintype.card_fin] at hdim
    omega
  · have hr := hb 3 ⟨e,c,stable,hc'⟩
      BinaryNaturalDual.FiveActors.ModuleGeometry.symmetric_six_rank_le_three
    simp only [BinaryPermutation.finrank_natural_even (Fin 6) (by decide),Fintype.card_fin] at hdim
    exact ⟨rfl,by omega,by omega,by omega⟩
  · have hr := hb 3 ⟨e,c,stable,hc'⟩
      Representation.AlternatingSevenConjugatePair.ElementaryGeometry.primeRank_symmetric.le
    simp only [BinaryPermutation.finrank_natural_odd (Fin 7) (by decide),Fintype.card_fin] at hdim
    omega
  · have hr := hb 4 ⟨e,c,stable,hc'⟩ symmetric_eight_two_rank
    simp only [BinaryPermutation.finrank_natural_even (Fin 8) (by decide),Fintype.card_fin] at hdim
    omega

private theorem exchanged_conjugation_injective
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hgen : Homogeneous.orbitSpan F.terminalRepresentation (F.terminalDot (F.X g)) I = ⊤) :
    letI := componentOrbit_top_normal L
    Function.Injective (MulAut.conjNormal.comp (F.terminalDot (F.X g)).subtype :
      F.terminalDot (F.X g) →* MulAut (componentOrbit L ⊤)) := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let X := F.terminalDot (F.X g)
  let ρ := F.terminalRepresentation
  have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible ρ s.hypothesis.faithful
    (s.hypothesis.irreducible_of_not_solvable s.nonsolvable) H hL.componentOrbit_top_ne_bot
  let f : X →* MulAut H := MulAut.conjNormal.comp X.subtype
  apply (injective_iff_map_eq_one f).mpr
  intro z hz
  have hzi : (z : F.TerminalHdot)⁻¹ = z := inv_eq_iff_mul_eq_one.mpr (by
    simpa only [pow_two] using elemPow_eq_one_of_isElementaryAbelian (p := 2)
      (z : F.TerminalHdot) z.property)
  have hzI : (z : F.TerminalHdot) ∈ subspaceStabilizer ρ I := by
    by_contra hn
    have hm : I.map (ρ (z : F.TerminalHdot)⁻¹) ≠ I := by
      rw [hzi]
      exact fun he => hn ((subspace_map_eq_iff ρ I _).mp he)
    have ho := hI.conjugation_not_inner ρ hfix z hm
    apply ho
    change f z ∈ MulAut.innerSubgroup H
    rw [hz]
    exact (MulAut.innerSubgroup H).one_mem
  have hzc : (z : F.TerminalHdot) ∈ centralizer (H : Set F.TerminalHdot) := by
    rw [← MulAut.conjNormal_ker_eq_centralizer]
    exact hz
  have he := s.hypothesis.spanning_constituent_stabilizer_centralizer_eq_bot hI.isIrrPlus hgen
  apply Subtype.ext
  apply mem_bot.mp
  rw [← he]
  exact ⟨⟨hzI,z.property⟩,hzc⟩

/-- The remaining natural S₆ constituent has a nontrivial component-orbit
kernel: otherwise the full rank-four actor embeds in Aut(A₆), of two-rank three. -/
theorem exchanged_natural_six_nonfaithful
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 6))) :
    ¬ Function.Injective (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤)
      I hI.invariant).toRepresentation.asGroupHom := by
  intro hf
  let ρ := F.terminalRepresentation
  let H := componentOrbit L ⊤
  let X := F.terminalDot (F.X g)
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  let : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hL.componentOrbit_top_ne_bot
  have hf' : Function.Injective (invariantSubspace ρ H I hI.invariant).toRepresentation := by
    intro a b hab
    exact hf (Units.ext hab)
  obtain ⟨e,_,_⟩ := faithful_natural_restriction ρ H (X ⊓ subspaceStabilizer ρ I)
    I hI.invariant inf_le_right hf' 6 (by decide) hmodel
  obtain ⟨x,_,hc,_,_⟩ := exchanged_lowRank_pair s.hypothesis s.classification_input.1
    s.low_rank_witness s.normal_sylow s.nonsolvable hL hm hI hgeo
  have hgen : Homogeneous.orbitSpan ρ X I = ⊤ := by
    apply top_unique
    rw [← hc.sup_eq_top]
    exact sup_le (Homogeneous.le_orbitSpan _ _ I) (le_iSup (fun y : F.terminalDot (F.X g) => I.map (F.terminalRepresentation y)) x)
  let j : X →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal.comp X.subtype)
  have hj : Function.Injective j :=
    (MulAut.congr e).injective.comp (s.exchanged_conjugation_injective hL hI hgen)
  let : IsElementaryAbelian 2 j.range := IsElementaryAbelian.of_injective (MonoidHom.ofInjective hj).symm.toMonoidHom
    (MonoidHom.ofInjective hj).symm.injective
  have hb := AlternatingSix.ShadowLocal.elementary_card_le_eight j.range
  rw [← Nat.card_congr (MonoidHom.ofInjective hj).toEquiv, elementary_card X] at hb
  have hd := (s.exchanged_natural_six hL hm hI hgeo 6 (by decide) (by decide) hmodel).2.2.2
  change finrank (ZMod 2) (Additive X) = 4 at hd
  rw [hd] at hb
  norm_num at hb

/-- The remaining natural S₆ constituent has a noncentral kernel. A central
kernel would vanish because its actual perfect image is the centerless A₆. -/
theorem exchanged_natural_six_noncentral_kernel
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 6))) :
    ¬ (invariantSubspace F.terminalRepresentation (componentOrbit L ⊤)
      I hI.invariant).toRepresentation.asGroupHom.ker ≤ center (componentOrbit L ⊤) := by
  intro hk
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
  have hi := s.hypothesis.irreducible_of_not_solvable s.nonsolvable
  exact s.exchanged_natural_six_nonfaithful hL hm hI hgeo hmodel
    (natural_central_kernel_faithful F.terminalRepresentation s.hypothesis.faithful hi H
      (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I) I
      (hI.isIrrPlus.ne_bot F.terminalRepresentation)
      (fixedSpace_eq_bot_of_normal_faithful_irreducible F.terminalRepresentation
        s.hypothesis.faithful hi H hL.componentOrbit_top_ne_bot)
      hI.invariant inf_le_right hk 6 (by decide) hmodel)

/-- The noncentral kernel forces a genuine two-component orbit. -/
theorem exchanged_natural_six_orbit_ne_component
    {L : Subgroup F.TerminalHdot} (hL : IsComponent F.TerminalHdot L)
    (hm : ⁅L,F.terminalDot (F.X g)⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) (Additive F.Uhat)}
    (hI : Homogeneous.IsIrrPlusWith F.terminalRepresentation (componentOrbit L ⊤)
      (F.terminalDot (F.X g)) I)
    (hgeo : ChapterG.Section10.ExchangedConstituentGeometry F.terminalRepresentation B v
      (hatSpace F (F.E g)) (F.terminalDot (F.X g)) I)
    (hmodel : ChapterG.Section06.HasModelOn
      (kerRepresentation (ChapterG.Section09.constituentAction F.terminalRepresentation
        (componentOrbit L ⊤) (F.terminalDot (F.X g) ⊓ subspaceStabilizer F.terminalRepresentation I)
        I hI.invariant inf_le_right)) ⊤ ⊤
      (BinaryPermutation.naturalRepresentation (Fin 6))) : componentOrbit L ⊤ ≠ L := by
  intro he
  have hn := s.exchanged_natural_six_noncentral_kernel hL hm hI hgeo hmodel
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let R := (invariantSubspace F.terminalRepresentation H I hI.invariant).toRepresentation.asGroupHom
  let : IsQuasisimple H := by
    change IsQuasisimple (componentOrbit L ⊤)
    rw [he]
    exact hL.2
  rcases IsQuasisimple.normal_le_center_or_eq_top R.ker with hc | ht
  · exact hn hc
  · have hfix := fixedSpace_eq_bot_of_normal_faithful_irreducible F.terminalRepresentation
      s.hypothesis.faithful (s.hypothesis.irreducible_of_not_solvable s.nonsolvable)
      H hL.componentOrbit_top_ne_bot
    have hle : I ≤ fixedSpace F.terminalRepresentation H := by
      intro u hu a
      have ha : R a = 1 := by
        change a ∈ R.ker
        rw [ht]
        exact mem_top a
      exact congrArg (fun f : LinearMap.GeneralLinearGroup (ZMod 2) I =>
        (f.val ⟨u,hu⟩ : Additive F.Uhat)) ha
    exact hI.isIrrPlus.ne_bot F.terminalRepresentation (bot_unique (hfix ▸ hle))

/-- The exceptional S₈ whole-action branch also has the original actor rank
exactly four; its ambient exclusion remains a separate source argument. -/
theorem actor_eq_four_of_eight_symmetric
    (hd : finrank (ZMod 2) (Additive F.Uhat) = 8)
    (e : F.TerminalHdot ≃* Equiv.Perm (Fin 8)) :
    finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 := by
  let X := F.terminalDot (F.X g)
  let A := X.map e.toMonoidHom
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hb := (primeRank_le_iff_elementary_card_le _).mp symmetric_eight_two_rank A inferInstance
  rw [Subgroup.card_map_of_injective e.injective, elementary_card X] at hb
  have hu := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb
  change finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) ≤ 4 at hu
  have hl := s.half_degree_le_actor
  rw [hd] at hl
  omega

/-- Eliminate the exchanged S₅, S₇ and S₈ constituents and the faithful S₆
constituent. The whole-component and marked full-four branches remain explicit. -/
theorem degree_cases_or_full_four_or_noncentral_six :
    ((finrank (ZMod 2) (Additive F.Uhat) = 4 ∧
        2 ≤ finrank (ZMod 2) (Additive (F.terminalDot (F.X g)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 6 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 3 ∧
        Nonempty (F.TerminalHdot ≃* Atlas.G2.Model (ZMod 2)))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        WholeOrNoncentralSixModels F.terminalRepresentation B v
          (hatSpace F (F.E g)) (F.terminalDot (F.X g))) := by
  rcases s.degree_cases_or_full_four_or_natural with hc | ⟨hd,⟨e⟩,hmodel⟩ |
    ⟨hd,L,hL,hm,horth,hwhole | hex⟩
  · exact Or.inl hc
  · exact Or.inr (Or.inl ⟨hd,s.actor_eq_four_of_eight_symmetric hd e,⟨e⟩,hmodel⟩)
  · exact Or.inr (Or.inr ⟨hd,L,hL,hm,horth,Or.inl hwhole⟩)
  · obtain ⟨I,hI,hv,hgeo,hpair,_,_,hnd,n,hn,hnu,hmodel⟩ := hex
    obtain ⟨rfl,hI4,h8,hm4⟩ := s.exchanged_natural_six hL hm hI hgeo n hn hnu hmodel
    exact Or.inr (Or.inr ⟨hd,L,hL,hm,horth,Or.inr
      ⟨I,hI,hv,hgeo,hpair,hI4,h8,hm4,hnd,
        s.exchanged_natural_six_orbit_ne_component hL hm hI hgeo hmodel,
        s.exchanged_natural_six_noncentral_kernel hL hm hI hgeo hmodel,hmodel⟩⟩)

/-- Apply the refined alternatives to the literal larger-actor component
consumer, retaining the complete full G₂(2) equivalence in the numerical input. -/
theorem component_or_full_four_or_noncentral_six
    (hfour : finrank (ZMod 2) (Additive F.Uhat) = 4 →
      ∀ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D →
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ → SmallComponentImage D)
    (hsix : ∀ K : Subgroup G, ComponentLift F g K →
      Nonempty (F.terminalDot K ≃* alternatingGroup (Fin 6)) → False) :
    ((∃ D : Subgroup F.TerminalHdot, IsComponent F.TerminalHdot D ∧
        ⁅D,F.terminalDot (F.X g)⁆ ≠ ⊥ ∧ Nonempty (D ≃* alternatingGroup (Fin 5))) ∨
      (∃ K : Subgroup G, ComponentLift F g K ∧ (F.terminalDot K).Normal ∧
        Nonempty (F.terminalDot K ≃* Atlas.G2.BinaryParabolicPair.DerivedModel) ∧
        F.terminalHatAction.ker.comap (K.subgroupOf F.H).subtype =
          pCore 2 (K.subgroupOf F.H))) ∨
      (finrank (ZMod 2) (Additive F.Uhat) = 8 ∧
        finrank (ZMod 2) (Additive (F.terminalDot (F.X g))) = 4 ∧
        Nonempty (F.TerminalHdot ≃* Equiv.Perm (Fin 8)) ∧
        FullLinearFour.MarkedAlternative F.terminalRepresentation B v (hatSpace F (F.E g))
          (F.terminalDot (F.X g))
          ((F.terminalDot (conjugate F.ZU g)).subgroupOf (F.terminalDot (F.X g)))) ∨
      (6 ≤ finrank (ZMod 2) (Additive F.Uhat) ∧
        WholeOrNoncentralSixModels F.terminalRepresentation B v
          (hatSpace F (F.E g)) (F.terminalDot (F.X g))) := by
  rcases s.degree_cases_or_full_four_or_noncentral_six with hd | hr
  · exact Or.inl (source_component_large_actor_of_degree_cases s.simple T s.empty s.maximal
      s.unique_overgroup s.many_overgroups s.seed_card
      (Classical.choice s.centralizer_quotient) F s.nonabelian g s.parabolic_mem
      s.normalizer_not_mem s.nonsolvable s.hypothesis hd hfour hsix)
  · exact Or.inr hr

end LargeActorSource
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.TerminalSolvable
