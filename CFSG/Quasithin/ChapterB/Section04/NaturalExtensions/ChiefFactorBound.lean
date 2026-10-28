module

public import CFSG.Quasithin.ChapterB.Section04.NaturalExtensions.FixedSpaces
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.ExceptionalExtension.NonsplitCase.Inputs
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity
public import Theory.Representation.BinaryOffender.SingleNoncentralFlag
public import Theory.Representation.SLThreeCentralExtension.ChiefCohomology

/-!
# The single natural chief factor dimension bound

A literal invariant chief flag with one natural SL₃(2) factor gives an
indecomposable central natural cover on the actual commutator [V,G]. The
previous central-kernel bound makes its dimension three or four. In an
indecomposable module every fixed vector lies in this nonzero commutator,
so the connecting cohomology map bounds V/[V,G]. Natural H¹ has dimension
one; the four-dimensional central cover has zero H¹ by the independent
involution calculation in `SLThreeCentralExtension.ChiefCohomology`.
These two cases give dimension three or four for V itself.

This is a cohomological alternative to the source's degree-eight permutation
argument. There is no FF, central-quotient-shape, Gaschütz or earlier B.4.8(4)
premise. `earlierB48Four` supplies the exact universally quantified B.5 input.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), B.4.8(4),
printed pp.91–92.
-/

public section

open Representation Representation.BinaryOffender
open Representation.OneCohomology
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
open CFSG.Quasithin.ChapterB.SourceInduction.ExceptionalExtension.Nonsplit
open CFSG.Quasithin.ChapterB.NaturalExtensions

namespace CFSG.Quasithin.ChapterB.NaturalExtensions.ChiefFactorBound
universe u v
variable {D : Type u} [Group D] {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V)

private lemma fixed_le_of_indecomposable (hind : IsIndecomposable ρ)
    (J : Subrepresentation ρ) (hJ : J.toSubmodule ≠ ⊥)
    (htriv : HasTrivialQuotient J) :
    OneCohomology.fixed ρ ≤ J.toSubmodule := by
  intro v hv
  by_contra hvJ
  let L : Submodule (ZMod 2) V := Submodule.span (ZMod 2) {v}
  have hL : L ≤ OneCohomology.fixed ρ := Submodule.span_le.mpr (by
    rintro w (rfl : w = v)
    exact hv)
  obtain ⟨A, hJA, hAL⟩ := (Submodule.disjoint_span_singleton_of_notMem hvJ).exists_isCompl
  let A' : Subrepresentation ρ := ⟨A, by
    intro g w hw
    have hm := hJA (htriv g w)
    simpa only [sub_add_cancel] using A.add_mem hm hw⟩
  let L' : Subrepresentation ρ := ⟨L, by
    intro g w hw
    rw [hL hw g]
    exact hw⟩
  rcases hind.2 A' L' hAL with hA | hL0
  · exact hJ (bot_unique (hJA.trans (congrArg Subrepresentation.toSubmodule hA).le))
  · have hvL : v ∈ L := Submodule.subset_span (Set.mem_singleton v)
    have h0 : L = ⊥ := congrArg Subrepresentation.toSubmodule hL0
    rw [h0] at hvL
    exact hvJ (hvL ▸ J.toSubmodule.zero_mem)

private lemma quotient_dim_le_H1 [Finite D] [FiniteDimensional (ZMod 2) V]
    (hind : IsIndecomposable ρ) (J : Subrepresentation ρ)
    (hJ : J.toSubmodule ≠ ⊥) (htriv : HasTrivialQuotient J) :
    Module.finrank (ZMod 2) (V ⧸ J.toSubmodule) ≤
      Module.finrank (ZMod 2) (H1 J.toRepresentation) := by
  apply LinearMap.finrank_le_finrank_of_injective (f := quotientToH1 J htriv)
  apply LinearMap.ker_eq_bot.mp
  apply Submodule.ker_liftQ_eq_bot
  rw [ker_extensionClass, sup_eq_left.mpr (fixed_le_of_indecomposable ρ hind J hJ htriv)]

private lemma flag_witness [FiniteDimensional (ZMod 2) V]
    (hflag : UniqueNoncentralNaturalFactor ρ) :
    ∃ (n : ℕ) (c : ℕ → Subrepresentation ρ) (i : ℕ),
      Nonempty (SingleNoncentralFlagWitness ρ ⊤ c i n) ∧
      IsLinearNatural (sectionRepresentation ρ (c i) (c (i+1))) BinaryField.two 3 := by
  obtain ⟨n,c,i,hmono,hzero,htop,_hchief,hi,hnat,hcentral⟩ := hflag
  obtain ⟨e⟩ := hnat
  let : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) BinaryField.two.Carrier) := SLThreeCentralExtension.actor_isPerfect
  let : Group.IsPerfect D := Group.IsPerfect.ofSurjective
    (f := e.groupEquiv.symm.toMonoidHom) e.groupEquiv.symm.surjective
  let : Group.IsPerfect (⊤ : Subgroup D) := Group.IsPerfect.ofSurjective
    (f := (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D).symm.toMonoidHom)
    (Subgroup.topEquiv : (⊤ : Subgroup D) ≃* D).symm.surjective
  let τ := sectionRepresentation ρ (c i) (c (i+1))
  let et : ActionEquiv (τ.comp (⊤ : Subgroup D).subtype)
      (linearNatural BinaryField.two 3) :=
    ⟨Subgroup.topEquiv.trans e.groupEquiv, e.linearEquiv, fun g v => e.intertwines g v⟩
  have hirr : IsIrreducible (τ.comp (⊤ : Subgroup D).subtype) :=
    irreducible_of_equiv et (linearNatural_irreducible _ (by decide))
  have hnoncentral : ∃ g ∈ (⊤ : Subgroup D), ∃ w, τ g w ≠ w := by
    by_contra! h
    have hfixed : OneCohomology.fixed BinaryLinearThree.W = ⊤ := by
      apply top_unique
      intro w _ g
      obtain ⟨v,rfl⟩ := e.linearEquiv.surjective w
      obtain ⟨a,rfl⟩ := e.groupEquiv.surjective g
      exact (e.intertwines a v).symm.trans (congrArg e.linearEquiv (h a (by trivial) v))
    rw [SLHigherNatural.fixed_eq_bot (by decide : 2 ≤ 3)] at hfixed
    exact bot_ne_top hfixed
  refine ⟨n,c,i,?_,⟨e⟩⟩
  exact singleNoncentralFlag ρ ⊤ c i n hmono hzero htop hi
    (fun j hj hji g _ v => hcentral j hj hji g v) hirr hnoncentral

/-- The actual commutator module, marked as a central natural cover. -/
structure NaturalCommutatorCover [FiniteDimensional (ZMod 2) V] where
  space : Subrepresentation ρ
  space_eq : space.toSubmodule = moved ρ ⊤
  nonzero : space.toSubmodule ≠ ⊥
  groupEquiv : D ≃* BinaryLinearThree.Group
  projection : Representation.IntertwiningMap
    (space.toRepresentation.comp groupEquiv.symm.toMonoidHom) BinaryLinearThree.W
  cover : IsCover projection
  dimension : Module.finrank (ZMod 2) space.toSubmodule = 3 ∨
    Module.finrank (ZMod 2) space.toSubmodule = 4

/-- Construct the cover from the given chief flag, without any ambient splitting premise. -/
theorem naturalCommutatorCover [FiniteDimensional (ZMod 2) V]
    (hflag : UniqueNoncentralNaturalFactor ρ) : Nonempty (NaturalCommutatorCover ρ) := by
  obtain ⟨n,c,i,⟨s⟩,⟨e⟩⟩ := flag_witness ρ hflag
  change ActionEquiv (sectionRepresentation ρ (c i) (c (i+1))) BinaryLinearThree.W at e
  let σ : Representation (ZMod 2) BinaryLinearThree.Group s.J.toSubmodule :=
    s.J.toRepresentation.comp e.groupEquiv.symm.toMonoidHom
  let p : σ.IntertwiningMap BinaryLinearThree.W :=
    (e.linearEquiv.toLinearMap.comp s.map).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      change e.linearEquiv (s.map (s.J.toRepresentation (e.groupEquiv.symm g) v)) = _
      rw [s.map_equivariant, e.intertwines, e.groupEquiv.apply_symm_apply]
      rfl)
  have hp : Function.Surjective p := e.linearEquiv.surjective.comp s.map_surjective
  have hf : p.toLinearMap.ker ≤ OneCohomology.fixed σ := by
    intro v hv g
    have hv' : v ∈ s.map.ker := by
      apply e.linearEquiv.injective
      exact (show e.linearEquiv (s.map v) = 0 from hv).trans e.linearEquiv.map_zero.symm
    exact s.map_kernel_central hv' ⟨e.groupEquiv.symm g, by trivial⟩
  have hind : ∀ A B : Submodule (ZMod 2) s.J.toSubmodule,
      (∀ g v, v ∈ A → σ g v ∈ A) →
      (∀ g v, v ∈ B → σ g v ∈ B) → IsCompl A B → A = ⊥ ∨ B = ⊥ := by
    intro A B hA hB hAB
    apply s.indecomposable A B ?_ ?_ hAB
    · apply le_subspaceStabilizer
      intro g _ v hv
      have hh := hA (e.groupEquiv g) v hv
      simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        e.groupEquiv.symm_apply_apply] using hh
    · apply le_subspaceStabilizer
      intro g _ v hv
      have hh := hB (e.groupEquiv g) v hv
      simpa only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        e.groupEquiv.symm_apply_apply] using hh
  exact ⟨⟨s.J,s.J_eq_commutator,s.nonzero,e.groupEquiv,p,
    isCover_of_indecomposable p hp hf SLThreeCentralExtension.commutator_eq_top hind,
    central_quotient_dimension σ p hp hf hind⟩⟩

variable [FiniteDimensional (ZMod 2) V]

private lemma NaturalCommutatorCover.trivialQuotient (s : NaturalCommutatorCover ρ) :
    HasTrivialQuotient s.space := by
  intro g v
  change ρ g v - v ∈ s.space.toSubmodule
  rw [s.space_eq]
  exact Submodule.subset_span ⟨g,Subgroup.mem_top _,v,Submodule.mem_top,rfl⟩

private lemma NaturalCommutatorCover.H1_three (s : NaturalCommutatorCover ρ)
    (hdim : Module.finrank (ZMod 2) s.space.toSubmodule = 3) :
    Module.finrank (ZMod 2) (H1 s.space.toRepresentation) = 1 := by
  have heq : Module.finrank (ZMod 2) s.space.toSubmodule =
      Module.finrank (ZMod 2) BinaryLinearThree.Vector := by
    rw [hdim, Module.finrank_fin_fun]
  have hp := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq).mpr
    s.cover.1
  let e := LinearEquiv.ofBijective s.projection.toLinearMap ⟨hp,s.cover.1⟩
  have he (g : D) (v : s.space.toSubmodule) :
      e (s.space.toRepresentation g v) = BinaryLinearThree.W (s.groupEquiv g) (e v) := by
    have hh := LinearMap.congr_fun (s.projection.isIntertwining' (s.groupEquiv g)) v
    change s.projection.toLinearMap (s.space.toRepresentation g v) =
      BinaryLinearThree.W (s.groupEquiv g) (s.projection.toLinearMap v)
    simpa only [LinearMap.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      s.groupEquiv.symm_apply_apply] using hh
  exact (H1Congr s.space.toRepresentation BinaryLinearThree.W s.groupEquiv e he).finrank_eq.trans
    SLHigherNatural.finrank_H1_sl3_two

/-- B.4.8(4): one natural noncentral chief factor bounds the entire indecomposable
module, including all central factors above and below it. -/
theorem dimension_of_unique_natural [Finite D]
    (hind : IsIndecomposable ρ)
    (hflag : UniqueNoncentralNaturalFactor ρ) :
    Module.finrank (ZMod 2) V = 3 ∨ Module.finrank (ZMod 2) V = 4 := by
  obtain ⟨s⟩ := naturalCommutatorCover ρ hflag
  have hquot := quotient_dim_le_H1 ρ hind s.space s.nonzero (s.trivialQuotient ρ)
  have hdim := Submodule.finrank_quotient_add_finrank s.space.toSubmodule
  rcases s.dimension with h3 | h4
  · rw [s.H1_three ρ h3] at hquot
    omega
  · let σ := s.space.toRepresentation.comp s.groupEquiv.symm.toMonoidHom
    have he (g : D) (v : s.space.toSubmodule) :
        (LinearEquiv.refl (ZMod 2) s.space.toSubmodule) (s.space.toRepresentation g v) =
          σ (s.groupEquiv g) ((LinearEquiv.refl (ZMod 2) s.space.toSubmodule) v) := by
      simp only [σ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        s.groupEquiv.symm_apply_apply, LinearEquiv.refl_apply]
    have hz : Module.finrank (ZMod 2) (H1 s.space.toRepresentation) = 0 :=
      (H1Congr s.space.toRepresentation σ s.groupEquiv
        (LinearEquiv.refl (ZMod 2) s.space.toSubmodule) he).finrank_eq.trans
          (by
            let := SLThreeCentralExtension.H1_subsingleton_of_four_dimensional_cover
              σ s.projection s.cover h4
            exact Module.finrank_zero_of_subsingleton)
    rw [hz] at hquot
    right
    omega

/-- The literal universally quantified earlier-source input consumed by B.5.
All cohomology and cover premises have been discharged. -/
theorem earlierB48Four :
    EarlierB48Four.{u,v} := by
  intro D _ _ U _ _ _ σ _ hi _ hn
  exact dimension_of_unique_natural σ hi hn

end CFSG.Quasithin.ChapterB.NaturalExtensions.ChiefFactorBound
