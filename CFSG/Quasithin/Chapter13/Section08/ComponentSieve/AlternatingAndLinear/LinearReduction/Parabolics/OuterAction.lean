module

public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.Defs
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.AutomorphismActions
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.SpecificGroups.BinaryLinear.InvariantNodeActions.MarkedExtension
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8
public import CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear.Flags

/-!
# Invariant minimal parabolics and the marked S₈ extension

The chapter's deleted basis flag has exactly the intrinsic minimal-parabolic
image. An actor outside a self-centralizing normal component induces an outer
automorphism. Inner/inverse-transpose coverage and actual flag geometry force
an individually preserved deleted flag to omit dimension two in dimension four.
The single-parabolic deduction works for any normalizing subgroup S; it does
not need the extra source hypotheses that S is Sylow and X = K ∨ S.

In the outer case, faithful conjugation constructs an equivalence of the whole
ambient group with S₈. Its restriction to K is the original PSL₄(2) marking
followed by the checked PSL₄(2)–A₈ comparison. The image of P retains the
original flag. The comparison import retains the ATLAS attribution and license.

For two distinct individually normalized parabolics, intersecting the ambient
Sylow with K and transporting through the original model gives a common Sylow
in their linear images. The geometric alignment theorem handles their possibly
different bases, and forces every actor into K.

These prove the intrinsic outer-action steps in Aschbacher–Smith 13.8.25,
printed pp.959–960 (PDF pp.976–977), combined manuscript of 1 March 2004.
Identifying the source subgroups as these actual flag stabilizers, and the
remaining module and Levi arguments of 13.8.25, are separate deductions.
-/

@[expose] public section

open Subgroup Equiv
open CFSG.Quasithin.Chapter2.ComponentRefinement.LieType.Binary
open CFSG.Quasithin.Chapter15.Section03.FusionCore.ExtraspecialElimination.ComponentReduction.ModelReduction.BinaryModels.ParabolicIdentification.Linear

namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OuterAction

variable {X : Type*} [Group X] {K : Subgroup X}

/-- The literal deleted-flag stabilizer has the intrinsic basis-coordinate image. -/
theorem deletedFlag_linear_image {m : ℕ} (hm : 2 ≤ m)
    (e : K ≃* PSL (m + 1)) (b : Basis m) (i : Fin m) :
    ((ambientFlagStabilizer e (deletedFlag hm b i)).subgroupOf K).map
        (linearModel e).toMonoidHom = BinaryLinear.InvariantNodeActions.minimalParabolic b i := by
  rw [ambientFlagStabilizer]
  have he : ((flagStabilizer e (deletedFlag hm b i)).map K.subtype).subgroupOf K =
      flagStabilizer e (deletedFlag hm b i) := by
    ext k
    constructor
    · rintro ⟨x, hx, h⟩
      exact K.subtype_injective h ▸ hx
    · intro hk
      exact ⟨k, hk, rfl⟩
  rw [he, deletedFlag_stabilizer, Subgroup.map_comap_eq_self_of_surjective
      (linearModel e).surjective]
  rfl

/-- Any actor outside K gives an actual outer automorphism fixing the supplied parabolic. -/
theorem exists_outer_preserving_minimalParabolic [K.Normal]
    {m : ℕ} (hm : 2 ≤ m) (e : K ≃* PSL (m + 1))
    (b : Basis m) (i : Fin m) (P S : Subgroup X)
    (hP : P = ambientFlagStabilizer e (deletedFlag hm b i))
    (hc : centralizer (K : Set X) = ⊥) (hn : S ≤ normalizer (P : Set X))
    (hs : ¬ S ≤ K) :
    ∃ a : MulAut (BinaryLinear.OuterCyclic.LinearGroup (m + 1)),
      a ∉ MulAut.innerSubgroup _ ∧
      (BinaryLinear.InvariantNodeActions.minimalParabolic b i).map a.toMonoidHom =
        BinaryLinear.InvariantNodeActions.minimalParabolic b i := by
  obtain ⟨x, hx, hxK⟩ : ∃ x : X, x ∈ S ∧ x ∉ K := by
    by_contra h
    apply hs
    intro x hx
    by_contra hxK
    exact h ⟨x, hx, hxK⟩
  let a := BinaryLinear.InvariantNodeActions.componentAction K (linearModel e) x
  refine ⟨a, ?_, ?_⟩
  · exact fun ha => hxK
      ((BinaryLinear.InvariantNodeActions.componentAction_mem_inner K (linearModel e) hc x).mp ha)
  · have hPK : P ≤ K := hP ▸ ambientFlagStabilizer_le e _
    have hp := BinaryLinear.InvariantNodeActions.componentAction_map_subgroup K
      (linearModel e) P hPK x (hn hx)
    rw [hP, deletedFlag_linear_image] at hp
    exact hp

/-- The symmetric extension attached to this exact PSL₄(2) component marking. -/
noncomputable def markedSymmetricExtension [K.Normal] (e : K ≃* PSL 4)
    (hc : centralizer (K : Set X) = ⊥) (hK : K ≠ ⊤) : X ≃* Perm (Fin 8) :=
  BinaryLinear.InvariantNodeActions.symmetricExtension K
    (e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8) hc hK

theorem markedSymmetricExtension_on_component [K.Normal] (e : K ≃* PSL 4)
    (hc : centralizer (K : Set X) = ⊥) (hK : K ≠ ⊤) (k : K) :
    markedSymmetricExtension e hc hK k =
      (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8 (e k) : Perm (Fin 8)) :=
  BinaryLinear.InvariantNodeActions.symmetricExtension_on_subgroup K _ hc hK k

theorem markedSymmetricExtension_component_image [K.Normal] (e : K ≃* PSL 4)
    (hc : centralizer (K : Set X) = ⊥) (hK : K ≠ ⊤) :
    K.map (markedSymmetricExtension e hc hK).toMonoidHom = alternatingGroup (Fin 8) :=
  BinaryLinear.InvariantNodeActions.symmetricExtension_map K _ hc hK

theorem markedSymmetricExtension_flag_image [K.Normal] (e : K ≃* PSL 4)
    (hc : centralizer (K : Set X) = ⊥) (hK : K ≠ ⊤) (F : Flag 4) :
    (ambientFlagStabilizer e F).map (markedSymmetricExtension e hc hK).toMonoidHom =
      (flagStabilizer e F).map ((alternatingGroup (Fin 8)).subtype.comp
        (e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toMonoidHom) := by
  rw [ambientFlagStabilizer, Subgroup.map_map]
  congr 1
  apply MonoidHom.ext
  intro k
  exact markedSymmetricExtension_on_component e hc hK k

/-- The whole-group equivalence retains both the component marking and the original flag. -/
theorem exists_marked_symmetric_extension [K.Normal] (e : K ≃* PSL 4)
    (P S : Subgroup X) (F : Flag 4) (hP : P = ambientFlagStabilizer e F)
    (hc : centralizer (K : Set X) = ⊥) (hs : ¬ S ≤ K) :
    ∃ E : X ≃* Perm (Fin 8),
      (∀ k : K, E k = (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8 (e k) : Perm (Fin 8))) ∧
      K.map E.toMonoidHom = alternatingGroup (Fin 8) ∧
      P.map E.toMonoidHom = (flagStabilizer e F).map ((alternatingGroup (Fin 8)).subtype.comp
        (e.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toMonoidHom) := by
  have hK : K ≠ ⊤ := fun h => hs (h ▸ le_top)
  refine ⟨markedSymmetricExtension e hc hK,
    markedSymmetricExtension_on_component e hc hK,
    markedSymmetricExtension_component_image e hc hK, ?_⟩
  rw [hP]
  exact markedSymmetricExtension_flag_image e hc hK F

/-- A normalized minimal parabolic forces inner action or the middle node of PSL₄(2).
Here `i.val + 1` is the omitted proper dimension; `m + 1` is the model dimension. -/
theorem normalizing_deletedFlag_alternative [K.Normal]
    {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (e : K ≃* PSL (m + 1))
    (b : Basis m) (i : Fin m) (P S : Subgroup X)
    (hP : P = ambientFlagStabilizer e (deletedFlag hm₀ b i))
    (hc : centralizer (K : Set X) = ⊥) (hn : S ≤ normalizer (P : Set X)) :
    S ≤ K ∨ (m = 3 ∧ i.val + 1 = 2) := by
  by_cases hs : S ≤ K
  · exact Or.inl hs
  · obtain ⟨a, ha, hfix⟩ := exists_outer_preserving_minimalParabolic hm₀ e b i P S hP hc hn hs
    exact Or.inr (BinaryLinear.InvariantNodeActions.outer_preserves_minimalParabolic_middle
      hm₀ hm₁ b i a ha hfix)

/-- The complete invariant-node alternative, retaining the original projective
marking, ambient subgroup P, and deleted flag in the faithful S₈ equivalence. -/
theorem normalizing_deletedFlag_marked_alternative [K.Normal]
    {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (e : K ≃* PSL (m + 1))
    (b : Basis m) (i : Fin m) (P S : Subgroup X)
    (hP : P = ambientFlagStabilizer e (deletedFlag hm₀ b i))
    (hc : centralizer (K : Set X) = ⊥) (hn : S ≤ normalizer (P : Set X)) :
    S ≤ K ∨ ∃ hdim : m = 3, i.val + 1 = 2 ∧
      let e₄ : K ≃* PSL 4 := cast (congrArg (fun r => K ≃* PSL (r + 1)) hdim) e
      let F₄ : Flag 4 := cast (congrArg (fun r => Flag (r + 1)) hdim) (deletedFlag hm₀ b i)
      ∃ E : X ≃* Perm (Fin 8),
        (∀ k : K, E k =
          (Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8 (e₄ k) : Perm (Fin 8))) ∧
        K.map E.toMonoidHom = alternatingGroup (Fin 8) ∧
        P.map E.toMonoidHom = (flagStabilizer e₄ F₄).map
          ((alternatingGroup (Fin 8)).subtype.comp
            (e₄.trans Atlas.Comparisons.Exceptional.psl4TwoEquivAlt8).toMonoidHom) := by
  by_cases hs : S ≤ K
  · exact Or.inl hs
  · obtain ⟨hdim, hi⟩ := (normalizing_deletedFlag_alternative hm₀ hm₁ e b i P S hP hc hn).resolve_left hs
    subst m
    exact Or.inr ⟨rfl, hi,
      exists_marked_symmetric_extension e P S (deletedFlag hm₀ b i) hP hc hs⟩

/-- Individual normalization of two distinct minimal parabolics over S ∩ K
forces S ≤ K. Their bases may differ, and no setwise-pair hypothesis is used. -/
theorem le_component_of_normalizing_two_deletedFlags [Finite X] [K.Normal]
    {m : ℕ} (hm₀ : 2 ≤ m) (hm₁ : m ≤ 4) (e : K ≃* PSL (m + 1))
    (b c : Basis m) (i j : Fin m) (P Q : Subgroup X) (S : Sylow 2 X)
    (hP : P = ambientFlagStabilizer e (deletedFlag hm₀ b i))
    (hQ : Q = ambientFlagStabilizer e (deletedFlag hm₀ c j))
    (hc : centralizer (K : Set X) = ⊥)
    (hSP : (S : Subgroup X) ⊓ K ≤ P) (hSQ : (S : Subgroup X) ⊓ K ≤ Q)
    (hne : P ≠ Q)
    (hnP : (S : Subgroup X) ≤ normalizer (P : Set X))
    (hnQ : (S : Subgroup X) ≤ normalizer (Q : Set X)) :
    (S : Subgroup X) ≤ K := by
  have hPK : P ≤ K := hP ▸ ambientFlagStabilizer_le e _
  have hQK : Q ≤ K := hQ ▸ ambientFlagStabilizer_le e _
  have hP' : (P.subgroupOf K).map (linearModel e).toMonoidHom =
      BinaryLinear.InvariantNodeActions.minimalParabolic b i := by
    rw [hP, deletedFlag_linear_image]
  have hQ' : (Q.subgroupOf K).map (linearModel e).toMonoidHom =
      BinaryLinear.InvariantNodeActions.minimalParabolic c j := by
    rw [hQ, deletedFlag_linear_image]
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal K
  let U : Sylow 2 (BinaryLinear.OuterCyclic.LinearGroup (m + 1)) :=
    T.mapSurjective (f := (linearModel e).toMonoidHom) (linearModel e).surjective
  have hUP : (U : Subgroup _) ≤ BinaryLinear.InvariantNodeActions.minimalParabolic b i := by
    change (T : Subgroup K).map (linearModel e).toMonoidHom ≤ _
    rw [← hP']
    apply Subgroup.map_mono
    intro k hk
    have hkS : k ∈ (S : Subgroup X).subgroupOf K := hT ▸ hk
    exact hSP ⟨hkS, k.property⟩
  have hUQ : (U : Subgroup _) ≤ BinaryLinear.InvariantNodeActions.minimalParabolic c j := by
    change (T : Subgroup K).map (linearModel e).toMonoidHom ≤ _
    rw [← hQ']
    apply Subgroup.map_mono
    intro k hk
    have hkS : k ∈ (S : Subgroup X).subgroupOf K := hT ▸ hk
    exact hSQ ⟨hkS, k.property⟩
  have hneq : BinaryLinear.InvariantNodeActions.minimalParabolic b i ≠
      BinaryLinear.InvariantNodeActions.minimalParabolic c j := by
    intro he
    apply hne
    have hpq := Subgroup.map_injective (linearModel e).injective
      (hP'.trans (he.trans hQ'.symm))
    have hh := congrArg (fun R : Subgroup K => R.map K.subtype) hpq
    simpa only [Subgroup.map_subgroupOf_eq_of_le hPK,
      Subgroup.map_subgroupOf_eq_of_le hQK] using hh
  intro x hx
  apply (BinaryLinear.InvariantNodeActions.componentAction_mem_inner K (linearModel e) hc x).mp
  apply BinaryLinear.InvariantNodeActions.preserving_two_minimalParabolics_is_inner
    hm₀ hm₁ b c i j U hUP hUQ hneq
  · have hp := BinaryLinear.InvariantNodeActions.componentAction_map_subgroup K
      (linearModel e) P hPK x (hnP hx)
    simpa only [hP'] using hp
  · have hq := BinaryLinear.InvariantNodeActions.componentAction_map_subgroup K
      (linearModel e) Q hQK x (hnQ hx)
    simpa only [hQ'] using hq


end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.LinearReduction.Parabolics.OuterAction
