module
public import CFSG.Quasithin.ChapterF.Section01.SourceRecognition.DGS85.OriginalExtension.MarkedRestoration
public import Theory.GroupTheory.Amalgam.CompletionInnerAction
public import Theory.GroupTheory.AutomorphismOvergroupCore
public import Theory.GroupTheory.SolvableOuterQuotient

/-!
# Restoring the original endpoints in a marked completion's automorphism group

The original full Borel acts faithfully on the reduced amalgam. If this action
preserves the kernel of a marked faithful completion X, quotient descent gives
an action on X. Self-normalizing endpoint images and their exact intersection
identify precisely the inner actors with the reduced Borel. Normal-supplement
gluing then restores both original endpoints, with the same full Borel map and
both reduced endpoint restrictions. The outer index is exactly [B:B₀], so the
original Sylow order is the reduced order times this index. Local-factor image
markings pass through these constructed maps.

This is the conditional pumping step in Delgado--Goldschmidt--Stellmacher,
*Groups and Graphs* (1985), (15.2), printed pp.226--228, as applied to the genuine
F.1.1 source pair. The geometric preservation of the apartment quotient kernel
and recognition of the permissible Aut⁰(X) action remain separate premises.
The result does not upgrade parabolic-equivalence or type-only alternatives.
-/

public noncomputable section
open Subgroup Theory.GroupTheory RankTwoAmalgam
namespace CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
open SuzukiContainment
variable {G X : Type*} [Group G] [Group X]
  {L : Fin 2 → Subgroup G} {S : Subgroup G}
variable (h : HypothesisF11 L S)
  (c : FaithfulCompletion (reducedAmalgam L S) (G := X))

/-- The original full Borel preserves the kernel of the marked reduced
completion. This is the geometric premise still discharged in DGS 15.2. -/
abbrev PreservesCompletionKernel : Prop :=
  CompletionAction.PreservesCompletionKernel (reducedOverlapAction h) c

variable (hk : PreservesCompletionKernel h c)

abbrev completionAction : commonBorel L S →* MulAut X :=
  CompletionAction.completionAction (reducedOverlapAction h) c hk

@[simp] theorem completionAction_left (b : commonBorel L S)
    (x : parabolic L (reducedSylow L S) 0) :
    completionAction h c hk b (c.left x) = c.left (reducedEndpointAction h 0 b x) := by
  rw [completionAction, CompletionAction.completionAction_left, reducedOverlapAction_left]

@[simp] theorem completionAction_right (b : commonBorel L S)
    (x : parabolic L (reducedSylow L S) 1) :
    completionAction h c hk b (c.right x) = c.right (reducedEndpointAction h 1 b x) := by
  rw [completionAction, CompletionAction.completionAction_right, reducedOverlapAction_right]

theorem completionAction_injective : Function.Injective (completionAction h c hk) :=
  CompletionAction.completionAction_injective (reducedOverlapAction h) c hk
    (reducedOverlapAction_injective h)

private theorem normalizerAction_restricted (P B D : Subgroup G)
    (hDB : D ≤ B) (hDP : D ≤ P) (hBP : B ≤ normalizer (P : Set G)) (d : D) :
    P.normalizerMonoidHom (inclusion hBP (inclusion hDB d)) =
      MulAut.conj (inclusion hDP d) := by
  apply MulEquiv.ext
  intro x
  apply Subtype.ext
  rfl

private theorem reducedEndpointAction_reduced (i : Fin 2)
    (b : commonBorel L (reducedSylow L S)) :
    reducedEndpointAction h i (inclusion (reduced_commonBorel_le h) b) =
      MulAut.conj (inclusion (commonBorel_le_parabolic i) b) :=
  normalizerAction_restricted _ _ _ (reduced_commonBorel_le h)
    (commonBorel_le_parabolic i)
    ((commonBorel_le_parabolic i).trans (parabolic_normalizes_reduced h i)) b

theorem completionAction_reduced (b : commonBorel L (reducedSylow L S)) :
    completionAction h c hk (inclusion (reduced_commonBorel_le h) b) =
      MulAut.conj (c.middle b) := by
  apply CompletionAction.completionAction_eq_conj (reducedOverlapAction h) c hk
    (inclusion (reduced_commonBorel_le h) b) b
  · intro x
    rw [reducedOverlapAction_left, reducedEndpointAction_reduced]
    rfl
  · intro x
    rw [reducedOverlapAction_right, reducedEndpointAction_reduced]
    rfl

@[expose] def completionEndpoint (i : Fin 2) :
    parabolic L (reducedSylow L S) i →* X :=
  match i with
  | 0 => c.left
  | 1 => c.right

theorem completionEndpoint_injective (i : Fin 2) :
    Function.Injective (completionEndpoint c i) := by
  fin_cases i
  · exact c.left_injective
  · exact c.right_injective

theorem completionEndpoint_borel (i : Fin 2)
    (b : commonBorel L (reducedSylow L S)) :
    completionEndpoint c i (inclusion (commonBorel_le_parabolic i) b) = c.middle b := by
  fin_cases i
  · rfl
  · exact (DFunLike.congr_fun c.compatible b).symm

theorem completionAction_endpoint (i : Fin 2) (b : commonBorel L S)
    (x : parabolic L (reducedSylow L S) i) :
    completionAction h c hk b (completionEndpoint c i x) =
      completionEndpoint c i (reducedEndpointAction h i b x) := by
  fin_cases i
  · exact completionAction_left h c hk b x
  · exact completionAction_right h c hk b x

theorem completionAction_endpoint_range (i : Fin 2) (b : commonBorel L S) :
    (completionEndpoint c i).range.map (completionAction h c hk b).toMonoidHom =
      (completionEndpoint c i).range := by
  ext y
  constructor
  · rintro ⟨_, ⟨x,rfl⟩,rfl⟩
    exact ⟨reducedEndpointAction h i b x, (completionAction_endpoint h c hk i b x).symm⟩
  · rintro ⟨x,rfl⟩
    refine ⟨completionEndpoint c i ((reducedEndpointAction h i b).symm x),
      ⟨_,rfl⟩,?_⟩
    change completionAction h c hk b
      (completionEndpoint c i ((reducedEndpointAction h i b).symm x)) = _
    rw [completionAction_endpoint, MulEquiv.apply_symm_apply]

variable (hoverlap : c.left.range ⊓ c.right.range = c.middle.range)
  (hnormalizer : ∀ i, normalizer ((completionEndpoint c i).range : Set X) =
    (completionEndpoint c i).range)

include h hk hoverlap hnormalizer

theorem completionAction_mem_inner_iff (b : commonBorel L S) :
    completionAction h c hk b ∈ (MulAut.conj : X →* MulAut X).range ↔
      (b : G) ∈ commonBorel L (reducedSylow L S) := by
  have hi := CompletionAction.mem_inner_iff c (completionAction h c hk)
    (completionAction_injective h c hk) (inclusion (reduced_commonBorel_le h))
    (completionAction_reduced h c hk) hoverlap (hnormalizer 0) (hnormalizer 1)
    (completionAction_endpoint_range h c hk 0) (completionAction_endpoint_range h c hk 1) b
  rw [inclusion_range] at hi
  exact hi

theorem completion_center_eq_bot : center X = ⊥ :=
  CompletionAction.center_eq_bot c (completionAction h c hk)
    (completionAction_injective h c hk) (inclusion (reduced_commonBorel_le h))
    (completionAction_reduced h c hk) hoverlap (hnormalizer 0) (hnormalizer 1)
    (inclusion_injective _)

@[expose] def innerEndpoint (i : Fin 2) : Subgroup (MulAut X) :=
  (completionEndpoint c i).range.map MulAut.conj

theorem completionAction_mem_innerEndpoint_iff (i : Fin 2) (b : commonBorel L S) :
    completionAction h c hk b ∈ innerEndpoint c i ↔
      (b : G) ∈ commonBorel L (reducedSylow L S) := by
  constructor
  · rintro ⟨x,_,hx⟩
    exact (completionAction_mem_inner_iff h c hk hoverlap hnormalizer b).mp ⟨x,hx⟩
  · intro hb
    let d : commonBorel L (reducedSylow L S) := ⟨b,hb⟩
    refine ⟨c.middle d,?_,(completionAction_reduced h c hk d).symm⟩
    exact ⟨inclusion (commonBorel_le_parabolic i) d, completionEndpoint_borel c i d⟩

@[expose] def innerEndpointEquiv (i : Fin 2) :
    parabolic L (reducedSylow L S) i ≃* innerEndpoint c i :=
  (MonoidHom.ofInjective (completionEndpoint_injective c i)).trans
    ((completionEndpoint c i).range.equivMapOfInjective MulAut.conj
      (Theory.GroupTheory.conj_injective_of_center_eq_bot
        (completion_center_eq_bot h c hk hoverlap hnormalizer)))

theorem innerEndpointEquiv_apply (i : Fin 2) (x : parabolic L (reducedSylow L S) i) :
    (innerEndpointEquiv h c hk hoverlap hnormalizer i x : MulAut X) =
      MulAut.conj (completionEndpoint c i x) := rfl

omit h hk hoverlap hnormalizer in
private theorem conj_automorphism (a : MulAut X) (x : X) :
    MulAut.conj (a x) = a * MulAut.conj x * a⁻¹ := by
  apply MulEquiv.ext
  intro y
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
    map_mul, map_inv, a.apply_symm_apply]

/-- Pump the marked reduced completion up to the original endpoints. The
overlap map is constructed by quotient descent, and every gluing condition
follows from generation, self-normalizing endpoints and source faithfulness. -/
theorem exists_original_automorphism_iso :
    ∃ E : RankTwoAmalgam.Iso (originalAmalgam L S)
      (RankTwoAmalgam.ofSubgroups
        (innerEndpoint c 0 ⊔ (completionAction h c hk).range)
        (completionAction h c hk).range
        (innerEndpoint c 1 ⊔ (completionAction h c hk).range)
        le_sup_right le_sup_right),
      E.middle = MonoidHom.ofInjective (completionAction_injective h c hk) ∧
      (∀ n : parabolic L (reducedSylow L S) 0,
        (E.left (inclusion (reduced_parabolic_le h 0) n) : MulAut X) =
          MulAut.conj (c.left n)) ∧
      (∀ n : parabolic L (reducedSylow L S) 1,
        (E.right (inclusion (reduced_parabolic_le h 1) n) : MulAut X) =
          MulAut.conj (c.right n)) := by
  have hagree (i : Fin 2) (b : commonBorel L (reducedSylow L S)) :
      (innerEndpointEquiv h c hk hoverlap hnormalizer i
        (inclusion (commonBorel_le_parabolic i) b) : MulAut X) =
        completionAction h c hk (inclusion (reduced_commonBorel_le h) b) := by
    rw [innerEndpointEquiv_apply, completionEndpoint_borel, completionAction_reduced]
  have hconj (i : Fin 2) (b : commonBorel L S)
      (n : parabolic L (reducedSylow L S) i) :
      (innerEndpointEquiv h c hk hoverlap hnormalizer i
        (reducedEndpointAction h i b n) : MulAut X) =
        completionAction h c hk b * innerEndpointEquiv h c hk hoverlap hnormalizer i n *
          (completionAction h c hk b)⁻¹ := by
    rw [innerEndpointEquiv_apply, innerEndpointEquiv_apply, ← completionAction_endpoint]
    exact conj_automorphism _ _
  obtain ⟨E,hE,hleft,hright⟩ := exists_original_amalgam_iso h (innerEndpoint c)
    (innerEndpointEquiv h c hk hoverlap hnormalizer)
    (completionAction h c hk) (completionAction_injective h c hk)
    (completionAction_mem_innerEndpoint_iff h c hk hoverlap hnormalizer) hagree hconj
  exact ⟨E,hE,fun n => (hleft n).trans (innerEndpointEquiv_apply h c hk hoverlap hnormalizer 0 n),
    fun n => (hright n).trans (innerEndpointEquiv_apply h c hk hoverlap hnormalizer 1 n)⟩

/-- The actual restored ambient subgroup of Aut(X), including every inner
automorphism of the reduced completion. -/
@[expose] def automorphismExtension : Subgroup (MulAut X) :=
  MulAut.innerSubgroup X ⊔ (completionAction h c hk).range

omit hoverlap hnormalizer in
theorem inner_le_automorphismExtension : MulAut.innerSubgroup X ≤
    automorphismExtension h c hk := le_sup_left

theorem original_outer_index :
    (MulAut.innerSubgroup X).relIndex (automorphismExtension h c hk) =
      (commonBorel L (reducedSylow L S)).relIndex (commonBorel L S) := by
  rw [automorphismExtension, relIndex_sup_left, ← index_comap]
  congr 1
  ext b
  exact completionAction_mem_inner_iff h c hk hoverlap hnormalizer b

/-- The restored outer quotient has precisely the original Borel extension
index; in particular it is a two-group. -/
theorem automorphismExtension_quotient_isPGroup :
    IsPGroup 2 (automorphismExtension h c hk ⧸
      (MulAut.innerSubgroup X).subgroupOf (automorphismExtension h c hk)) := by
  let := reduced_borel_normal h
  let := h.finite_parabolic 0
  let : Finite (commonBorel L S) := Finite.of_injective
    (inclusion (commonBorel_le_parabolic 0)) (inclusion_injective _)
  obtain ⟨n,hn⟩ := (borel_extension_isPGroup h).exists_card_eq
  apply IsPGroup.of_card (n := n)
  change (MulAut.innerSubgroup X).relIndex (automorphismExtension h c hk) = _
  rw [original_outer_index h c hk hoverlap hnormalizer]
  exact hn

theorem original_sylow_card_via_outer :
    Nat.card S = Nat.card (reducedSylow L S) *
      (MulAut.innerSubgroup X).relIndex (automorphismExtension h c hk) := by
  rw [original_outer_index h c hk hoverlap hnormalizer]
  exact original_sylow_card h

omit h hk hoverlap hnormalizer in
private theorem local_image_of_restriction {P P₀ K : Subgroup G}
    (h₀ : P₀ ≤ P) (hK : K ≤ P₀)
    (f : P →* MulAut X) (g : P₀ →* X)
    (hf : ∀ x : P₀, f (inclusion h₀ x) = MulAut.conj (g x)) :
    (K.subgroupOf P).map f = ((K.subgroupOf P₀).map g).map MulAut.conj := by
  rw [map_map]
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    refine ⟨⟨x,hK hx⟩,hx,?_⟩
    exact (hf ⟨x,hK hx⟩).symm
  · rintro ⟨x,hx,rfl⟩
    exact ⟨inclusion h₀ x,hx,hf x⟩

/-- The local-factor marking in a reduced endpoint supplies the marking in
the original endpoint through the constructed map. No original embedding
or original core equality is assumed. -/
theorem exists_original_endpoint_local_marking (i : Fin 2) (K : Subgroup X)
    (hK : ((L i).subgroupOf (parabolic L (reducedSylow L S) i)).map
      (completionEndpoint c i) = K) :
    ∃ f : parabolic L S i →* MulAut X, Function.Injective f ∧
      ((L i).subgroupOf (parabolic L S i)).map f = K.map MulAut.conj := by
  obtain ⟨E,_,hleft,hright⟩ := exists_original_automorphism_iso h c hk hoverlap hnormalizer
  fin_cases i
  · let f := (innerEndpoint c 0 ⊔ (completionAction h c hk).range).subtype.comp E.left.toMonoidHom
    refine ⟨f, Subtype.val_injective.comp E.left.injective, ?_⟩
    have hh := local_image_of_restriction (reduced_parabolic_le h 0)
      (show L 0 ≤ parabolic L (reducedSylow L S) 0 from le_sup_left.trans le_sup_left)
      f c.left hleft
    exact hh.trans (congrArg (Subgroup.map MulAut.conj) hK)
  · let f := (innerEndpoint c 1 ⊔ (completionAction h c hk).range).subtype.comp E.right.toMonoidHom
    refine ⟨f, Subtype.val_injective.comp E.right.injective, ?_⟩
    have hh := local_image_of_restriction (reduced_parabolic_le h 1)
      (show L 1 ≤ parabolic L (reducedSylow L S) 1 from le_sup_left.trans le_sup_left)
      f c.right hright
    exact hh.trans (congrArg (Subgroup.map MulAut.conj) hK)

end CFSG.Quasithin.ChapterF.Source.DGS85.OriginalExtension
