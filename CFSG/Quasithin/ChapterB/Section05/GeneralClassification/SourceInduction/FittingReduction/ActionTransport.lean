module
public import CFSG.Quasithin.ChapterB.Section05.GeneralClassification.SourceInduction.FittingReduction.Configuration
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceImplication.ExtensionConsequences.Homogeneity

/-!
# Transport of all four-dimensional factor clauses

Equivariant group and linear identifications preserve the full B.4.8(3)
output, including its offender family, ratio and involution fixed spaces.
This is used to move a recursively obtained factor into the original fixed
quotient in B.5.8. No new B.4.8 implication is assumed.

The pullback and weight arguments specialize the existing transport proofs in
ExceptionalExtension/NonsplitCase/Transport and ThreeCovers/Offenders.
Source: Aschbacher–Smith, combined 1 March 2004 manuscript, pp.91 and 106.
-/

@[expose] public section
open Subgroup Representation Representation.BinaryOffender
open CFSG.Quasithin.ChapterB.QuasisimpleSource
open CFSG.Quasithin.ChapterB.QuasisimpleSource.ExtensionConsequences
namespace CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
section
variable {D E U T : Type*} [Group D] [Group E]
  [AddCommGroup U] [Module (ZMod 2) U] [AddCommGroup T] [Module (ZMod 2) T]
  {σ : Representation (ZMod 2) D U} {τ : Representation (ZMod 2) E T}

private def pullback (e : ActionEquiv σ τ) (N : Subrepresentation τ) : Subrepresentation σ where
  toSubmodule := N.toSubmodule.comap e.linearEquiv.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change e.linearEquiv (σ g v) ∈ N
    rw [e.intertwines]
    exact N.apply_mem_toSubmodule _ hv

private theorem indecomposable_transport (e : ActionEquiv σ τ) (h : IsIndecomposable σ) :
    IsIndecomposable τ := by
  let := h.1
  refine ⟨e.linearEquiv.injective.nontrivial, fun A B hc => ?_⟩
  have hc' : IsCompl (pullback e A).toSubmodule (pullback e B).toSubmodule :=
    (Submodule.orderIsoMapComap e.linearEquiv).symm.isCompl hc
  have hz (N : Subrepresentation τ) (hn : pullback e N = ⊥) : N = ⊥ := by
    apply Subrepresentation.toSubmodule_injective
    apply bot_unique
    intro v hv
    obtain ⟨x,rfl⟩ := e.linearEquiv.surjective v
    have hx : x ∈ pullback e N := hv
    rw [hn] at hx
    simpa using congrArg e.linearEquiv (show x = 0 from hx)
  exact (h.2 _ _ hc').imp (hz A) (hz B)

private noncomputable def pullbackEquiv (e : ActionEquiv σ τ) (N : Subrepresentation τ) :
    ActionEquiv (pullback e N).toRepresentation N.toRepresentation where
  groupEquiv := e.groupEquiv
  linearEquiv :=
    { toFun := fun x => ⟨e.linearEquiv x,x.property⟩
      invFun := fun y => ⟨e.linearEquiv.symm y,by
        change e.linearEquiv (e.linearEquiv.symm y) ∈ N
        simp only [e.linearEquiv.apply_symm_apply]; exact y.property⟩
      left_inv := fun x => Subtype.ext (e.linearEquiv.symm_apply_apply x)
      right_inv := fun y => Subtype.ext (e.linearEquiv.apply_symm_apply y)
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun a x => Subtype.ext (map_smul _ _ _) }
  intertwines g x := Subtype.ext (e.intertwines g x)

private theorem pullback_moved (e : ActionEquiv σ τ) (N : Subrepresentation τ)
    (hn : N.toSubmodule = moved τ ⊤) :
    (pullback e N).toSubmodule = moved σ ⊤ := by
  apply (Submodule.orderIsoMapComap e.linearEquiv).injective
  change ((N.toSubmodule.comap e.linearEquiv.toLinearMap).map e.linearEquiv.toLinearMap) = _
  rw [Submodule.map_comap_eq_of_surjective e.linearEquiv.surjective, hn]
  have hh := subspaceCommutator_map_embedding τ σ e.groupEquiv.symm.toMonoidHom
    e.linearEquiv.toLinearMap (fun g v => by
      simpa using (e.intertwines (e.groupEquiv.symm g) v).symm) ⊤ ⊤
  change moved τ ⊤ = (moved σ ⊤).map e.linearEquiv.toLinearMap
  simpa only [Submodule.map_top, LinearEquiv.range, Subgroup.map_top_of_surjective e.groupEquiv.symm.toMonoidHom
    e.groupEquiv.symm.surjective] using hh

end
section
variable {G H V W : Type*} [Group G] [Group H]
  [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]
  {ρ : Representation (ZMod 2) G V} {σ : Representation (ZMod 2) H W}

private theorem elementary_map (e : G ≃* H) {A : Subgroup G}
    (hA : IsElementaryTwo A) : IsElementaryTwo (A.map e.toMonoidHom) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsElementaryAbelian 2 A := hA.2
  refine ⟨?_, IsElementaryAbelian.map _⟩
  intro h
  apply hA.1
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  simpa only [Subgroup.map_bot] using h

private theorem weight_map (e : ActionEquiv ρ σ) (A : Subgroup G) :
    weight σ (A.map e.groupEquiv.toMonoidHom) = weight ρ A := by
  unfold weight
  rw [rank_map_injective _ e.groupEquiv.injective,
    ← fixedSpace_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
    LinearEquiv.finrank_map_eq]

private theorem best_map (e : ActionEquiv ρ σ) {A : Subgroup G}
    (hA : IsBestOffender ρ A) : IsBestOffender σ (A.map e.groupEquiv.toMonoidHom) := by
  refine ⟨elementary_map e.groupEquiv hA.1, ?_⟩
  intro B hB
  have hm : (B.map e.groupEquiv.symm.toMonoidHom).map e.groupEquiv.toMonoidHom = B := by
    rw [map_map]; simp
  have hle : B.map e.groupEquiv.symm.toMonoidHom ≤ A := by
    have h := Subgroup.map_mono (f := e.groupEquiv.symm.toMonoidHom) hB
    simpa [map_map] using h
  rw [← hm, weight_map, weight_map]
  exact hA.2 _ hle

private theorem quadratic_map (e : ActionEquiv ρ σ) {A : Subgroup G}
    (hA : IsQuadratic ρ A) : IsQuadratic σ (A.map e.groupEquiv.toMonoidHom) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ w
  obtain ⟨v, rfl⟩ := e.linearEquiv.surjective w
  have h := congrArg e.linearEquiv (hA a ha b hb v)
  change σ (e.groupEquiv a) (σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v) =
    σ (e.groupEquiv b) (e.linearEquiv v) - e.linearEquiv v
  simpa only [e.intertwines, map_sub] using h

private theorem ratio_le (e : ActionEquiv ρ σ) : quadraticRatio σ ≤ quadraticRatio ρ := by
  apply le_iInf
  intro A
  apply le_iInf
  rintro ⟨hA, hq⟩
  have hr : actionRatio σ (A.map e.groupEquiv.toMonoidHom) = actionRatio ρ A := by
    unfold actionRatio
    rw [← fixedCodim_map_equivariant ρ σ _ e.linearEquiv e.intertwines,
      rank_map_injective _ e.groupEquiv.injective]
  exact iInf_le_of_le (A.map e.groupEquiv.toMonoidHom)
    (iInf_le_of_le ⟨elementary_map e.groupEquiv hA, quadratic_map e hq⟩ hr.le)

private theorem ratio_eq (e : ActionEquiv ρ σ) : quadraticRatio ρ = quadraticRatio σ :=
  le_antisymm (ratio_le (actionSymm e)) (ratio_le e)



private theorem moved_map (e : ActionEquiv ρ σ) (A : Subgroup G) :
    (moved ρ A).map e.linearEquiv.toLinearMap = moved σ (A.map e.groupEquiv.toMonoidHom) := by
  have hh := subspaceCommutator_map_embedding σ ρ e.groupEquiv.symm.toMonoidHom
    e.linearEquiv.toLinearMap (fun g v => by
      simpa using (e.intertwines (e.groupEquiv.symm g) v).symm)
    (A.map e.groupEquiv.toMonoidHom) ⊤
  simpa [Submodule.map_top, LinearEquiv.range, Subgroup.map_map] using hh.symm

/-- Transport every clause of the actual four-dimensional source action.
The offender and involution statements retain the transported natural marking. -/
theorem fourDimensional_transport (e : ActionEquiv ρ σ) (q : FourDimensionalSource σ) :
    Nonempty (FourDimensionalSource ρ) := by
  let N := pullback e q.space
  let p := pullbackEquiv e q.space
  let n : ActionEquiv N.toRepresentation (linearNatural BinaryField.two 3) :=
    ⟨p.groupEquiv.trans q.natural.groupEquiv,p.linearEquiv.trans q.natural.linearEquiv,
      fun g v => (congrArg q.natural.linearEquiv (p.intertwines g v)).trans
        (q.natural.intertwines _ _)⟩
  have hn := pullback_moved e q.space q.space_eq
  have hi := indecomposable_transport (actionSymm e) q.indecomposable
  refine ⟨⟨e.linearEquiv.finrank_eq.trans q.dimension,hi,N,hn,n,?_,
    (ratio_eq e).trans q.ratio,?_⟩⟩
  · intro A
    have hb : IsBestOffender ρ A ↔ IsBestOffender σ (A.map e.groupEquiv.toMonoidHom) := by
      constructor
      · exact best_map e
      · intro h
        have hh := best_map (actionSymm e) h
        simpa [actionSymm, Subgroup.map_map] using hh
    rw [hb, q.offenders]
    simp only [Subgroup.map_map]
    rfl
  · intro a ha
    have hat : orderOf (e.groupEquiv a) = 2 := (e.groupEquiv.orderOf_eq a).trans ha
    obtain ⟨hm,hd,hc⟩ := q.involutions (e.groupEquiv a) hat
    have hf := fixedSpace_map_equivariant ρ σ e.groupEquiv.toMonoidHom
      e.linearEquiv e.intertwines (zpowers a)
    rw [MonoidHom.map_zpowers] at hf
    change (fixedSpace ρ (zpowers a)).map e.linearEquiv.toLinearMap =
      fixedSpace σ (zpowers (e.groupEquiv a)) at hf
    refine ⟨?_,?_,?_⟩
    · apply Submodule.map_injective_of_injective e.linearEquiv.injective
      rw [moved_map,MonoidHom.map_zpowers]
      change moved σ (zpowers (e.groupEquiv a)) = _
      exact hm.trans hf.symm
    · rw [← hf, LinearEquiv.finrank_map_eq] at hd
      exact hd
    · intro v hv
      change e.linearEquiv v ∈ q.space
      apply hc
      rw [← hf]
      exact ⟨v,hv,rfl⟩

end
end CFSG.Quasithin.ChapterB.SourceInduction.FittingReduction
