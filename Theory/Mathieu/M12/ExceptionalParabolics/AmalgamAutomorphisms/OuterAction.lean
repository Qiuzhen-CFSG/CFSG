module

public import Theory.Mathieu.M12.ExceptionalParabolics
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.Automorphisms
public import Theory.Mathieu.M12.ExceptionalParabolics.Extension.SecondParabolic.InnerBounds

/-!
# The outer M₁₂ overlap acts faithfully on the inner amalgam

The marked inner-model embedding pulls the two outer parabolics and their
overlap back to the original M₁₂ subgroups. Thus conjugation by every outer
overlap element preserves all three inner subgroups, and the existing
ambient-isomorphism transport supplies both commuting inclusion squares.
The two inner parabolics generate M₁₂, so their restrictions determine the
ambient automorphism. The verified full-automorphism identification makes
this action faithful.

The action formulas retain the literal degree-24 inner-model embedding.
They supply the concrete outer action in Goldschmidt, Automorphisms of
trivalent graphs, §3.8, and the M₁₂/Aut(M₁₂) branch of Aschbacher--Smith
F.1.12, printed p.263. No automorphism count is assumed here.
-/

@[expose] public section
noncomputable section

namespace Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms
open Subgroup Theory.GroupTheory
open M12ExceptionalExtension (Carrier innerModel automorphismEquiv)

private theorem embedding_automorphism (g : Carrier) (x : M12) :
    innerModel.embedding (automorphismEquiv g x) =
      g * innerModel.embedding x * g⁻¹ := by
  apply automorphismEquiv.injective
  simp only [map_mul, map_inv, M12ExceptionalExtension.automorphismEquiv_embedding]
  apply MulEquiv.ext
  intro y
  simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply,
    map_mul, map_inv, MulEquiv.apply_symm_apply]

private theorem map_comap_eq_of_mem (K : Subgroup Carrier) (g : Carrier) (hg : g ∈ K) :
    (K.comap innerModel.embedding).map (automorphismEquiv g).toMonoidHom =
      K.comap innerModel.embedding := by
  have hle : (K.comap innerModel.embedding).map (automorphismEquiv g).toMonoidHom ≤
      K.comap innerModel.embedding := by
    rintro _ ⟨x, hx, rfl⟩
    change innerModel.embedding (automorphismEquiv g x) ∈ K
    rw [embedding_automorphism]
    exact K.mul_mem (K.mul_mem hg hx) (K.inv_mem hg)
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective (automorphismEquiv g).injective]

/-- The actual outer overlap preserves the original first inner parabolic. -/
theorem outer_first_map (s : M12ExceptionalExtension.overlap) :
    firstParabolic.map (automorphismEquiv s.val).toMonoidHom = firstParabolic := by
  rw [← M12ExceptionalExtension.SecondCoordinates.comap_firstParabolic innerModel]
  exact map_comap_eq_of_mem _ _ s.property.1

/-- The actual outer overlap preserves the original second inner parabolic. -/
theorem outer_second_map (s : M12ExceptionalExtension.overlap) :
    secondParabolic.map (automorphismEquiv s.val).toMonoidHom = secondParabolic := by
  rw [← M12ExceptionalExtension.SecondCoordinates.comap_secondParabolic innerModel]
  exact map_comap_eq_of_mem _ _ s.property.2

/-- The original inner overlap is invariant under the entire outer overlap. -/
theorem outer_middle_map (s : M12ExceptionalExtension.overlap) :
    sylowCandidate.map (automorphismEquiv s.val).toMonoidHom = sylowCandidate := by
  rw [← M12ExceptionalExtension.SecondCoordinates.comap_overlap innerModel]
  exact map_comap_eq_of_mem _ _ s.property

/-- Conjugation by the literal outer overlap on the original inner inclusion amalgam. -/
def outerOverlapAction (s : M12ExceptionalExtension.overlap) :
    RankTwoAmalgam.Iso amalgam amalgam :=
  RankTwoAmalgam.ofSubgroupsIso (automorphismEquiv s.val)
    inf_le_left inf_le_right inf_le_left inf_le_right
    (outer_first_map s) (outer_middle_map s) (outer_second_map s)

@[simp] theorem outerOverlapAction_left_apply
    (s : M12ExceptionalExtension.overlap) (x : firstParabolic) :
    ((outerOverlapAction s).left x : M12) = automorphismEquiv s.val x := rfl

@[simp] theorem outerOverlapAction_middle_apply
    (s : M12ExceptionalExtension.overlap) (x : sylowCandidate) :
    ((outerOverlapAction s).middle x : M12) = automorphismEquiv s.val x := rfl

@[simp] theorem outerOverlapAction_right_apply
    (s : M12ExceptionalExtension.overlap) (x : secondParabolic) :
    ((outerOverlapAction s).right x : M12) = automorphismEquiv s.val x := rfl

/-- On the first endpoint the action is literal conjugation after the marked embedding. -/
theorem embedding_outerOverlapAction_left
    (s : M12ExceptionalExtension.overlap) (x : firstParabolic) :
    innerModel.embedding ((outerOverlapAction s).left x : M12) =
      s.val * innerModel.embedding x * s.val⁻¹ :=
  embedding_automorphism s.val x

/-- The overlap action uses the same literal conjugation and embedding. -/
theorem embedding_outerOverlapAction_middle
    (s : M12ExceptionalExtension.overlap) (x : sylowCandidate) :
    innerModel.embedding ((outerOverlapAction s).middle x : M12) =
      s.val * innerModel.embedding x * s.val⁻¹ :=
  embedding_automorphism s.val x

/-- On the second endpoint the action is literal conjugation after the marked embedding. -/
theorem embedding_outerOverlapAction_right
    (s : M12ExceptionalExtension.overlap) (x : secondParabolic) :
    innerModel.embedding ((outerOverlapAction s).right x : M12) =
      s.val * innerModel.embedding x * s.val⁻¹ :=
  embedding_automorphism s.val x

/-- The actual outer overlap acts faithfully on the original marked M₁₂ amalgam. -/
theorem outerOverlapAction_injective : Function.Injective outerOverlapAction := by
  intro s t h
  apply Subtype.ext
  apply automorphismEquiv.injective
  have hL (x : firstParabolic) : automorphismEquiv s.val x = automorphismEquiv t.val x :=
    congrArg (fun e : RankTwoAmalgam.Iso amalgam amalgam => (e.left x : M12)) h
  have hR (x : secondParabolic) : automorphismEquiv s.val x = automorphismEquiv t.val x :=
    congrArg (fun e : RankTwoAmalgam.Iso amalgam amalgam => (e.right x : M12)) h
  have he : firstParabolic ⊔ secondParabolic ≤
      (automorphismEquiv s.val).toMonoidHom.eqLocus
        (automorphismEquiv t.val).toMonoidHom :=
    sup_le (fun x hx => hL ⟨x, hx⟩) (fun x hx => hR ⟨x, hx⟩)
  rw [ValueBoundParabolics.parabolic_sup_eq_top] at he
  exact MulEquiv.ext (fun x => he (Subgroup.mem_top x))

/-- The original inner overlap retains its actual embedding into the outer overlap. -/
def innerOverlapEmbedding : sylowCandidate →* M12ExceptionalExtension.overlap :=
  (innerModel.embedding.comp sylowCandidate.subtype).codRestrict _ (by
    intro x
    change (x : M12) ∈ M12ExceptionalExtension.overlap.comap innerModel.embedding
    rw [M12ExceptionalExtension.SecondCoordinates.comap_overlap innerModel]
    exact x.property)

theorem innerOverlapEmbedding_injective : Function.Injective innerOverlapEmbedding := by
  intro x y h
  apply Subtype.ext
  apply innerModel.embedding_injective
  exact congrArg (fun z : M12ExceptionalExtension.overlap => (z : Carrier)) h

/-- The outer action extends the original first-endpoint inner conjugation. -/
theorem outerOverlapAction_inner_left (s : sylowCandidate) (x : firstParabolic) :
    ((outerOverlapAction (innerOverlapEmbedding s)).left x : M12) =
      (s : M12) * x * (s : M12)⁻¹ := by
  change automorphismEquiv (innerModel.embedding s) x = _
  rw [M12ExceptionalExtension.automorphismEquiv_embedding]
  rfl

/-- The outer action extends inner conjugation on the original overlap. -/
theorem outerOverlapAction_inner_middle (s x : sylowCandidate) :
    ((outerOverlapAction (innerOverlapEmbedding s)).middle x : M12) =
      (s : M12) * x * (s : M12)⁻¹ := by
  change automorphismEquiv (innerModel.embedding s) x = _
  rw [M12ExceptionalExtension.automorphismEquiv_embedding]
  rfl

/-- The outer action extends the original second-endpoint inner conjugation. -/
theorem outerOverlapAction_inner_right (s : sylowCandidate) (x : secondParabolic) :
    ((outerOverlapAction (innerOverlapEmbedding s)).right x : M12) =
      (s : M12) * x * (s : M12)⁻¹ := by
  change automorphismEquiv (innerModel.embedding s) x = _
  rw [M12ExceptionalExtension.automorphismEquiv_embedding]
  rfl

end Sporadic.Mathieu.M12SmallPair.ExceptionalParabolics.AmalgamAutomorphisms
