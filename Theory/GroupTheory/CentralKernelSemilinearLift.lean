module
public import Theory.GroupTheory.OddSemilinearSubgroupLift
public import Theory.GroupTheory.SylowCentralJoinIndex

/-!
# Semilinear recognition from a central projective kernel

Let a finite group H have a normal constituent L and odd complement E,
with a prescribed projective homomorphism on L having central two-kernel.
An equivalence from L to an actual invariant subgroup D of X yields a
faithful map into X semidirect E if the transported projective map is
coefficient-compatible and E fixes a Sylow two-subgroup of D. The normal
core M has no normal subgroup of index two, and the join of M with the
projective kernel has index dividing two. The resulting map preserves
all linear and complement coordinates and their exact subgroup images.

Pull the supplied model Sylow back through the equivalence. The normal
two-kernel lies in this Sylow, so the central-join index theorem proves
that it and M generate L. Transfer the projective kernel through the
actual equivalence, then apply the odd semilinear subgroup lift. Surjectivity
of the equivalence gives the exact linear image; the complement maps to
all pure actors. No identification with a previously chosen source Sylow
and no additional matrix action instance is required.

Source: Alperin--Brauer--Gorenstein II.3 Proposition 3, article pp27–28.
This common assembly step applies to both actual determinant models.
-/

namespace Subgroup
public theorem exists_injective_semilinear_model_of_central_kernel
    {H X Q : Type*} [Group H] [Finite H] [Group X] [Group Q]
    (D : Subgroup X) [Finite D]
    (L E : Subgroup H) [L.Normal] (hcomp : L.IsComplement' E)
    (hodd : Odd (Nat.card E)) (α : E →* MulAut X)
    (hD : ∀ a x, α a x ∈ D ↔ x ∈ D) (β : E →* MulAut Q)
    (eL : L ≃* D) (φ : L →* Q) (hφtwo : IsPGroup 2 φ.ker)
    (hφcentral : φ.ker.map L.subtype ≤ center H)
    (hq : ∀ (a : E) (x y : D), y.val = α a x.val →
      φ (eL.symm y) = β a (φ (eL.symm x)))
    (f : H →* Q ⋊[β] E)
    (hfL : ∀ l : L, f l = SemidirectProduct.inl (φ l))
    (hfE : ∀ e : E, f e = SemidirectProduct.inr e)
    (T : Sylow 2 D) (hT : ∀ (a : E) (t : T), α a t.val.val = t.val.val)
    (M : Subgroup L) [M.Normal]
    (hno : ∀ N : Subgroup M, N.Normal → N.index ≠ 2)
    (hindex : (φ.ker ⊔ M).index ∣ 2) :
    ∃ F : H →* X ⋊[α] E, Function.Injective F ∧
      (∀ l : L, F l = SemidirectProduct.inl (eL l).val) ∧
      (∀ e : E, F e = SemidirectProduct.inr e) ∧
      L.map F = D.map SemidirectProduct.inl ∧
      E.map F = (SemidirectProduct.inr : E →* X ⋊[α] E).range := by
  classical
  let q := φ.comp eL.symm.toMonoidHom
  have hqtwo : IsPGroup 2 q.ker := by
    let j : q.ker →* φ.ker := (eL.symm.toMonoidHom.comp q.ker.subtype).codRestrict _
      (fun x => x.property)
    exact hφtwo.of_injective j (fun x y h =>
      Subtype.ext (eL.symm.injective (congrArg Subtype.val h)))
  have hk : q.ker.comap eL.toMonoidHom = φ.ker := by
    ext x
    change φ (eL.symm (eL x)) = 1 ↔ φ x = 1
    rw [eL.symm_apply_apply]
  let S := T.mapSurjective (f := eL.symm.toMonoidHom) eL.symm.surjective
  have hS : (S : Subgroup L) = (T : Subgroup D).comap eL.toMonoidHom := by
    ext x
    constructor
    · rintro ⟨y, hy, h⟩
      change eL.symm y = x at h
      change eL x ∈ (T : Subgroup D)
      rw [← h, eL.apply_symm_apply]
      exact hy
    · intro hx
      exact ⟨eL x, hx, eL.symm_apply_apply x⟩
  have hgen : M ⊔ (T : Subgroup D).comap eL.toMonoidHom = ⊤ := by
    rw [← hS, sup_comm]
    exact (S.sup_normal_eq_top_and_join_index φ.ker M
      (hφtwo.le_sylow_of_normal S) hindex).1
  obtain ⟨F, hF, hFL, hFE⟩ := exists_injective_semilinear_subgroup_lift_of_odd_complement
    D L E hcomp hodd α hD β eL (MonoidHom.id E) Function.injective_id
    q hq hqtwo (by rw [hk]; exact hφcentral) f
    (fun l => by simpa only [q, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      eL.symm_apply_apply] using hfL l) hfE T hT M hno hgen
  refine ⟨F, hF, hFL, hFE, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨(eL ⟨l, hl⟩).val, (eL ⟨l, hl⟩).property, (hFL ⟨l, hl⟩).symm⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨eL.symm ⟨d, hd⟩, (eL.symm ⟨d, hd⟩).property,
        (hFL _).trans (congrArg (fun z : D => SemidirectProduct.inl z.val)
          (eL.apply_symm_apply _))⟩
  · ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, (hFE ⟨a, ha⟩).symm⟩
    · rintro ⟨a, rfl⟩
      exact ⟨a.val, a.property, hFE a⟩
end Subgroup
