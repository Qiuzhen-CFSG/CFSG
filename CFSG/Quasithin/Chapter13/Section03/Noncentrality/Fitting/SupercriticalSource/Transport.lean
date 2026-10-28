module

public import CFSG.Quasithin.Chapter13.Section03.Noncentrality.Fitting.SupercriticalSource.Frattini

/-!
# The selected quaternion action on the residual Frattini quotient

The odd quotient of the two-residual is the literal selected subgroup of
`H / O₂(H)`. Its Frattini quotient inherits the original conjugation action.
The quaternion image of `T ∩ L⁺` therefore proves irreducibility for the
whole acting subgroup `T ∩ H`, as required in Lemma 13.3.14(d).
-/

public section

open Subgroup

namespace CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

@[expose] public noncomputable def residualFrattiniEquiv (H : Subgroup G) (D : Subgroup (Star H))
    (hp : Odd p) (hD : IsPGroup p D) :
    Chapter1.XiFrattiniQuotient (starResidual H D) ≃* D ⧸ frattini D :=
  QuotientGroup.congr _ _ (oddStarResidualCoreEquiv H D hp hD)
    (frattini_map_equiv _)

theorem residualFrattiniEquiv_mk (H : Subgroup G) (D : Subgroup (Star H))
    (hp : Odd p) (hD : IsPGroup p D) (v : starResidual H D) :
    residualFrattiniEquiv H D hp hD
      (QuotientGroup.mk' _ (QuotientGroup.mk' (pCore 2 (starResidual H D)) v)) =
    QuotientGroup.mk' (frattini D)
      (oddStarResidualCoreEquiv H D hp hD (QuotientGroup.mk' (pCore 2 (starResidual H D)) v)) := rfl

theorem residualFrattiniEquiv_equivariant
    (H : Subgroup G) (D : Subgroup (Star H)) [D.Normal]
    (hp : Odd p) (hD : IsPGroup p D) (S : Subgroup H)
    (hn : S ≤ normalizer (starResidual H D : Set H))
    (s : S) (v : Chapter1.XiFrattiniQuotient (starResidual H D)) :
    residualFrattiniEquiv H D hp hD (Chapter1.xiFrattiniAction S (starResidual H D) hn s v) =
      quotientAut (frattini D) (MulAut.conjNormal
        (QuotientGroup.mk' (pCore 2 H) (s : H))) (residualFrattiniEquiv H D hp hD v) := by
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ v
  obtain ⟨v, rfl⟩ := QuotientGroup.mk'_surjective _ v
  simp only [Chapter1.xiFrattiniAction, MonoidHom.comp_apply, quotientAut_apply_mk,
    residualFrattiniEquiv_mk]
  apply congrArg (QuotientGroup.mk' (frattini D))
  apply Subtype.ext
  change QuotientGroup.mk' (pCore 2 H) (s.val * v.val * s.val⁻¹) =
    QuotientGroup.mk' (pCore 2 H) s.val * QuotientGroup.mk' (pCore 2 H) v.val *
      (QuotientGroup.mk' (pCore 2 H) s.val)⁻¹
  simp only [map_mul, map_inv]

theorem residual_frattini_irreducible
    (T H Lplus : Subgroup G) (hLH : Lplus ≤ H)
    (D : Subgroup (Star H)) [D.Normal]
    (hp : Odd p) (hD : Chapter1.XiOddQuotient p D)
    (hQ : Nonempty (((T.subgroupOf Lplus).map
      ((MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH))) ≃*
        QuaternionGroup 2))
    (hn : T.subgroupOf H ≤ normalizer (starResidual H D : Set H))
    (A : Subgroup (Chapter1.XiFrattiniQuotient (starResidual H D)))
    (hA : ∀ s : T.subgroupOf H, ∀ v ∈ A,
      Chapter1.xiFrattiniAction (T.subgroupOf H) (starResidual H D) hn s v ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  let S := T.subgroupOf Lplus
  let a := (MulAut.conjNormal : Star H →* MulAut D).comp (starMap H Lplus hLH)
  let B := S.map a
  obtain ⟨e⟩ := hQ
  let f : QuaternionGroup 2 →* MulAut D := B.subtype.comp e.symm.toMonoidHom
  have hf : Function.Injective f := B.subtype_injective.comp e.symm.injective
  let E := residualFrattiniEquiv H D hp hD.isPGroup
  have hinv (g : QuaternionGroup 2) (v : D ⧸ frattini D)
      (hv : v ∈ A.map E.toMonoidHom) :
      quotientAut (frattini D) (f g) v ∈ A.map E.toMonoidHom := by
    obtain ⟨l, hl, hel⟩ := (e.symm g).property
    obtain ⟨v, hv, rfl⟩ := hv
    let s : T.subgroupOf H := ⟨⟨l, hLH l.property⟩, hl⟩
    have ha : f g = MulAut.conjNormal (QuotientGroup.mk' (pCore 2 H) (s : H)) := hel.symm
    rw [ha]
    change quotientAut (frattini D) (MulAut.conjNormal
      (QuotientGroup.mk' (pCore 2 H) (s : H)))
        (residualFrattiniEquiv H D hp hD.isPGroup v) ∈ A.map E.toMonoidHom
    rw [← residualFrattiniEquiv_equivariant H D hp hD.isPGroup (T.subgroupOf H) hn s v]
    exact mem_map_of_mem E.toMonoidHom (hA s v hv)
  rcases faithful_quaternion_frattini_irreducible hp hD f hf (A.map E.toMonoidHom) hinv with hz | ht
  · exact Or.inl ((A.map_eq_bot_iff_of_injective E.injective).mp hz)
  · right
    apply map_injective E.injective
    rw [map_top_of_surjective _ E.surjective]
    exact ht

end CFSG.Quasithin.Chapter13.Section03.Noncentrality.SupercriticalSource
