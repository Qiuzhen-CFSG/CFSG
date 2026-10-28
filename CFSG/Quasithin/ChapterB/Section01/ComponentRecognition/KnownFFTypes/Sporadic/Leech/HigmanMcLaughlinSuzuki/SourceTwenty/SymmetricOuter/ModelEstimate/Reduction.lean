module

public import CFSG.Quasithin.ChapterB.Section01.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanMcLaughlinSuzuki.SourceTwenty.SymmetricOuter.Factors
public import Theory.Representation.BinaryOffender.RankThreeDual

/-!
# Two branches of the induced S8 model estimate

An odd permutation exchanges the two four-spaces. Consequently projection
onto the first coordinate is injective on the common fixed space, bounding
its dimension by four. This branch needs neither an elementary actor nor
a rank assumption.

For actors in A8, the remaining input is an actual equivariant comparison
of the specified outer-conjugate four-space with the dual of the natural
four-space. Given that comparison, the faithful displacement bound proves
the desired estimate, including regular E8 subgroups. The comparison is
an explicit construction target here, not a proved model identification.

Source: Guralnick--Malle, Classification of 2F-modules I, Proposition 5.1,
HS paragraph, pp.16--17; Aschbacher--Smith K.4, printed p.457.
-/

public section
namespace CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Symmetric
open Representation Representation.BinaryOffender
open Representation.SymmetricEightConstituents

/-- The exact model comparison needed by the even-actor branch. Both
actions use the original exceptional isomorphism and the specified (0 1)
conjugation, with no change of group marking. -/
@[expose] def HasOuterDualComparison : Prop :=
  ∃ e : Four ≃ₗ[ZMod 2] Module.Dual (ZMod 2) Four,
    ∀ (a : alternatingGroup (Fin 8)) (v : Four),
      e (outerNatural a v) = natural.dual a (e v)

private theorem transposition_sign : transposition.sign = -1 := by
  apply (Int.units_eq_one_or transposition.sign).resolve_left
  intro ht
  have hh := symmetricRepresentation_inner ⟨transposition, ht⟩
    (0, fun _ => (1 : ZMod 2))
  change symmetricRepresentation transposition (0, fun _ => (1 : ZMod 2)) = _ at hh
  rw [symmetricRepresentation_transposition] at hh
  have hz := congrFun (congrArg Prod.fst hh) 0
  exact one_ne_zero (by simpa only [map_zero, Pi.zero_apply] using hz)

/-- Any subgroup containing an odd permutation has a fixed space of
dimension at most four on the actual induced pair. -/
theorem induced_fixedCodim_ge_four_of_not_le_alternating (B : Subgroup Models.S8)
    (hg : ¬ B ≤ alternatingGroup (Fin 8)) :
    4 ≤ fixedCodim Models.induced B := by
  classical
  obtain ⟨g, hgB, hgEven⟩ := Set.not_subset.mp hg
  have hsign : g.sign = -1 := (Int.units_eq_one_or g.sign).resolve_left hgEven
  let a : alternatingGroup (Fin 8) := ⟨g * transposition, by
    change (g * transposition).sign = 1
    rw [map_mul, hsign, transposition_sign]
    decide⟩
  have hag : a.val * transposition = g := by
    change g * transposition * transposition = g
    rw [mul_assoc, ← pow_two, transposition_sq, mul_one]
  have ha (v : Eight) : symmetricRepresentation g v =
      (natural a v.2, outerNatural a v.1) := by
    rw [← hag, map_mul, Module.End.mul_apply,
      symmetricRepresentation_transposition, symmetricRepresentation_inner]
  let f : fixedSpace symmetricRepresentation B →ₗ[ZMod 2] Four :=
    (LinearMap.fst (ZMod 2) Four Four).comp (fixedSpace symmetricRepresentation B).subtype
  have hf : Function.Injective f := by
    intro v w hvw
    apply Subtype.ext
    apply Prod.ext
    · exact hvw
    · have hv := congrArg Prod.snd (v.property ⟨g, hgB⟩)
      have hw := congrArg Prod.snd (w.property ⟨g, hgB⟩)
      change v.val.1 = w.val.1 at hvw
      change (symmetricRepresentation g v.val).2 = v.val.2 at hv
      change (symmetricRepresentation g w.val).2 = w.val.2 at hw
      rw [ha] at hv hw
      change outerNatural a v.val.1 = v.val.2 at hv
      change outerNatural a w.val.1 = w.val.2 at hw
      rw [← hv, ← hw, hvw]
  have hdim := LinearMap.finrank_le_finrank_of_injective hf
  have hfour : Module.finrank (ZMod 2) Four = 4 := by simp [Four]
  have htotal := fixedCodim_add_finrank symmetricRepresentation B
  rw [eight_finrank] at htotal
  rw [hfour] at hdim
  change 4 ≤ fixedCodim symmetricRepresentation B
  omega

/-- The faithful natural-plus-dual inequality applies to the literal
contained A8 actor, conditional on the specified outer-dual comparison. -/
theorem induced_fixedCodim_ge_four_of_outerDualComparison
    (hdual : HasOuterDualComparison) (B : Subgroup Models.S8)
    (hB : B ≤ alternatingGroup (Fin 8)) (hr : 3 ≤ rank B) :
    4 ≤ fixedCodim Models.induced B := by
  obtain ⟨e, he⟩ := hdual
  let A := alternatingGroup (Fin 8)
  let C := B.subgroupOf A
  have hCB : C.map A.subtype = B := Subgroup.map_subgroupOf_eq_of_le hB
  have hrC : 3 ≤ rank C := by
    have hh := rank_map_injective A.subtype Subtype.val_injective C
    rw [hCB] at hh
    omega
  let E : Eight ≃ₗ[ZMod 2] Four × Module.Dual (ZMod 2) Four :=
    (LinearEquiv.refl (ZMod 2) Four).prodCongr e
  have hE (a : A) (v : Eight) :
      E ((symmetricRepresentation.comp A.subtype) a v) =
        (natural.prod natural.dual) a (E v) := by
    change E (symmetricRepresentation a.val v) = _
    rw [symmetricRepresentation_inner]
    apply Prod.ext
    · rfl
    · exact he a v.2
  have hcost := fixedCodim_map_equivariant (symmetricRepresentation.comp A.subtype)
    (natural.prod natural.dual) (MonoidHom.id A) E hE C
  rw [Subgroup.map_id] at hcost
  have hres := fixedCodim_map_equivariant (symmetricRepresentation.comp A.subtype)
    symmetricRepresentation A.subtype (LinearEquiv.refl (ZMod 2) Eight)
    (fun _ _ => rfl) C
  rw [hCB] at hres
  change 4 ≤ fixedCodim symmetricRepresentation B
  rw [← hres, hcost]
  exact four_le_fixedCodim_prod_dual_of_rank_three natural natural_faithful C hrC

end CFSG.Quasithin.ChapterB.ComponentRecognition.KnownFFTypes.Sporadic.Leech.HigmanSims.Twenty.Symmetric
