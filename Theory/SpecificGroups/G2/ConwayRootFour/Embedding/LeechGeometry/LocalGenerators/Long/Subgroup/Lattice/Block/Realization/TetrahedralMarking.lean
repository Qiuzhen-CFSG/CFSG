module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.ScalarInterface
public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Subgroup.Lattice.Block.Realization.TetrahedralMarking.RationalUnits
public import Theory.GroupAction.SimpleCosets
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# A tetrahedral marking of the actual rational icosian scalar image

The rational norm-one icosians are the 24 Hurwitz units. Their literal map to
the retained scalar A₅ has two signs as its kernel, so its image has order 12.
The faithful action of A₅ on this subgroup's five cosets identifies that image
with a four-point stabilizer. Labeling the identity coset by the fifth point
then gives an injective marking from the existing `alternatingGroup fourPoints`
with exactly the prescribed range.

This argument uses the actual scalar image and does not require computing the
noncomputable golden-projective-line labeling. The comparison application is
in `TetrahedralMarking.Comparison`.

Source application: Aschbacher, *Sporadic Groups* (1994), 49.2 and 49.5.
The retained icosian models and scalar quotient are the attributed ATLAS ports
of Gerald Höhn, revision `8eabb35afe2b5e45bf913a2d05c53e558d2e2917`;
see `LICENSES/ATLAS.txt` and `LICENSES/ATLAS-CITATION.cff`.
-/

@[expose] public noncomputable section

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization

private theorem four_range_iff (g : alternatingGroup (Fin 5)) :
    g ∈ (alternatingGroup.ofSubtype fourPoints).range ↔ g.val 4 = 4 := by
  rw [alternatingGroup.mem_range_ofSubtype_iff]
  constructor
  · intro hs
    apply Equiv.Perm.notMem_support.mp
    intro h
    exact (by decide : (4 : Fin 5) ∉ fourPoints) (hs h)
  · intro hg i hi
    fin_cases i <;> simp_all [fourPoints, Equiv.Perm.mem_support]

private theorem exists_tetrahedral_marking (H : Subgroup (alternatingGroup (Fin 5)))
    (hH : Nat.card H = 12) :
    ∃ j : alternatingGroup fourPoints →* alternatingGroup (Fin 5),
      Function.Injective j ∧ j.range = H := by
  classical
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have hi : H.index = 5 := by
    have h := H.card_mul_index
    rw [hH, hcard] at h
    omega
  have hp : H ≠ ⊤ := by
    intro h
    have := Subgroup.index_eq_one.mpr h
    omega
  let := H.faithfulSMul_quotient_of_simple hp
  let := Fintype.ofFinite (alternatingGroup (Fin 5) ⧸ H)
  let q : alternatingGroup (Fin 5) ⧸ H := QuotientGroup.mk 1
  let e₀ : (alternatingGroup (Fin 5) ⧸ H) ≃ Fin 5 :=
    Fintype.equivFinOfCardEq ((Nat.card_eq_fintype_card (α := alternatingGroup (Fin 5) ⧸ H)).symm.trans
      (H.index_eq_card.symm.trans hi))
  let e := e₀.trans (Equiv.swap (e₀ q) 4)
  have he : e q = 4 := by simp [e]
  let f : alternatingGroup (Fin 5) →* Equiv.Perm (Fin 5) :=
    e.permCongrHom.toMonoidHom.comp
      (MulAction.toPermHom (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5) ⧸ H))
  have hf : Function.Injective f :=
    e.permCongrHom.injective.comp MulAction.toPerm_injective
  have hs (g : alternatingGroup (Fin 5)) : f g ∈ alternatingGroup (Fin 5) := by
    let s := Equiv.Perm.sign.comp f
    rcases s.normal_ker.eq_bot_or_eq_top with hk | hk
    · have hc := Nat.card_le_card_of_injective s (s.ker_eq_bot_iff.mp hk)
      have ht : Nat.card ℤˣ = 2 := by simp [Nat.card_eq_fintype_card]
      rw [hcard, ht] at hc
      omega
    · have hm : g ∈ s.ker := hk ▸ Subgroup.mem_top g
      exact hm
  let fA := f.codRestrict (alternatingGroup (Fin 5)) hs
  have hb : Function.Bijective fA := by
    apply (Nat.bijective_iff_injective_and_card _).mpr
    exact ⟨fun g h heq => hf (congrArg Subtype.val heq), rfl⟩
  let E := MulEquiv.ofBijective fA hb
  have hfix (g : alternatingGroup (Fin 5)) : (E g).val 4 = 4 ↔ g ∈ H := by
    change f g 4 = 4 ↔ g ∈ H
    rw [← he]
    change e (g • e.symm (e q)) = e q ↔ g ∈ H
    rw [e.symm_apply_apply, e.injective.eq_iff]
    change g ∈ MulAction.stabilizer (alternatingGroup (Fin 5)) q ↔ g ∈ H
    rw [MulAction.stabilizer_quotient]
  let j := E.symm.toMonoidHom.comp (alternatingGroup.ofSubtype fourPoints)
  refine ⟨j, E.symm.injective.comp alternatingGroup.ofSubtype_injective, ?_⟩
  ext g
  constructor
  · rintro ⟨a, rfl⟩
    apply (hfix _).mp
    change (E (E.symm (alternatingGroup.ofSubtype fourPoints a))).val 4 = 4
    rw [E.apply_symm_apply]
    exact (four_range_iff _).mp ⟨a, rfl⟩
  · intro hg
    obtain ⟨a, ha⟩ := (four_range_iff (E g)).mpr ((hfix g).mpr hg)
    refine ⟨a, ?_⟩
    change E.symm (alternatingGroup.ofSubtype fourPoints a) = g
    rw [ha, E.symm_apply_apply]

/-- The literal rational scalar image admits a faithful marking on the existing four points. -/
theorem exists_rationalTetrahedralMarking :
    ∃ j : alternatingGroup fourPoints →* alternatingGroup (Fin 5),
      Function.Injective j ∧ j.range = rationalScalarToFive.range :=
  exists_tetrahedral_marking rationalScalarToFive.range rationalScalarToFive_range_card

/-- An unconditional A₄ marking of the actual rational norm-one scalar image. -/
def rationalTetrahedralMarking : alternatingGroup fourPoints →* alternatingGroup (Fin 5) :=
  Classical.choose exists_rationalTetrahedralMarking

theorem rationalTetrahedralMarking_injective : Function.Injective rationalTetrahedralMarking :=
  (Classical.choose_spec exists_rationalTetrahedralMarking).1

/-- Equality with the literal inclusion, sign quotient, and retained five-point equivalence. -/
theorem rationalTetrahedralMarking_range :
    rationalTetrahedralMarking.range = rationalScalarToFive.range :=
  (Classical.choose_spec exists_rationalTetrahedralMarking).2

end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Long.Block.Realization
