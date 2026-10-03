module

public import Stellmacher.ElementaryAbelianMaxOrder
public import Theory.GroupTheory.SylowNormalIntersection
public import Theory.GroupTheory.NormalClosureSupplement

/-!
# Internal generation of a Thompson normal closure

For a Sylow 2-subgroup `S`, put `J=J(S)` and let `E` be its
normal closure in the ambient finite group. The normal closure of `J`
inside `E` is already all of `E`.

The Sylow intersection `T=S∩E` contains `J(S)`, so the maximal
elementary-order comparison gives `J(T)=J(S)`. Its normalizer therefore
normalizes `J(S)`. Frattini gives `G=E N_G(T)`, and normal-closure
supplement transfer identifies the internal and ambient normal closures.

This makes explicit the generation step behind the final centralization
argument in the noncentralizing case of Stellmacher (2.3), journal p.20;
see `refs/latex/stellmacher-n-group.tex`. The lemma is independent of
the factor decomposition in (2.2).
-/

namespace Stellmacher.SectionTwo

/-- The elementary Thompson subgroup generates its ambient normal closure
also under conjugation by that normal closure itself. -/
public theorem thompson_normalClosure_generates
    {G : Type*} [Group G] [Finite G] (S : Sylow 2 G) :
    let J := elementaryAbelianMaxJ (S : Subgroup G)
    let E := Subgroup.normalClosure (J : Set G)
    Subgroup.normalClosure (J.subgroupOf E : Set E) = ⊤ := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  obtain ⟨T, hT⟩ := S.exists_subgroupOf_eq_of_normal E
  let R : Subgroup G := (T : Subgroup E).map E.subtype
  have hJS : J ≤ (S : Subgroup G) := sSup_le fun _ hA ↦ hA.1
  have hJE : J ≤ E := Subgroup.le_normalClosure
  have hRS : R ≤ (S : Subgroup G) := by
    rintro r ⟨rE, hr, rfl⟩
    rw [hT] at hr
    exact hr
  have hJR : J ≤ R := by
    intro j hj
    refine ⟨⟨j, hJE hj⟩, ?_, rfl⟩
    rw [hT]
    exact hJS hj
  have hsmall := elementaryAbelianMaxOrder_le_and_j_le_of_eq R (S : Subgroup G) hRS
  have hlarge := elementaryAbelianMaxOrder_le_and_j_le_of_maxJ_le (S : Subgroup G) R hJR
  have horder : elementaryAbelianMaxOrder R = elementaryAbelianMaxOrder (S : Subgroup G) :=
    le_antisymm hsmall.1 hlarge.1
  have hJeq : elementaryAbelianMaxJ R = J :=
    le_antisymm (hsmall.2 horder) (hlarge.2 horder.symm)
  have hNJ : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (J : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
    change R.map (MulAut.conj g).toMonoidHom = R at hg
    change J.map (MulAut.conj g).toMonoidHom = J
    rw [← hJeq, ← elementaryAbelianMaxJ_map_equiv (MulAut.conj g) R, hg]
  have hgen : E ⊔ Subgroup.normalizer (R : Set G) = ⊤ := by
    rw [sup_comm]
    exact Sylow.normalizer_sup_eq_top T
  have hclosure := Subgroup.normalClosure_eq_map_of_normal_supplement
    E (Subgroup.normalizer (R : Set G)) J hgen hJE hNJ
  change E = (Subgroup.normalClosure (J.subgroupOf E : Set E)).map E.subtype at hclosure
  apply Subgroup.map_injective E.subtype_injective
  rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact hclosure.symm

end Stellmacher.SectionTwo
