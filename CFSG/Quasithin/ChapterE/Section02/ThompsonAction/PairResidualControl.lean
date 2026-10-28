module
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.PairResidualFactors
public import Theory.GroupTheory.PResidual.SubnormalSupplement
/-!
# Conjugation and normalization of the original residual pair

Residual formation commutes with the actual ambient conjugation. Lift the
source factor permutation and the chosen Sylow exchange through the original
centralizer quotient to the same factor preimages and residuals. The offender
preimage normalizes both residual factors, which are normal in O²(G) once
the genuine source residual containment is supplied.
Source: Aschbacher–Smith E.2.3(1) and the paired step in3.1.7.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction
variable {G H : Type*} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite G] [Finite H] in
theorem comap_map_conjugate (q : G →* H) (A : Subgroup H) (g : G) :
    (A.comap q).map (MulAut.conj g).toMonoidHom =
      (A.map (MulAut.conj (q g)).toMonoidHom).comap q := by
  ext x
  constructor
  · rintro ⟨v,hv,rfl⟩
    exact ⟨q v,hv,by simp [MulAut.conj_apply]⟩
  · rintro ⟨v,hv,he⟩
    refine ⟨g⁻¹*x*g,?_,by simp [MulAut.conj_apply,mul_assoc]⟩
    change q (g⁻¹*x*g) ∈ A
    have hh : q (g⁻¹*x*g) = v := by
      rw [map_mul,map_mul,map_inv,←he]
      simp [MulAut.conj_apply,mul_assoc]
    exact hh.symm ▸ hv

omit [Finite H] in
theorem factorResidual_conjugate (q : G →* H) (Y : Subgroup H) [Y.Normal]
    (A B : Subgroup Y) (g : G)
    (hAB : A.map (MulAut.conjNormal (q g)).toMonoidHom = B) :
    (factorResidual q Y A).map (MulAut.conj g).toMonoidHom = factorResidual q Y B := by
  have hh := congrArg (map Y.subtype) hAB
  have hc : Y.subtype.comp (MulAut.conjNormal (q g)).toMonoidHom =
      (MulAut.conj (q g)).toMonoidHom.comp Y.subtype := by ext; rfl
  rw [map_map,hc,←map_map] at hh
  change ((pResidual 2 ((A.map Y.subtype).comap q)).map _).map _ = _
  rw [map_embedded_pResidual,comap_map_conjugate,hh]

omit [Finite G] [Finite H] in
theorem factorResidual_normalized (q : G →* H) (Y : Subgroup H)
    (A : Subgroup Y) [A.Normal] :
    Y.comap q ≤ normalizer (factorResidual q Y A : Set G) := by
  have hA : factorPreimage q Y A ≤ Y.comap q := by
    intro x hx
    exact map_subtype_le A hx
  have hn := (normal_subgroupOf_iff_le_normalizer hA).mp (factorPreimage_normal q Y A)
  exact hn.trans (normalizer_le_normalizer_characteristic_image
    (factorPreimage q Y A) (pResidual 2 (factorPreimage q Y A)))


/-- Every ambient element permutes the same two original residual factors. -/
theorem paired_residual_factors_permuted
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype)) (g : G) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    let K₁ := factorResidual q Y d.first
    let K₂ := factorResidual q Y d.second
    (K₁.map (MulAut.conj g).toMonoidHom = K₁ ∧ K₂.map (MulAut.conj g).toMonoidHom = K₂) ∨
      (K₁.map (MulAut.conj g).toMonoidHom = K₂ ∧ K₂.map (MulAut.conj g).toMonoidHom = K₁) := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  have hcore : pCore 2 H = ⊥ := by
    let e := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective q hq)
    rw [←pCore_map_iso 2 e,hU.quotient_pCore_eq_bot,Subgroup.map_bot]
  have hcY : pCore 2 Y = ⊥ := by
    have hle : (pCore 2 Y).map Y.subtype ≤ pCore 2 H :=
      le_sSup ⟨inferInstance,pCore_isPGroup.map Y.subtype⟩
    rw [hcore] at hle
    apply bot_unique
    intro x hx
    exact Subtype.ext (hle (mem_map_of_mem Y.subtype hx))
  rcases d.automorphism_permutation hcY (MulAut.conjNormal (q g)) with h | h
  · exact Or.inl ⟨factorResidual_conjugate q Y _ _ g h.1,
      factorResidual_conjugate q Y _ _ g h.2⟩
  · exact Or.inr ⟨factorResidual_conjugate q Y _ _ g h.1,
      factorResidual_conjugate q Y _ _ g h.2⟩

omit [Finite H] in
/-- A chosen source exchange lifts through the original quotient to the residual pair. -/
theorem paired_residual_factors_exchange
    (T : Sylow 2 G) (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (q : G →* H) (hq : Function.Surjective q)
    (hker : q.ker = centralizer (U : Set G))
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hker).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)).subtype))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hker)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first) :
    let Y := offenderSubgroup (NormalElementaryQuotient.representation U q hq hker)
    ∃ t ∈ (T : Subgroup G),
      (factorResidual q Y d.first).map (MulAut.conj t).toMonoidHom = factorResidual q Y d.second ∧
      (factorResidual q Y d.second).map (MulAut.conj t).toMonoidHom = factorResidual q Y d.first := by
  let α := NormalElementaryQuotient.representation U q hq hker
  let Y := offenderSubgroup α
  let := offenderSubgroup_normal α
  obtain ⟨t,h₁,h₂⟩ := hexchange
  obtain ⟨g,hg,he⟩ := t.property
  refine ⟨g,hg,?_,?_⟩
  · exact factorResidual_conjugate q Y _ _ g (he.symm ▸ h₁)
  · exact factorResidual_conjugate q Y _ _ g (he.symm ▸ h₂)


omit [Finite G] [Finite H] in
theorem factorResidual_normal_in_residual (q : G →* H) (Y : Subgroup H)
    (A : Subgroup Y) [A.Normal] (hR : (pResidual 2 G).map q ≤ Y) :
    ((factorResidual q Y A).subgroupOf (pResidual 2 G)).Normal := by
  exact normal_subgroupOf_of_le_normalizer
    ((map_le_iff_le_comap.mp hR).trans (factorResidual_normalized q Y A))

end CFSG.Quasithin.ChapterE.ThompsonAction
