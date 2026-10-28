module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.OtherTypes.BinaryGeometry.Parabolics
public import Theory.GroupTheory.PResidual.NormalSubgroup
public import Theory.GroupTheory.PPerfectHom

/-!
# Embedding relative blocks of a lifted binary parabolic

A two-perfect subgroup of P Q, with P normalized by the two-group Q,
lies in P. Apply this twice to a relative block of a lifted parabolic:
once to put it in L, and once to put it in the parabolic preimage.
The binary component has trivial two-core, so its map into the literal
component quotient is injective. Intersecting the preimage with L thus
recovers the actual model parabolic. Pullback of the original subnormal
chain gives subnormality of the resulting model embedding.

The block itself remains the domain of this embedding. In particular no
claim that arbitrary images of short groups are short is used, and the
argument allows an outer graph automorphism in Q.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), E.6.8,
printed pp.247–248, and C.1.7, printed p.123.
-/

public section

open Subgroup Theory.GroupTheory BinaryLinear.OuterCyclic
namespace CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry
variable {G : Type*} [Group G] {Q L B : Subgroup G} {n : ℕ}

private theorem perfect_le_normal_factor {P R : Subgroup G}
    (hn : R ≤ normalizer (P : Set G)) (hr : IsPGroup 2 R)
    (hb : B ≤ P ⊔ R) (hp : IsPPerfect 2 B) : B ≤ P := by
  let D := P ⊔ R
  let N := P.subgroupOf D
  let : N.Normal := normal_subgroupOf_of_le_normalizer (sup_le P.le_normalizer hn)
  have hquot : IsPGroup 2 (D ⧸ N) :=
    isPGroup_quotient_of_sup_eq_top N (R.subgroupOf D) hr.comap_subtype
      (codisjoint_subgroupOf_sup P R).eq_top
  have ht := hp.hom_eq_one_of_isPGroup hquot
    ((QuotientGroup.mk' N).comp (inclusion hb))
  intro b hB
  exact (QuotientGroup.eq_one_iff (inclusion hb ⟨b, hB⟩)).mp
    (DFunLike.congr_fun ht ⟨b, hB⟩)

/-- The component embeds in its extension modulo the two-core. -/
theorem modelQuotientMap_injective (Q : Subgroup G) (hn : 0 < n)
    (hm : ClassicalGroup.IsPSL L n 2) : Function.Injective (modelQuotientMap Q hn hm) := by
  let E := componentExtension Q L
  let j : LinearGroup n →* E := (inclusion (show L ≤ E from le_sup_left)).comp
    (binaryEquiv hn hm).symm.toMonoidHom
  have hj : Function.Injective j := (inclusion_injective (show L ≤ E from le_sup_left)).comp (binaryEquiv hn hm).symm.injective
  have hp : (pCore 2 E).comap j ≤ pCore 2 (LinearGroup n) :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_of_injective j hj⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply le_bot_iff.mp
  change ((quotientMap Q L).comp j).ker ≤ ⊥
  rw [← MonoidHom.comap_ker, show (quotientMap Q L).ker = pCore 2 E from QuotientGroup.ker_mk' _]
  exact hp.trans (BinaryLinear.SmallParabolicLevi.linearGroup_twoCore_eq_bot.le)

/-- Quotient invariance lifts to normalization of the full ambient preimage. -/
theorem quotientPreimage_normalized {P : Subgroup (ComponentQuotient Q L)}
    (hN : Q ≤ normalizer (L : Set G))
    (hi : sylowImage Q L ≤ normalizer (P : Set (ComponentQuotient Q L))) :
    Q ≤ normalizer (quotientPreimage Q L P : Set G) := by
  intro q hq
  have hqE : q ∈ componentExtension Q L := by
    rw [componentExtension_eq hN]
    exact mem_sup_right hq
  apply (P.comap (quotientMap Q L)).le_normalizer_map (componentExtension Q L).subtype
  refine mem_map.mpr ⟨⟨q, hqE⟩, ?_, rfl⟩
  apply P.le_normalizer_comap (quotientMap Q L)
  apply hi
  apply mem_map_of_mem
  change q ∈ componentNormalizer Q L
  rw [componentNormalizer_eq hN]
  exact hq

/-- The inverse image of a model subgroup inside L is its literal copy in L. -/
private theorem in_model_of_in_preimage (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (P : Subgroup (LinearGroup n)) (l : L)
    (hl : (l : G) ∈ quotientPreimage Q L (quotientParabolic Q hn hm P)) :
    binaryEquiv hn hm l ∈ P := by
  have hmem := (mem_quotientPreimage (show (l : G) ∈ componentExtension Q L from
    (show L ≤ componentExtension Q L from le_sup_left) l.property)).mp hl
  have he : modelQuotientMap Q hn hm (binaryEquiv hn hm l) =
      quotientMap Q L ⟨l, (show L ≤ componentExtension Q L from le_sup_left) l.property⟩ := by
    change quotientMap Q L (inclusion le_sup_left ((binaryEquiv hn hm).symm (binaryEquiv hn hm l))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hm' : modelQuotientMap Q hn hm (binaryEquiv hn hm l) ∈ P.map (modelQuotientMap Q hn hm) :=
    he ▸ hmem
  exact (comap_map_eq_self_of_injective (modelQuotientMap_injective Q hn hm) P).le hm'

/-- Every two-perfect relative subgroup of the lift embeds subnormally in the literal model parabolic. -/
theorem exists_subnormal_model_embedding (hn : 0 < n) (hm : ClassicalGroup.IsPSL L n 2)
    (hN : Q ≤ normalizer (L : Set G)) (hQ : IsPGroup 2 Q)
    (P : Subgroup (LinearGroup n))
    (hi : sylowImage Q L ≤ normalizer (quotientParabolic Q hn hm P : Set _))
    (hBD : B ≤ quotientPreimage Q L (quotientParabolic Q hn hm P) ⊔ Q)
    (hs : (B.subgroupOf (quotientPreimage Q L (quotientParabolic Q hn hm P) ⊔ Q)).IsSubnormal)
    (hp : IsPPerfect 2 B) :
    ∃ f : B →* P, Function.Injective f ∧ f.range.IsSubnormal := by
  let R := quotientPreimage Q L (quotientParabolic Q hn hm P)
  let D := R ⊔ Q
  have hDE : D ≤ L ⊔ Q := sup_le
    ((quotientPreimage_le Q L _).trans (componentExtension_eq hN).le) le_sup_right
  have hBL : B ≤ L := perfect_le_normal_factor hN hQ (hBD.trans hDE) hp
  have hBR : B ≤ R := perfect_le_normal_factor (quotientPreimage_normalized hN hi) hQ hBD hp
  let j : P →* G := L.subtype.comp ((binaryEquiv hn hm).symm.toMonoidHom.comp P.subtype)
  have hj : Function.Injective j := L.subtype_injective.comp
    ((binaryEquiv hn hm).symm.injective.comp P.subtype_injective)
  have hjD (p : P) : j p ∈ D := by
    apply mem_sup_left
    apply (mem_quotientPreimage (show j p ∈ componentExtension Q L from
      (show L ≤ componentExtension Q L from le_sup_left) ((binaryEquiv hn hm).symm p).property)).mpr
    exact mem_map_of_mem (modelQuotientMap Q hn hm) p.property
  let a : P →* D := j.codRestrict D hjD
  let f : B →* P := ((binaryEquiv hn hm).toMonoidHom.comp (inclusion hBL)).codRestrict P
    (fun b => in_model_of_in_preimage hn hm P (inclusion hBL b) (hBR b.property))
  have hf : Function.Injective f := by
    intro x y he
    apply (inclusion_injective hBL)
    apply (binaryEquiv hn hm).injective
    exact congrArg Subtype.val he
  refine ⟨f, hf, ?_⟩
  have he : f.range = (B.subgroupOf D).comap a := by
    ext p
    constructor
    · rintro ⟨b, rfl⟩
      change j (f b) ∈ B
      change ((binaryEquiv hn hm).symm (binaryEquiv hn hm (inclusion hBL b)) : G) ∈ B
      rw [MulEquiv.symm_apply_apply]
      exact b.property
    · intro hpB
      refine ⟨⟨j p, hpB⟩, ?_⟩
      apply Subtype.ext
      change binaryEquiv hn hm ⟨j p, hBL hpB⟩ = p.val
      exact (binaryEquiv hn hm).apply_symm_apply p
  rw [he]
  exact hs.comap a

end CFSG.Quasithin.ChapterE.Section06.Components.OtherTypes.BinaryGeometry

end
