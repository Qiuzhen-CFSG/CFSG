module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.NaturalSource
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.SevenSource.BlockTyping
public import CFSG.Quasithin.ChapterB.Section03.Offenders.OddParity
public import Theory.SpecificGroups.Alternating.SevenComponent.PointSix
/-!
# The source block construction from an unfaithful natural A₇ action

The map into S₇ may have an odd central kernel on the component. If the
Thompson subgroup centralizes the natural module, B.2.10 makes Baum(T)
normal. Otherwise its image contains an actual offender; B.3.2's parity
calculation forces the image to be all S₇. C.1.24 then constructs a block
unless a nonzero characteristic subgroup of Baum(T) is normal.

The C.1.24 construction retains the central cover while lifting the cubic
and proving movement of the actual selected Sylow omega centre. No
identification of the given module with an omega-centre span is used.

Source: Aschbacher--Smith, B.2.10, B.3.2(4), C.1.24(a), printed pp.78--79,
83--84,130--131; applied to the contrary branch of 3.3.6--8, pp.587--588.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.SylowNormalizer
open BinaryPermutation
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem representation_intertwines
    (V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    {Q : Type*} [Group Q] (q : G →* Q) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (V : Set G))
    (j : Q →* Equiv.Perm (Fin 7))
    (e : Additive V ≃ₗ[ZMod 2] natural (Fin 7))
    (he : ∀ (g : G) (v : Additive V),
      e (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        naturalRepresentation (Fin 7) (j (q g)) (e v)) :
    ∀ g v, e (NormalElementaryQuotient.representation V q hq hk g v) =
      naturalRepresentation (Fin 7) (j g) (e v) := by
  intro a v
  obtain ⟨g,rfl⟩ := hq a
  rw [← he]
  congr 1
  apply Additive.toMul.injective
  apply Subtype.ext
  exact NormalElementaryQuotient.representation_apply V q hq hk g v

/-- The natural coordinates force the full S₇ actor in the moving branch;
C.1.24 then supplies the block without discarding a central cover. -/
theorem block_of_natural_seven_action
    (L V : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    [IsQuasisimple (L ⧸ pCore 2 L)]
    (hL : L.IsCComponent) (hf : generalizedFitting G = pCore 2 G)
    (hfL : generalizedFitting L = pCore 2 L) (T : Sylow 2 G)
    (hprod : ∀ g : G, ∃ l ∈ L, ∃ t ∈ (T : Subgroup G), l*t=g)
    (q : G →* Equiv.Perm (Fin 7)) (hk : q.ker = centralizer (V : Set G))
    (hLq : L.map q = alternatingGroup (Fin 7))
    (e : Additive V ≃ₗ[ZMod 2] natural (Fin 7))
    (he : ∀ (g : G) (v : Additive V),
      e (Additive.ofMul (MulAut.conjNormal g v.toMul)) =
        naturalRepresentation (Fin 7) (q g) (e v))
    (hm : ⁅V,L⁆ ≠ ⊥)
    (hcore : pCore 2 G = (T : Subgroup G) ⊓ centralizer (V : Set G))
    (hchar : ∀ C : Subgroup (ChapterB.baumann (T : Subgroup G)),
      C.Characteristic → C ≠ ⊥ →
      ¬ (C.map (ChapterB.baumann (T : Subgroup G)).subtype).Normal) :
    ChapterC.IsBlock L := by
  have hQT : pCore 2 G ≤ T := pCore_isPGroup.le_sylow_of_normal T
  have hVT : V ≤ T := (show V ≤ pCore 2 G from
    le_sSup ⟨inferInstance, IsElementaryAbelian.isPGroup 2 V⟩).trans hQT
  have hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.ker := by
    intro hJ
    have hn := (ChapterB.lemma_B_2_10_centralizing V (T : Subgroup G) hVT hQT
      hcore (by simpa only [ChapterB.thompsonJ_zero, hk] using hJ)).2.2.2
    have hTne : (T : Subgroup G) ≠ ⊥ := by
      intro ht
      have hv : V = ⊥ := le_bot_iff.mp (hVT.trans_eq ht)
      exact hm (by rw [hv, commutator_bot_left])
    let : Nontrivial (ChapterB.baumann (T : Subgroup G)) :=
      (nontrivial_iff_ne_bot _).mpr
        (ChapterC.RankOne.SymmetricSix.baumann_ne_bot (T : Subgroup G) T.isPGroup' hTne)
    exact hchar ⊤ inferInstance top_ne_bot (by
      simpa only [← MonoidHom.range_eq_map, range_subtype] using hn)
  have hq : Function.Surjective q := by
    let r := q.rangeRestrict
    have hr : Function.Surjective r := q.rangeRestrict_surjective
    have hkr : r.ker = centralizer (V : Set G) := by
      rw [MonoidHom.ker_rangeRestrict, hk]
    obtain ⟨A,hA⟩ := NormalElementaryQuotient.isFFModule_of_thompson_not_le V r hr hkr
      (T : Subgroup G) hVT (by
        change ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ q.rangeRestrict.ker
        rwa [MonoidHom.ker_rangeRestrict])
    have hE := representation_intertwines V r hr hkr q.range.subtype e he
    have hN := hA.map_equivariant _ (naturalRepresentation (Fin 7))
      q.range.subtype q.range.subtype_injective e hE
    have hC : IsOffender (coreRepresentation (Fin 7)) (A.map q.range.subtype) := by
      refine ⟨hN.1, ?_⟩
      rw [BinaryPermutation.fixedCodim_core_eq_full_odd (Fin 7) (by decide)]
      rw [← BinaryPermutation.fixedCodim_natural_eq_full_odd (Fin 7) (by decide)]
      exact hN.2
    have hnot := ChapterB.Offenders.core_offender_not_le_alternating (Or.inr rfl) hC
    have hAr : alternatingGroup (Fin 7) ≤ q.range := by
      rw [← hLq]
      exact map_le_range q L
    rcases alternatingGroup.SevenComponent.range_eq_alternating_or_top q hAr with ha | ht
    · exact False.elim (hnot (ha ▸ map_subtype_le A))
    · exact MonoidHom.range_eq_top.mp ht
  have hE := representation_intertwines V q hq hk (MonoidHom.id _) e he
  have hc : ∀ A, fixedCodim (NormalElementaryQuotient.representation V q hq hk) A =
      fixedCodim (naturalRepresentation (Fin 7)) A := by
    intro A
    simpa only [map_id] using fixedCodim_map_equivariant
      (NormalElementaryQuotient.representation V q hq hk)
      (naturalRepresentation (Fin 7)) (MonoidHom.id _) e hE A
  have hsi : Function.Injective e.symm.toLinearMap := e.symm.injective
  have hse : ∀ g v, e.symm (naturalRepresentation (Fin 7) g v) =
      NormalElementaryQuotient.representation V q hq hk g (e.symm v) := by
    intro g v
    apply e.injective
    rw [e.apply_symm_apply, hE, e.apply_symm_apply]
    rfl
  apply (ChapterC.RankOne.SevenSource.Natural.normal_characteristic_or_block_of_natural_seven_linear
    L V hL hf hfL T hprod q hq hk hLq hc e.symm.toLinearMap hsi hse hm).resolve_left
  rintro ⟨C,hC,hne,hn⟩
  exact hchar C hC hne hn
end CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.SylowNormalizer
