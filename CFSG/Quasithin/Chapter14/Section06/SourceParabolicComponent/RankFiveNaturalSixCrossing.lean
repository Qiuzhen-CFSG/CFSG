module
public import CFSG.Quasithin.Chapter14.Section06.SourceQuadraticBound
public import CFSG.Quasithin.Chapter14.Section06.SourceNormalSubgroups
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.Basic
public import Theory.GroupTheory.PResidual.SubnormalCoreAction
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.ConjugateSpanSylow

/-!
# The original conjugate-module crossing

In the abelian plane branch, every nonidentity point has an abelian
centralizer span. Thus any conjugate by a plane-centralizing element of
the component point span centralizes that same point span.

For the selected block C in I, the external radical satisfies
[O₂(I),C] ≤ U(C) by two-perfect commutator idempotence. If a conjugate
U(C)^t remained in O₂(I), I and t would normalize U(C)U(C)^t.
Its normalizer is a two-local overgroup, contradicting maximality of T∩I.
All subgroups and conjugations are the original ambient ones.

Source: Aschbacher–Smith 14.6.10(5), printed p.1030, the conjugate B
and point-span calculations. The finite augmentation-core action supplies
the subsequent transposition calculation separately.
-/

public section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hunique hmany hcard e hab

 theorem source_rankTwo_point_span_abelian (v : G)
    (hv : v ∈ localModule T M) (hv1 : v ≠ 1) :
    IsMulCommutative (conjugateSpanBy (localModule T M) (centralizer ({v} : Set G))) :=
  point_span_abelian_of_intersecting_conjugates_commute _ hv hv1
    (source_rankTwo_intersecting_conjugates_commute hG T hempty hM hunique hmany hcard e hab)

 theorem source_rankTwo_point_span_conjugate_commute (C : Subgroup G) (v t : G)
    (hv : v ∈ localModule T M) (hv1 : v ≠ 1)
    (ht : t ∈ centralizer (localModule T M : Set G)) :
    let Wv := conjugateSpanBy (localModule T M) (C ⊓ centralizer ({v} : Set G))
    Wv.map (MulAut.conj t).toMonoidHom ≤ centralizer (Wv : Set G) := by
  let U := conjugateSpanBy (localModule T M) (centralizer ({v} : Set G))
  let Wv := conjugateSpanBy (localModule T M) (C ⊓ centralizer ({v} : Set G))
  let : IsMulCommutative U := source_rankTwo_point_span_abelian
    hG T hempty hM hunique hmany hcard e hab v hv hv1
  have hWU : Wv ≤ U := conjugateSpanBy_mono le_rfl inf_le_right
  have htC : t ∈ centralizer ({v} : Set G) :=
    mem_centralizer_singleton_iff.mpr (ht v hv).symm
  have htN : t ∈ normalizer (U : Set G) := le_normalizer_conjugateSpanBy _ _ htC
  have hBU : Wv.map (MulAut.conj t).toMonoidHom ≤ U := by
    rintro x ⟨w,hw,rfl⟩
    exact (mem_normalizer_iff.mp htN w).mp (hWU hw)
  exact hBU.trans ((le_centralizer U).trans (centralizer_le hWU))

end CFSG.Quasithin.Chapter14.Section06

public section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem core_commutator_le_blockModule (I C : Subgroup G)
    (hCI : C ≤ I) (hIC : I ≤ normalizer (C : Set G)) (hC : IsPPerfect 2 C) :
    ⁅I.pCoreIn 2,C⁆ ≤ (ChapterC.blockU C).map C.subtype := by
  let Q := I.pCoreIn 2
  have hIQ : I ≤ normalizer (Q : Set G) := I.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image I (pCore 2 I))
  have hCQ : C ≤ normalizer (Q : Set G) := hCI.trans hIQ
  have hcommQ : ⁅Q,C⁆ ≤ Q := le_normalizer_iff_commutator_le_left.mp hCQ
  have hcommC : ⁅Q,C⁆ ≤ C := le_normalizer_iff_commutator_le_right.mp
    ((pCoreIn_le 2 I).trans hIC)
  have hcommcore : ⁅Q,C⁆ ≤ C.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 I).to_le hcommQ) hcommC
      (normalizer_commutator_ge_right Q C)
  have hm : (ChapterC.blockU C).map C.subtype = ⁅C.pCoreIn 2,C⁆ := by
    rw [ChapterC.blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype]
    rfl
  rw [hm]
  exact (commutator_isPPerfect_idempotent C Q hC (isPGroup_pCoreIn 2 I) hCQ).symm.le.trans
    (commutator_mono hcommcore le_rfl)

omit [Finite G] in
private theorem conjugate_module_escape
    (T : Sylow 2 G) (Tu M Mc I C W : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (hgen : C ⊔ ((T : Subgroup G) ⊓ I) = I)
    (hW : W ≠ ⊥) (hWS : W ≤ (T : Subgroup G) ⊓ I)
    (hIW : I ≤ normalizer (W : Set G))
    (hcomm : ⁅I.pCoreIn 2,C⁆ ≤ W)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htI : t ∉ I)
    (htS : t ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G))
    (htt : t * t ∈ I) :
    ¬ W.map (MulAut.conj t).toMonoidHom ≤ I.pCoreIn 2 := by
  let S := (T : Subgroup G) ⊓ I
  let B := W.map (MulAut.conj t).toMonoidHom
  let P := W ⊔ B
  have hPT : P ≤ (T : Subgroup G) := by
    apply sup_le (hWS.trans inf_le_left)
    rintro _ ⟨w,hw,rfl⟩
    exact (T : Subgroup G).mul_mem
      ((T : Subgroup G).mul_mem ht ((hWS hw).1)) ((T : Subgroup G).inv_mem ht)
  have hSB : S ≤ normalizer (B : Set G) := by
    apply le_normalizer_iff.mpr
    rintro s hs _ ⟨w,hw,rfl⟩
    have hs' : t⁻¹*s*t ∈ S := by
      have hh := (mem_normalizer_iff.mp ((normalizer (S : Set G)).inv_mem htS) s).mp hs
      simpa only [inv_inv] using hh
    refine ⟨(t⁻¹*s*t)*w*(t⁻¹*s*t)⁻¹,
      (mem_normalizer_iff.mp (hIW hs'.2) w).mp hw,?_⟩
    change t * ((t⁻¹*s*t)*w*(t⁻¹*s*t)⁻¹) * t⁻¹ = s * (t*w*t⁻¹) * s⁻¹
    group
  have hSP : S ≤ normalizer (P : Set G) :=
    (le_inf (inf_le_right.trans hIW) hSB).trans
      (normalizer_inf_normalizer_le_normalizer_sup W B)
  have htP : t ∈ normalizer (P : Set G) := by
    rw [mem_normalizer_iff_map_conj_eq,Subgroup.map_sup]
    have hb : B.map (MulAut.conj t).toMonoidHom = W := by
      change (W.map _).map _ = _
      rw [map_map]
      have he : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
          (MulAut.conj (t*t)).toMonoidHom := by
        ext x
        change t * (t*x*t⁻¹) * t⁻¹ = (t*t)*x*(t*t)⁻¹
        group
      rw [he]
      exact mem_normalizer_iff_map_conj_eq.mp (hIW htt)
    change B ⊔ B.map (MulAut.conj t).toMonoidHom = P
    rw [hb,sup_comm]
  intro hBQ
  have hCP : C ≤ normalizer (P : Set G) := by
    apply le_normalizer_iff.mpr
    intro c hc x hx
    have hWc : W.map (MulAut.conj c).toMonoidHom ≤ P := by
      exact (mem_normalizer_iff_map_conj_eq.mp (hIW ((le_sup_left.trans hgen.le) hc))).le.trans le_sup_left
    have hBc : B.map (MulAut.conj c).toMonoidHom ≤ P := by
      rintro _ ⟨b,hb,rfl⟩
      change (MulAut.conj c) b ∈ P
      rw [conj_eq_commutatorElement_mul]
      have hcb : ⁅c,b⁆ ∈ W := by
        apply hcomm
        rw [commutator_comm]
        exact commutator_mem_commutator hc (hBQ hb)
      exact P.mul_mem ((le_sup_left : W ≤ P) hcb) ((le_sup_right : B ≤ P) hb)
    have hh : P.map (MulAut.conj c).toMonoidHom ≤ P := by
      rw [Subgroup.map_sup]
      exact sup_le hWc hBc
    exact hh (mem_map_of_mem _ hx)
  have hIP : I ≤ normalizer (P : Set G) := hgen ▸ sup_le hCP hSP
  have hPne : P ≠ ⊥ := fun hp => hW (le_bot_iff.mp (hp ▸ (show W ≤ P from le_sup_left)))
  have hlocal : normalizer (P : Set G) ∈ Chapter1.H G :=
    Chapter1.mem_H_of_isTwoLocal ⟨P,hPne,T.isPGroup'.to_le hPT,rfl⟩
  have he := (lemma14_6_5 hI hIP hlocal).2
  exact htI (he ▸ (show t ∈ (T : Subgroup G) ⊓ normalizer (P : Set G) from ⟨ht,htP⟩)).2

/-- In the literal source block branch the selected conjugate leaves the
original two-core. The only geometric choice still supplied is the element t. -/
theorem source_parabolic_block_conjugate_escape
    (T : Sylow 2 G) (Tu M Mc I C : Subgroup G)
    (hI : I ∈ IStar (T : Subgroup G) (outsideOvergroups (Chapter1.H G) Tu Mc M))
    (hCI : C ≤ I) (hIC : I ≤ normalizer (C : Set G))
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I)
    (hgen : C ⊔ ((T : Subgroup G) ⊓ I) = I)
    (hC : ChapterC.IsShort C)
    (t : G) (ht : t ∈ (T : Subgroup G)) (htI : t ∉ I)
    (htS : t ∈ normalizer (((T : Subgroup G) ⊓ I : Subgroup G) : Set G))
    (htt : t * t ∈ I) :
    ¬ ((ChapterC.blockU C).map C.subtype).map (MulAut.conj t).toMonoidHom ≤
      I.pCoreIn 2 := by
  let W := (ChapterC.blockU C).map C.subtype
  have hW : W ≠ ⊥ := fun hz => hC.blockU_ne_bot
    (((ChapterC.blockU C).map_eq_bot_iff_of_injective C.subtype_injective).mp hz)
  have hWQ : W ≤ I.pCoreIn 2 := (map_mono ChapterC.blockU_le_core).trans
    (pCoreIn_mono_of_normalizes hCI hIC)
  obtain ⟨S,hS⟩ := hSyl
  have hWS : W ≤ (T : Subgroup G) ⊓ I := hWQ.trans (hS ▸ pCoreIn_le_sylow I S)
  have hIW : I ≤ normalizer (W : Set G) := hIC.trans
    (normalizer_le_normalizer_characteristic_image C (ChapterC.blockU C))
  exact conjugate_module_escape T Tu M Mc I C W hI hgen hW hWS hIW
    (core_commutator_le_blockModule I C hCI hIC hC.twoPerfect) t ht htI htS htt

end CFSG.Quasithin.Chapter14.Section06
