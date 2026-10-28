module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.CoreIdentification
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.SylowJoin
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.Product

/-!
# Gaschütz on the elementary total core identifies both original block cores

The individual centralizers Qi need not be abelian in the two-block case.
The source Frattini argument makes their intersection Q elementary. The
actual total S is Sylow in K₁K₂S by the two preceding Sylow assertions.
Gaschütz splits this same Q, and its crossed retraction restricts to each
two-perfect Ki, proving O₂(Ki)=Ui without discarding the natural cover.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G] {R K L : Subgroup G} {F F' : Type*} [Field F] [Field F']

private theorem paired_core_eq_module
    (h : Setup R K F) (h' : Setup R L F') (hR : IsPGroup 2 R)
    (hKL : L ≤ centralizer (K : Set G))
    (hSylow : ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    (hSylow' : ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = S R ⊓ L)
    (M T_H : Subgroup G) (x : G) (hx : x ∈ M) (hxR : x ∈ normalizer (R : Set G))
    (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G))
    (hQelem : IsElementaryAbelian 2 ↥(S R ⊓ centralizer ((U K ⊔ U L : Subgroup G) : Set G))) :
    K.pCoreIn 2 = U K ∧ L.pCoreIn 2 = U L := by
  let U₀ := U K ⊔ U L
  let Q₀ := S R ⊓ centralizer (U₀ : Set G)
  let N := (K ⊔ L) ⊔ S R
  let V := U₀.map (MulAut.conj x⁻¹).toMonoidHom
  have hKN : K ≤ N := le_sup_left.trans le_sup_left
  have hLN : L ≤ N := le_sup_right.trans le_sup_left
  have hSN : S R ≤ N := le_sup_right
  have hQN : Q₀ ≤ N := inf_le_left.trans hSN
  have hUS : U₀ ≤ S R := sup_le h.module_le h'.module_le
  have hUN : U₀ ≤ N := hUS.trans hSN
  have hVS : V ≤ S R := (map_mono hUS).trans_eq (h.stable hxR)
  have hVN : V ≤ N := hVS.trans hSN
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hnc' := second_noncommuting hi
  have hQeq : Q₀ = Q R K ⊓ Q R L := by
    rw [h.core,h'.core]
    ext a
    constructor
    · rintro ⟨ha,hc⟩
      exact ⟨⟨ha,centralizer_le (show U K ≤ U₀ from le_sup_left) hc⟩,
        ⟨ha,centralizer_le (show U L ≤ U₀ from le_sup_right) hc⟩⟩
    · rintro ⟨⟨ha,hc⟩,⟨_,hc'⟩⟩
      refine ⟨ha,?_⟩
      have hh : U₀ ≤ centralizer ({a} : Set G) := sup_le
        (by intro u hu; exact mem_centralizer_singleton_iff.mpr (hc u hu))
        (by intro u hu; exact mem_centralizer_singleton_iff.mpr (hc' u hu))
      intro u hu
      exact mem_centralizer_singleton_iff.mp (hh hu)
  have hQ1 : Q₀ ≤ Q R K := hQeq ▸ inf_le_left
  have hQ2 : Q₀ ≤ Q R L := hQeq ▸ inf_le_right
  let := h.elementary
  let := h'.elementary
  let : IsElementaryAbelian 2 U₀ := IsElementaryAbelian.sup_of_le_centralizer
    ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _))))
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map (MulAut.conj x⁻¹).toMonoidHom
  have hUQ : U₀ ≤ Q₀ := le_inf hUS (le_centralizer U₀)
  have hKQ : ⁅K,Q₀⁆ ≤ U K := (commutator_mono le_rfl hQ1).trans (h.core_commutator_le hxR hnc)
  have hLQ : ⁅L,Q₀⁆ ≤ U L := (commutator_mono le_rfl hQ2).trans (h'.core_commutator_le hxR hnc')
  have hSQ : S R ≤ normalizer (Q₀ : Set G) := by
    rw [hQeq]
    have hnK : S R ≤ normalizer (Q R K : Set G) := le_sup_right.trans
      ((K ⊔ S R).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (K ⊔ S R) (pCore 2 (K ⊔ S R : Subgroup G))))
    have hnL : S R ≤ normalizer (Q R L : Set G) := le_sup_right.trans
      ((L ⊔ S R).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (L ⊔ S R) (pCore 2 (L ⊔ S R : Subgroup G))))
    exact (le_inf hnK hnL).trans inf_normalizer_le_normalizer_inf
  have hNQ : N ≤ normalizer (Q₀ : Set G) := sup_le (sup_le
    (le_normalizer_iff_commutator_le_right.mpr (hKQ.trans (le_sup_left.trans hUQ)))
    (le_normalizer_iff_commutator_le_right.mpr (hLQ.trans (le_sup_right.trans hUQ)))) hSQ
  let Q' := Q₀.subgroupOf N
  let : Q'.Normal := normal_subgroupOf_of_le_normalizer hNQ
  let := hQelem
  let : IsElementaryAbelian 2 Q' := IsElementaryAbelian.subgroupOf hQN
  let : IsElementaryAbelian 2 (V.subgroupOf N) := IsElementaryAbelian.subgroupOf hVN
  obtain ⟨T,hT⟩ := exists_sylow_two_block_join (S R) K L (hR.to_le inf_le_left)
    h.normalizes h'.normalizes (le_centralizer_iff.mp hKL) hSylow hSylow'
  have hTeq : (T : Subgroup N) = (S R).subgroupOf N :=
    (map_injective N.subtype_injective) (hT.trans (map_subgroupOf_eq_of_le hSN).symm)
  have hVT : V.subgroupOf N ≤ T := hTeq ▸ subgroupOf_mono N hVS
  have hspan : (T : Subgroup N) = Q' ⊔ V.subgroupOf N := by
    rw [hTeq,← subgroupOf_sup hQN hVN]
    exact congrArg (fun A : Subgroup G => A.subgroupOf N)
      ((h.two_block_factorization h' hKL M T_H x hx hxR hindex hpair ht hnc).2.2.1.trans (sup_comm _ _))
  have hcoreKQ : K.pCoreIn 2 ≤ Q₀ := by
    have hq : K.pCoreIn 2 ≤ Q R K := pCoreIn_mono_of_normalizes le_sup_left (sup_le K.le_normalizer h.normalizes)
    rw [hQeq]
    refine le_inf hq ?_
    rw [h'.core]
    exact le_inf (hq.trans (h.core ▸ inf_le_left))
      ((pCoreIn_le 2 K).trans ((le_centralizer_iff.mp hKL).trans (centralizer_le (map_subtype_le _))))
  have hcoreLQ : L.pCoreIn 2 ≤ Q₀ := by
    have hq : L.pCoreIn 2 ≤ Q R L := pCoreIn_mono_of_normalizes le_sup_left (sup_le L.le_normalizer h'.normalizes)
    rw [hQeq]
    refine le_inf ?_ hq
    rw [h.core]
    exact le_inf (hq.trans (h'.core ▸ inf_le_left))
      ((pCoreIn_le 2 L).trans (hKL.trans (centralizer_le (map_subtype_le _))))
  have finish (J W : Subgroup G) (hJN : J ≤ N) (hJW : IsPPerfect 2 J)
      (hJQ : ⁅J,Q₀⁆ ≤ W) (hcore : J.pCoreIn 2 ≤ Q₀) : J.pCoreIn 2 ≤ W := by
    have hp : IsPPerfect 2 (J.subgroupOf N) := hJW.of_surjective
      (subgroupOfEquivOfLe hJN).symm.toMonoidHom (subgroupOfEquivOfLe hJN).symm.surjective
    have hcomm : ⁅J.subgroupOf N,Q'⁆ ≤ W.subgroupOf N := by
      apply commutator_le.mpr
      intro j hj q hq
      exact hJQ (commutator_mem_commutator hj hq)
    have hh := radical_intersection_le_of_sylow_supplement Q' (J.subgroupOf N)
      (W.subgroupOf N) (V.subgroupOf N) (IsElementaryAbelian.isPGroup 2 Q') hp hcomm T hVT hspan
    intro j hj
    exact hh (show (⟨j,hQN (hcore hj)⟩ : N) ∈ J.subgroupOf N ⊓ Q' from
      ⟨pCoreIn_le 2 J hj,hcore hj⟩)
  exact ⟨le_antisymm (finish K (U K) hKN h.short.twoPerfect hKQ hcoreKQ) (map_mono blockU_le_core),
    le_antisymm (finish L (U L) hLN h'.short.twoPerfect hLQ hcoreLQ) (map_mono blockU_le_core)⟩

/-- Both genuine block cores follow from the original common-normal obstruction. -/
theorem Setup.two_block_individual_cores
    (h : Setup R K F) (h' : Setup R L F') (hR : IsPGroup 2 R)
    (hKL : L ≤ centralizer (K : Set G))
    (hSylow : ∃ T : Sylow 2 K, (T : Subgroup K).map K.subtype = S R ⊓ K)
    (hSylow' : ∃ T : Sylow 2 L, (T : Subgroup L).map L.subtype = S R ⊓ L)
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M) (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer (K ⊔ L : Subgroup G)) (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) → M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (U K : Set G)) :
    K.pCoreIn 2 = U K ∧ L.pCoreIn 2 = U L := by
  have hp := h.two_block_source_product h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  exact paired_core_eq_module h h' hR hKL hSylow hSylow' M T_H x hx (hMR hx) hindex hpair ht hnc hp.2.2.2.2.2
end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
