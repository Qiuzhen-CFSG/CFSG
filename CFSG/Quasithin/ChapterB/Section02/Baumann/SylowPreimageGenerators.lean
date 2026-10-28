module
public import CFSG.Quasithin.ChapterB.Section02.Baumann.PreimageGenerators
public import CFSG.Quasithin.Chapter1.Section02.LocalComponents
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.ElementaryThompsonRelative
/-!
# Baumann generation with Sylow preimages

Equal-weight replacement places the maximum elementary subgroups in the
Thompson groups of Sylow preimages. Sylow conjugacy and the residual/Sylow
factorization transport them back into the generated group. This proves
condition (e) and the alpha and Sylow conclusions without making the full
action kernel a two-group.

Source: Aschbacher--Smith B.2.19, printed pp.81--82. The augmentation
application retains the central three in the covered row of 13.2.2(7).
-/

public noncomputable section
open Subgroup Stellmacher
open scoped IsMulCommutative
open Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.BaumannArgument
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_conj_mul (A : Subgroup G) (g h : G) :
    (A.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom =
      A.map (MulAut.conj (g*h)).toMonoidHom := A.conjBy_conjBy h g

private theorem max_le_J_of_order (R D A : Subgroup G)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hAD : A ≤ D)
    (horder : elementaryAbelianMaxOrder D = elementaryAbelianMaxOrder R) :
    A ≤ elementaryAbelianMaxJ D := by
  apply le_sSup
  refine ⟨hAD,hA.2.1,?_⟩
  intro E hED hE
  obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty D
  exact (hB.2.2 E hED hE).trans_eq
    ((card_eq_elementaryAbelianMaxOrder D B hB).trans
      (horder.trans (maxOrder_eq_card_of_mem R A hA)))

/-- Sylow conjugacy lifts a maximum elementary subgroup through a full
preimage even when its kernel has odd order elements. -/
theorem maximum_le_of_sylow_and_residual_normalizes
    (R D Y I A : Subgroup G) (hD : IsSylowSubgroupIn D Y)
    (hA : A ∈ elementaryAbelianMaxSubgroups R) (hAY : A ≤ Y)
    (horder : elementaryAbelianMaxOrder D = elementaryAbelianMaxOrder R)
    (hJI : elementaryAbelianMaxJ D ≤ I)
    (hLI : pResidual 2 G ≤ normalizer (I : Set G)) : A ≤ I := by
  obtain ⟨S,hS⟩ := hD
  obtain ⟨P,hP⟩ := (hA.2.1.isPGroup.comap_subtype (K := Y)).exists_le_sylow
  obtain ⟨y,hy⟩ := MulAction.exists_smul_eq Y P S
  have hAD : A.map (MulAut.conj y.val).toMonoidHom ≤ D := by
    rw [←hS]
    rintro _ ⟨a,ha,rfl⟩
    refine ⟨y * ⟨a,hAY ha⟩ * y⁻¹,?_,rfl⟩
    have he : (P : Subgroup Y).map (MulAut.conj y).toMonoidHom = S := by
      change ((y • P : Sylow 2 Y) : Subgroup Y) = S
      rw [hy]
    rw [←he]
    exact mem_map_of_mem _ (hP ha)
  have hmax : A.map (MulAut.conj y.val).toMonoidHom ≤ elementaryAbelianMaxJ D := by
    apply le_sSup
    refine ⟨hAD,hA.2.1.map _,?_⟩
    intro E hED hE
    rw [card_map_of_injective (MulAut.conj y.val).injective]
    obtain ⟨B,hB⟩ := elementaryAbelianMaxSubgroups_nonempty D
    exact (hB.2.2 E hED hE).trans_eq
      ((card_eq_elementaryAbelianMaxOrder D B hB).trans
        (horder.trans (maxOrder_eq_card_of_mem R A hA)))
  have hYS : Y ≤ pResidual 2 G ⊔ D := by
    have hh := congrArg (map Y.subtype) (pResidual_sup_sylow_eq_top S)
    rw [Subgroup.map_sup,hS,←MonoidHom.range_eq_map,range_subtype] at hh
    exact hh.symm.le.trans (sup_le_sup_right (map_pResidual_le 2 Y.subtype) _)
  obtain ⟨l,hl,d,hd,hld⟩ := mem_sup_of_normal_left.mp (hYS (Y.inv_mem y.property))
  have hconj : (elementaryAbelianMaxJ D).map (MulAut.conj y.val⁻¹).toMonoidHom ≤ I := by
    rw [←hld,←map_conj_mul]
    have hdn : (elementaryAbelianMaxJ D).map (MulAut.conj d).toMonoidHom =
        elementaryAbelianMaxJ D := mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_elementaryAbelianMaxJ D (D.le_normalizer hd))
    rw [hdn]
    exact (map_mono hJI).trans_eq (mem_normalizer_iff_map_conj_eq.mp (hLI hl))
  have hm := (map_mono (f := (MulAut.conj y.val⁻¹).toMonoidHom) hmax).trans hconj
  rw [map_conj_mul,inv_mul_cancel] at hm
  have hid : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by ext x;simp
  rwa [hid,map_id] at hm



omit [Finite G] in
private theorem map_preimage_conjugate {K : Type*} [Group K]
    (q : G →* K) (D : Subgroup G) (g : G) :
    ((D.map q).comap q).map (MulAut.conj g).toMonoidHom =
      (((D.map (MulAut.conj g).toMonoidHom).map q).comap q) := by
  ext x
  constructor
  · rintro ⟨y,⟨d,hd,he⟩,rfl⟩
    refine ⟨g*d*g⁻¹,mem_map_of_mem _ hd,?_⟩
    simp only [map_mul,map_inv,he,MulEquiv.coe_toMonoidHom,MulAut.conj_apply]
  · rintro ⟨_,⟨d,hd,rfl⟩,he⟩
    refine ⟨g⁻¹*x*g,⟨d,hd,?_⟩,by dsimp;group⟩
    have hh := congrArg (fun z => (q g)⁻¹*z*q g) he
    simpa only [map_mul,map_inv,MulEquiv.coe_toMonoidHom,MulAut.conj_apply,
      mul_assoc,inv_mul_cancel_left,inv_mul_cancel,mul_one] using hh

variable {ι : Type*} [Fintype ι] [Nonempty ι]
/-- Equal-weight replacement through Sylow preimages supplies condition (e)
of B.2.18 with the entire action kernel retained. -/
theorem maxJ_le_generated_of_sylow_preimage_cover
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (D : ι → Subgroup G)
    (h : HypothesesAD V R (fun i => elementaryAbelianMaxJ (D i)))
    (hD : ∀ i, IsSylowSubgroupIn (D i)
      (((D i).map (actionMap V)).comap (actionMap V)))
    (hQD : ∀ i, R ⊓ centralizer (V : Set G) ≤ D i)
    (hrank : ∀ i, twoRank (D i) = twoRank R)
    (hcover : ∀ A ∈ elementaryAbelianMaxSubgroups R, A.map (actionMap V) ≠ ⊥ →
      ∃ E : Set (Subgroup (G ⧸ centralizer (V : Set G))),
        sSup E = A.map (actionMap V) ∧
        ∀ B ∈ E,
          IsElementaryTwo B ∧
          EqualWeightLE (NormalElementaryQuotient.representation V (actionMap V)
            (QuotientGroup.mk'_surjective _) (actionMap_ker V)) B (A.map (actionMap V)) ∧
          ∃ i, ∃ g ∈ pResidual 2 G,
            B ≤ ((D i).map (MulAut.conj g).toMonoidHom).map (actionMap V)) :
    elementaryAbelianMaxJ R ≤ ⨆ i, elementaryAbelianMaxJ (D i) := by
  classical
  let q := actionMap V
  let Q := R ⊓ centralizer (V : Set G)
  let I := ⨆ i, elementaryAbelianMaxJ (D i)
  have hQI : Q ≤ normalizer (I : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    change I.map (MulAut.conj g).toMonoidHom = I
    dsimp only [I]
    rw [Subgroup.map_iSup]
    congr 1
    funext i
    exact mem_normalizer_iff_map_conj_eq.mp
      (normalizer_le_normalizer_elementaryAbelianMaxJ (D i) ((D i).le_normalizer (hQD i hg)))
  have hLI : pResidual 2 G ≤ normalizer (I : Set G) :=
    (residual_le_generated_sup_centralizer V R _ h).trans
      (sup_le I.le_normalizer hQI)
  have hconj (i : ι) (g : G) (hg : g ∈ pResidual 2 G) :
      elementaryAbelianMaxJ ((D i).map (MulAut.conj g).toMonoidHom) ≤ I := by
    rw [elementaryAbelianMaxJ_map_equiv]
    exact (map_mono (le_iSup (fun j => elementaryAbelianMaxJ (D j)) i)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (hLI hg))
  have horderD (i : ι) : elementaryAbelianMaxOrder (D i) = elementaryAbelianMaxOrder R := by
    rw [maxOrder_eq_two_pow_rank, maxOrder_eq_two_pow_rank, hrank i]
  have horderQ : elementaryAbelianMaxOrder Q = elementaryAbelianMaxOrder R := by
    rw [maxOrder_eq_two_pow_rank, maxOrder_eq_two_pow_rank,
      (centralizer_rank_and_alpha V R h.V_le_R h.no_strong).1]
  have hJQI : elementaryAbelianMaxJ Q ≤ I := by
    let i : ι := Classical.choice inferInstance
    exact ((elementaryAbelianMaxOrder_le_and_j_le_of_eq Q (D i) (hQD i)).2
      (horderQ.trans (horderD i).symm)).trans
      (le_iSup (fun j => elementaryAbelianMaxJ (D j)) i)
  apply sSup_le
  intro A hA
  have hAK : A ⊓ q.ker ≤ I := by
    let C := V ⊔ (A ⊓ centralizer (V : Set G))
    have hC := maximal_replacement V R A h.V_le_R h.no_strong hA
    have hCQ : C ≤ Q := le_inf hC.1 (sup_le V.le_centralizer inf_le_right)
    have hCJ : C ≤ elementaryAbelianMaxJ Q :=
      max_le_J_of_order R Q C hC hCQ horderQ
    rw [actionMap_ker V]
    exact (show A ⊓ centralizer (V : Set G) ≤ C from le_sup_right).trans (hCJ.trans hJQI)
  by_cases hz : A.map q = ⊥
  · have hAk := (map_eq_bot_iff A).mp hz
    exact (le_inf le_rfl hAk).trans hAK
  obtain ⟨E, hE, hparts⟩ := hcover A hA hz
  have hmap : A.map q ≤ (A ⊓ I).map q := by
    rw [← hE]
    apply sSup_le
    intro B hB
    obtain ⟨hBe, hBA, i, g, hg, hBg⟩ := hparts B hB
    let B₀ := A ⊓ B.comap q
    let C := B₀ ⊔ (V ⊓ centralizer (B₀ : Set G))
    obtain ⟨hC, hCmap⟩ := lemma_B_2_8_construct V q
      (QuotientGroup.mk'_surjective _) (actionMap_ker V) R h.V_le_R A hA B hBe hBA
    have hCD : C ≤ ((((D i).map (MulAut.conj g).toMonoidHom).map q).comap q) := by
      have hh : C.map q ≤ ((D i).map (MulAut.conj g).toMonoidHom).map q := hCmap ▸ hBg
      exact map_le_iff_le_comap.mp hh
    have hSyl : IsSylowSubgroupIn ((D i).map (MulAut.conj g).toMonoidHom)
        ((((D i).map (MulAut.conj g).toMonoidHom).map q).comap q) := by
      have hh := (Chapter1.IsSylowIn.map_iff (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).mpr (hD i)
      rw [map_preimage_conjugate] at hh
      exact hh
    have hCI : C ≤ I := by
      apply maximum_le_of_sylow_and_residual_normalizes R _ _ I C hSyl hC hCD
        ?_ (hconj i g hg) hLI
      rw [maxOrder_eq_two_pow_rank,twoRank_map_equiv,←maxOrder_eq_two_pow_rank]
      exact horderD i
    intro b hb
    obtain ⟨a, ha, rfl⟩ := hBA.1 hb
    exact ⟨a, ⟨ha, hCI (mem_sup_left (show a ∈ B₀ from ⟨ha, hb⟩))⟩, rfl⟩
  intro a ha
  obtain ⟨b, hb, he⟩ := hmap (mem_map_of_mem q ha)
  have hab : a * b⁻¹ ∈ A ⊓ q.ker := by
    refine ⟨A.mul_mem ha (A.inv_mem hb.1), ?_⟩
    change q (a * b⁻¹) = 1
    rw [map_mul, map_inv, he, mul_inv_cancel]
  simpa only [inv_mul_cancel_right] using I.mul_mem (hAK hab) hb.2

/-- B.2.19 for Sylow subgroups of the actual full inverse images. -/
theorem baumann_of_sylow_preimage_cover
    (V R : Subgroup G) [V.Normal] [IsElementaryAbelian 2 V]
    (D : ι → Subgroup G)
    (h : HypothesesAD V R (fun i => elementaryAbelianMaxJ (D i)))
    (hD : ∀ i, IsSylowSubgroupIn (D i)
      (((D i).map (actionMap V)).comap (actionMap V)))
    (hQD : ∀ i, R ⊓ centralizer (V : Set G) ≤ D i)
    (hrank : ∀ i, twoRank (D i) = twoRank R)
    (hcover : ∀ A ∈ elementaryAbelianMaxSubgroups R, A.map (actionMap V) ≠ ⊥ →
      ∃ E : Set (Subgroup (G ⧸ centralizer (V : Set G))),
        sSup E = A.map (actionMap V) ∧
        ∀ B ∈ E,
          IsElementaryTwo B ∧
          EqualWeightLE (NormalElementaryQuotient.representation V (actionMap V)
            (QuotientGroup.mk'_surjective _) (actionMap_ker V)) B (A.map (actionMap V)) ∧
          ∃ i, ∃ g ∈ pResidual 2 G,
            B ≤ ((D i).map (MulAut.conj g).toMonoidHom).map (actionMap V))
    (hQ : IsSylowSubgroupIn (R ⊓ centralizer (V : Set G))
      ((pResidual 2 G ⊔ R) ⊓ centralizer (V : Set G))) :
    (pCore 2 (pResidual 2 G)).map (pResidual 2 G).subtype ≤ baumann R ∧
      thompsonAlpha R =
        (thompsonAlpha R ⊓ centralizer (pResidual 2 G : Set G)) ⊔
          (V ⊓ centralizer (elementaryAbelianMaxJ R : Set G)) ∧
      IsSylowSubgroupIn (baumann R ⊓ centralizer (V : Set G))
        ((pResidual 2 G ⊔ baumann R) ⊓ centralizer (V : Set G)) ∧
      (IsSylowSubgroupIn ((baumann R).map (actionMap V))
          ((pResidual 2 G).map (actionMap V) ⊔ (baumann R).map (actionMap V)) →
        IsSylowSubgroupIn (baumann R) (pResidual 2 G ⊔ baumann R)) := by
  have hJI := maxJ_le_generated_of_sylow_preimage_cover V R D h hD hQD hrank hcover
  obtain ⟨hc, ha, hs⟩ := lemma_B_2_18 V R _ h hJI
  exact ⟨hc, ha, (hs hQ).1, (hs hQ).2⟩

end CFSG.Quasithin.ChapterB.BaumannArgument
