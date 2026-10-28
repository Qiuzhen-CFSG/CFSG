module

public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualFusion.ResidualNormalizer.Thompson.Solvable.EarlierWeakClosure
public import Theory.GroupTheory.SymmetricThreeTwoCoreGeneration
public import Theory.GroupTheory.GeneralizedFitting.StandardComponent

/-!
# Hyperplane control and the second clause of 14.7.31

The original natural action transports the plane-centralizer hypothesis to
all hyperplanes of all conjugates of V. A conjugate outside the two-core of
an S₃ extension meets the core in a hyperplane. Its noncentral commutator
with B gives an intersection point, which natural transitivity moves to the
original flag point. The returning-point assumption then puts the whole
conjugate into the core. E.3.15 gives normality of the literal zero weak closure.

The earlier structural implication remains explicit, owned by
qt-d-1222-source; final source assembly belongs to qt-d-14775-source.
No weak-closure conclusion is assumed here.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Lemma 14.7.31, printed p.1055, PDF p.1072.
-/

public section

open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.EarlierWeakClosure
open Chapter12.Section08 Theory.GroupTheory
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

omit [Finite G] in
private theorem right_conjugate_mul (A : Subgroup G) (a b : G) :
    conjugate A (a * b) = conjugate (conjugate A a) b := by
  unfold conjugate
  rw [map_map]
  congr 1
  ext x
  simp [mul_assoc]

omit [Finite G] in
private theorem centralizer_conjugate (A : Subgroup G) (g : G) :
    centralizer (conjugate A g : Set G) = conjugate (centralizer (A : Set G)) g := by
  exact (map_centralizer_equiv (A : Set G) (MulAut.conj g⁻¹)).symm

omit [Finite G] in
private theorem normalizer_conjugate (A : Subgroup G) (g : G) :
    normalizer (conjugate A g : Set G) = conjugate (normalizer (A : Set G)) g :=
  (map_normalizer_eq_of_bijective A (MulAut.conj g⁻¹).bijective).symm

/-- Source (*) for each plane of each conjugate of the original V. -/
theorem hyperplane_centralizer
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (g : G) (A : Subgroup G) (hAV : A ≤ conjugate V g) (hcard : Nat.card A = 4) :
    centralizer (A : Set G) ≤ normalizer (conjugate V g : Set G) := by
  have hne : F.Vi 2 ≠ ⊥ := by
    intro he
    have hc := F.card 2 (by decide)
    rw [he, card_bot] at hc
    norm_num at hc
  have hbase : centralizer (F.Vi 2 : Set G) ≤ normalizer (V : Set G) :=
    (le_inf hplane le_rfl).trans
      (inf_centralizer_le_normalizer_of_trivial_intersections
        (h.seed_TI structural) hne (F.le_seed 2))
  have hpull : conjugate A g⁻¹ ≤ V := by
    have hm := map_mono (f := (MulAut.conj (g⁻¹)⁻¹).toMonoidHom) hAV
    change conjugate A g⁻¹ ≤ conjugate (conjugate V g) g⁻¹ at hm
    exact hm.trans_eq (by simpa only [inv_inv] using conjugate_conjugate_inv V g⁻¹)
  obtain ⟨l, hl, he⟩ := h.subspace_transitive (conjugate A g⁻¹) (F.Vi 2)
    hpull (F.le_seed 2) (by
      rw [conjugate, card_map_of_injective (MulAut.conj (g⁻¹)⁻¹).injective, hcard,
        F.card 2 (by decide)]
      norm_num)
  have hpullcentral : centralizer (conjugate A g⁻¹ : Set G) ≤ normalizer (V : Set G) := by
    have hc := map_mono (f := (MulAut.conj (l⁻¹)⁻¹).toMonoidHom) hbase
    change conjugate (centralizer (F.Vi 2 : Set G)) l⁻¹ ≤
      conjugate (normalizer (V : Set G)) l⁻¹ at hc
    rw [← centralizer_conjugate, ← normalizer_conjugate,
      (conjugate_eq_iff V l⁻¹).mpr (h.chosen.normalizes (L.inv_mem hl)),
      ← he] at hc
    have he : conjugate (conjugate (conjugate A g⁻¹) l) l⁻¹ = conjugate A g⁻¹ := by
      simpa only [inv_inv] using conjugate_conjugate_inv (conjugate A g⁻¹) l⁻¹
    rwa [he] at hc
  have hc := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hpullcentral
  change conjugate (centralizer (conjugate A g⁻¹ : Set G)) g ≤
    conjugate (normalizer (V : Set G)) g at hc
  rwa [← centralizer_conjugate, conjugate_conjugate_inv, ← normalizer_conjugate] at hc

/-- A nonzero intersection can be marked by the original flag point. -/
theorem returning_point
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (F : InvariantFlag T V 3) (B : Subgroup G) (g : G)
    (hne : conjugate V g ⊓ B ≠ ⊥) :
    ∃ k : G, conjugate V k = conjugate V g ∧ conjugate (F.Vi 1) k ≤ B := by
  let := h.chosen.elementary
  obtain ⟨x, hx⟩ := ne_bot_iff_exists_ne_one.mp hne
  have hx1 : (x : G) ≠ 1 := fun he => hx (Subtype.ext he)
  obtain ⟨v, hv, hvx⟩ := x.property.1
  have hv1 : v ≠ 1 := by
    intro he
    subst v
    exact hx1 (hvx.symm.trans (map_one _))
  have hv2 : v ^ 2 = 1 := by
    exact elemPow_eq_one_of_isElementaryAbelian v hv
  have hcv : Nat.card (zpowers v) = Nat.card (F.Vi 1) := by
    rw [Nat.card_zpowers, orderOf_eq_prime hv2 hv1, F.card 1 (by decide), pow_one]
  obtain ⟨l, hl, he⟩ := h.subspace_transitive (F.Vi 1) (zpowers v)
    (F.le_seed 1) (zpowers_le.mpr hv) hcv.symm
  refine ⟨l * g, ?_, ?_⟩
  · rw [right_conjugate_mul, (conjugate_eq_iff V l).mpr (h.chosen.normalizes hl)]
  · rw [right_conjugate_mul, he]
    change (zpowers v).map (MulAut.conj g⁻¹).toMonoidHom ≤ B
    rw [MonoidHom.map_zpowers]
    exact zpowers_le.mpr (hvx.symm ▸ x.property.2)

/-- Every conjugate in the relative Sylow lies in the actual normal two-core. -/
theorem conjugate_le_core
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (A B : Subgroup G) (hBN : A ≤ normalizer (B : Set G))
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hcore : A ⊓ centralizer (B : Set G) = A.pCoreIn 2)
    (hreturn : ∀ g : G, conjugate (F.Vi 1) g ≤ B →
      conjugate F.U g ≤ A ⊓ centralizer (B : Set G))
    (g : G) (hg : conjugate V g ≤ A) : conjugate V g ≤ A.pCoreIn 2 := by
  let := h.chosen.elementary
  by_contra hout
  let C := conjugate V g
  have hC : IsPGroup 2 C := (IsElementaryAbelian.isPGroup 2 V).map _
  have hi := (core_hyperplane_and_generation A C hg hC hout e).1
  have hcardC : Nat.card C = 8 := by
    change Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) = 8
    rw [card_map_of_injective (MulAut.conj g⁻¹).injective, h.seed_card]
    norm_num
  have hcardD : Nat.card (C ⊓ A.pCoreIn 2 : Subgroup G) = 4 := by
    have he := ((C ⊓ A.pCoreIn 2).subgroupOf C).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (show C ⊓ A.pCoreIn 2 ≤ C from inf_le_left)).toEquiv] at he
    change (C ⊓ A.pCoreIn 2).relIndex C * _ = Nat.card C at he
    rw [hi, hcardC] at he
    omega
  have hBC : B ≤ normalizer (C : Set G) := by
    apply le_trans _ (hyperplane_centralizer h structural F hplane g
      (C ⊓ A.pCoreIn 2) inf_le_left hcardD)
    apply le_centralizer_iff.mpr
    exact inf_le_right.trans (hcore.symm.le.trans inf_le_right)
  have hCB : C ≤ normalizer (B : Set G) := hg.trans hBN
  have hcomm : ⁅C, B⁆ ≤ C ⊓ B :=
    le_inf (le_normalizer_iff_commutator_le_left.mp hBC)
      (le_normalizer_iff_commutator_le_right.mp hCB)
  have hinter : C ⊓ B ≠ ⊥ := by
    intro he
    have hc : C ≤ centralizer (B : Set G) :=
      commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp (he ▸ hcomm))
    exact hout (hcore ▸ le_inf hg hc)
  obtain ⟨k, hk, hp⟩ := returning_point h F B g hinter
  apply hout
  rw [← hk]
  exact (map_mono (le_conjugateSpanBy V F.H)).trans ((hreturn k hp).trans hcore.le)

/-- Clause (2), with the actual relative Sylow and corank-zero construction. -/
theorem clause_two
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3)
    (hplane : centralizer (F.Vi 2 : Set G) ≤ normalizer (L : Set G))
    (A R B : Subgroup G) (hSylow : Chapter1.IsSylowIn 2 R A)
    (hBA : B ≤ A) (hB : IsPReduced 2 (B.subgroupOf A))
    (e : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (hcore : A ⊓ centralizer (B : Set G) = A.pCoreIn 2)
    (hreturn : ∀ g : G, conjugate (F.Vi 1) g ≤ B →
      conjugate F.U g ≤ A ⊓ centralizer (B : Set G)) :
    ChapterE.indexedWeakClosure V R 0 ≤ A ∧
      A ≤ normalizer (ChapterE.indexedWeakClosure V R 0 : Set G) := by
  obtain ⟨S, hS⟩ := hSylow
  have hRA : R ≤ A := hS ▸ map_subtype_le _
  have hW : ChapterE.indexedWeakClosure V R 0 ≤ A.pCoreIn 2 := by
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro C hC
    obtain ⟨g, rfl, hg⟩ := (ChapterE.mem_gamma_zero_iff V R C).mp hC
    simpa only [conjugate, inv_inv] using conjugate_le_core h structural F hplane A B
      ((normal_subgroupOf_iff_le_normalizer hBA).mp hB.normal) e hcore hreturn
      g⁻¹ (by simpa only [conjugate, inv_inv] using hg.trans hRA)
  refine ⟨(ChapterE.indexedWeakClosure_le V R 0).trans hRA, ?_⟩
  have he := ChapterE.weakClosure_eq_in_two_overgroup V A S (A.pCoreIn 2) 0
    (isPGroup_pCoreIn 2 A) (pCoreIn_le 2 A) (by simpa only [hS] using hW)
  rw [hS] at he
  rw [he]
  exact (A.le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image A (pCore 2 A))).trans
    (ChapterE.normalizer_le_weakClosure_normalizer V (A.pCoreIn 2) 0)

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.EarlierWeakClosure
