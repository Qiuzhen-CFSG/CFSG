module
public import CFSG.Quasithin.Chapter12.Section06.Nonsingular.LocalThompson
public import CFSG.Quasithin.Chapter12.Section06.NaturalSource.FullAction
public import CFSG.Quasithin.ChapterB.Section03.Offenders.StrongNonsingular
public import Theory.Representation.NormalElementaryQuotient.StrongReplacement
public import Theory.GroupTheory.ElementaryThompsonPrimeRank
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Equal two-rank at the original fixed-free nonsingular point

Assume C_V(L)=1 and that the original T_v is Sylow in M_v. A maximum
elementary subgroup of T either has a maximum replacement centralizing V,
or induces a strong offender on the original six-space. B.3.2 supplies a
nonsingular vector fixed by that offender. Nonsingular local centralizers
are L-conjugate, so the given relative Sylow position bounds its order by
the maximum elementary order in T_v. Hence m_2(T_v)=m_2(T).

The proof retains V and the full LT action, including its centralizer
kernel, and uses the original orthogonal coordinates. This is the rank
comparison used to prove the fixed-free branch of source 12.6.15.
Source: Aschbacher--Smith, B.2.4, B.3.2 and 12.6.6--15, combined manuscript
of 1 March 2004, printed pp.75--76, 83--84 and 824--826.
-/

public section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative

namespace CFSG.Quasithin.Chapter12.Section06
variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass}
variable {T : Sylow 2 G} {L V : Subgroup G} [IsElementaryAbelian 2 V]

private theorem nonsingular_elementary_card_le
    (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G))
    (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G)))
    (A : Subgroup G) (hA : IsElementaryAbelian 2 A)
    (u : V) (hu : D.Nonsingular u) (hAu : A ≤ LT T L ⊓ Gv (u : G)) :
    Nat.card A ≤ 2 ^ primeRank 2 (Tv T (v : G)) := by
  obtain ⟨l,hBl,_⟩ := D.nonsingular_local_pair_conjugate H.chosen hTV v u hv hu
  let e := MulAut.conj (l : G)
  let A' := A.map e.symm.toMonoidHom
  have hback : A'.map e.toMonoidHom = A := by
    rw [map_map]
    have he : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      exact e.apply_symm_apply x
    rw [he,map_id]
  have hAB : A' ≤ LT T L ⊓ Gv (v : G) := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hback,hBl]
    exact hAu
  have hAM : A' ≤ Mv L (v : G) := hAB.trans
    (inf_le_inf (sup_le L.le_normalizer H.chosen.sylow_normalizes_component) le_rfl)
  let : IsElementaryAbelian 2 A' := hA.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 (A'.subgroupOf (Mv L (v : G))) := IsElementaryAbelian.subgroupOf hAM
  have hc := (primeRank_le_iff_elementary_card_le (p := 2) (Mv L (v : G))).mp le_rfl
    (A'.subgroupOf (Mv L (v : G))) inferInstance
  obtain ⟨P,hP⟩ := hs
  let c : P ≃* Tv T (v : G) :=
    (equivMapOfInjective (P : Subgroup (Mv L (v : G))) (Mv L (v : G)).subtype
      (Mv L (v : G)).subtype_injective).trans (MulEquiv.subgroupCongr hP)
  rwa [Nat.card_congr (subgroupOfEquivOfLe hAM).toEquiv,
    card_map_of_injective e.symm.injective,P.primeRank_eq,primeRank_equiv 2 c] at hc

theorem SourceHypothesis.nonsingular_two_rank_eq_of_fixed_free
    (H : SourceHypothesis K T L V)
    (D : OrthogonalMarking L V H.chosen.normalizes)
    (hTV : (T : Subgroup G) ≤ normalizer (V : Set G)) (hz : ZV L V = ⊥)
    (v : V) (hv : D.Nonsingular v)
    (hs : Chapter1.IsSylowIn 2 (Tv T (v : G)) (Mv L (v : G))) :
    primeRank 2 (Tv T (v : G)) = primeRank 2 T := by
  let J := LT T L
  let W := V.subgroupOf J
  let P := (T : Subgroup G).subgroupOf J
  have hVJ : V ≤ J := H.chosen.le_sylow.trans le_sup_right
  have hTJ : (T : Subgroup G) ≤ J := le_sup_right
  have hn : J ≤ normalizer (V : Set G) := sup_le H.chosen.normalizes hTV
  let : W.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.subgroupOf hVJ
  let a : W ≃* V := subgroupOfEquivOfLe hVJ
  let c : Additive W ≃ₗ[ZMod 2] Additive V :=
    { a.toAdditive with map_smul' := ZMod.map_smul a.toAdditive }
  let E := c.trans (D.fullLinearCoordinates hz)
  obtain ⟨f,_,ha,hk⟩ := D.exists_full_permutation_action H.chosen hz hTV
  let q := f.rangeRestrict
  have hker : q.ker = centralizer (W : Set J) := by
    rw [MonoidHom.ker_rangeRestrict,hk]
    ext j
    constructor
    · intro h x hx
      exact Subtype.ext (h x.val hx)
    · intro h x hx
      exact congrArg J.subtype (h ⟨x,hVJ hx⟩ hx)
  let ρ := NormalElementaryQuotient.representation W q f.rangeRestrict_surjective hker
  let σ := BinaryPermutation.naturalRepresentation (Fin 8)
  have hE (b : f.range) (x : Additive W) : E (ρ b x) = σ b.val (E x) := by
    obtain ⟨j,rfl⟩ := f.rangeRestrict_surjective b
    have hh : a (ρ (q j) x).toMul =
        V.normalizerMonoidHom ⟨j.val,hn j.property⟩ (a x.toMul) := by
      apply Subtype.ext
      exact congrArg J.subtype
        (NormalElementaryQuotient.representation_apply W q f.rangeRestrict_surjective hker j x)
    change (D.fullCoordinates hz (a (ρ (q j) x).toMul)).toAdd =
      σ (f j) (D.fullCoordinates hz (a x.toMul)).toAdd
    rw [hh]
    exact ha j (a x.toMul)
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty P
  have hcard : Nat.card A = 2 ^ primeRank 2 T := by
    rw [elementaryAbelianMaxSubgroups_card_eq P A hA,
      elementaryAbelianMaxOrder_eq_two_pow_primeRank,
      primeRank_equiv 2 (subgroupOfEquivOfLe hTJ)]
  have hb : Nat.card A ≤ 2 ^ primeRank 2 (Tv T (v : G)) := by
    rcases NormalElementaryQuotient.maxElementary_strong_or_centralizer W q
      f.rangeRestrict_surjective hker P A (comap_mono H.chosen.le_sylow) hA with hstrong | ⟨B,hB,hBC⟩
    · have hmodel : IsStrongOffender σ ((A.map q).map f.range.subtype) := by
        have hoff : IsOffender ρ (A.map q) := ⟨hstrong.1,hstrong.2.le⟩
        refine ⟨(hoff.map_equivariant ρ σ f.range.subtype f.range.subtype_injective E hE).1,?_⟩
        rw [←fixedCodim_map_equivariant ρ σ f.range.subtype E hE,
          rank_map_injective f.range.subtype f.range.subtype_injective]
        exact hstrong.2
      have hmap : (A.map q).map f.range.subtype = A.map f := map_map _ _ _
      rw [hmap] at hmodel
      obtain ⟨w,hw,hfix⟩ := ChapterB.Offenders.strong_natural_eight_fixes_nonsingular (A.map f) hmodel
      let x := E.symm w
      let u : V := a x.toMul
      have hu : D.Nonsingular u := by
        apply (D.fullCoordinates_nonsingular_iff hz u).mp
        change BinaryPermutation.TerminalOrthogonal.Eight.form (E (E.symm w)) ≠ 0
        rwa [E.apply_symm_apply]
      have hAu : A.map J.subtype ≤ LT T L ⊓ Gv (u : G) := by
        rintro _ ⟨j,hj,rfl⟩
        refine ⟨j.property,?_⟩
        apply mem_centralizer_singleton_iff.mpr
        have hx : ρ (q j) x = x := by
          apply E.injective
          rw [hE,E.apply_symm_apply]
          exact hfix (f j) (mem_map_of_mem f hj)
        have he := NormalElementaryQuotient.representation_apply W q f.rangeRestrict_surjective hker j x
        have he' := (congrArg (fun z : Additive W => J.subtype (z.toMul : J)) hx).symm.trans
          (congrArg J.subtype he)
        exact (mul_inv_eq_iff_eq_mul.mp he'.symm)
      have hc := nonsingular_elementary_card_le H D hTV v hv hs (A.map J.subtype)
        (hA.2.1.map J.subtype) u hu hAu
      rwa [card_map_of_injective J.subtype_injective] at hc
    · have hBT : B.map J.subtype ≤ (T : Subgroup G) := by
        exact (map_mono (f := J.subtype) hB.1).trans_eq
          (map_subgroupOf_eq_of_le hTJ)
      have hBV : B.map J.subtype ≤ centralizer (V : Set G) := by
        rintro _ ⟨j,hj,rfl⟩ x hx
        exact congrArg J.subtype (hBC hj ⟨x,hVJ hx⟩ hx)
      have hBv : B.map J.subtype ≤ Tv T (v : G) := le_inf hBT
        (hBV.trans (centralizer_le (Set.singleton_subset_iff.mpr v.property)))
      let : IsElementaryAbelian 2 B := hB.2.1
      let : IsElementaryAbelian 2 (B.map J.subtype) := IsElementaryAbelian.map J.subtype
      let : IsElementaryAbelian 2 ((B.map J.subtype).subgroupOf (Tv T (v : G))) :=
        IsElementaryAbelian.subgroupOf hBv
      have hc := (primeRank_le_iff_elementary_card_le (p := 2) (Tv T (v : G))).mp le_rfl
        ((B.map J.subtype).subgroupOf (Tv T (v : G))) inferInstance
      rwa [Nat.card_congr (subgroupOfEquivOfLe hBv).toEquiv,
        card_map_of_injective J.subtype_injective,
        elementaryAbelianMaxSubgroups_card_eq P B hB,
        ←elementaryAbelianMaxSubgroups_card_eq P A hA] at hc
  rw [hcard] at hb
  exact le_antisymm
    (Theory.GroupTheory.primeRank_le_of_injective 2
      (inclusion (show Tv T (v : G) ≤ (T : Subgroup G) from inf_le_left))
      (inclusion_injective _))
    ((Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hb)

end CFSG.Quasithin.Chapter12.Section06
