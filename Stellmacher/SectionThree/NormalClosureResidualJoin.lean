module
public import Stellmacher.SectionThree.LemmaThreeFour
public import Stellmacher.SectionThree.LemmaThreeSeven

/-!
# The normal closure of a normal Sylow-image subgroup

For a solvable member P of Stellmacher's P-set, let q be a finite quotient
map and let J be normal in the image of the distinguished Sylow subgroup S.
If the lift of J inside S is not contained in the 2-core of P, then the
normal closure of J is the join of J and the image of the 2-residual of P.
This supplies the residual-image identification used in (8.1)(b) of
Stellmacher, Journal of Algebra 190 (1997), following (3.4).

The lifted subgroup T is normal in S. Lemma (3.4) gives [O²(P),T]=O²(P),
so mapping commutators into the normal closure of J contains the residual
image there. Conversely the residual supplements S, and both images
normalize their join with J. That join is therefore normal in the quotient,
which gives the reverse containment. The quotient map need not be faithful.
-/

namespace Stellmacher.SectionThree

public theorem normalClosure_eq_residual_sup_of_normal_sylow_image
    {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    (S : Subgroup G) (h : Hypotheses G S)
    (P : Subgroup G) (hP : P ∈ PSet (⊤ : Subgroup G) S)
    (hsolv : Group.IsSolvable P) (q : P →* X) (hq : Function.Surjective q)
    (J : Subgroup X) (hJS : J ≤ (S.subgroupOf P).map q)
    (hJn : (J.subgroupOf ((S.subgroupOf P).map q)).Normal)
    (hnot : ¬ S ⊓ (J.comap q).map P.subtype ≤ twoCoreAmbient P) :
    Subgroup.normalClosure (J : Set X) =
      ((twoResidualAmbient P).subgroupOf P).map q ⊔ J := by
  classical
  have hSP : S ≤ P := by
    obtain ⟨U, hU⟩ := hP.1.2.1
    rw [← hU]
    exact Subgroup.map_subtype_le _
  let SP := S.subgroupOf P
  let R := twoResidualSubgroup P
  let L := SP ⊓ J.comap q
  let T := L.map P.subtype
  have hSPmap : SP.map P.subtype = S := Subgroup.map_subgroupOf_eq_of_le hSP
  have hTmap : T = S ⊓ (J.comap q).map P.subtype := by
    change (SP ⊓ J.comap q).map P.subtype = _
    rw [Subgroup.map_inf _ _ _ P.subtype_injective, hSPmap]
  have hTS : T ≤ S := hTmap ▸ inf_le_left
  have hnormJ : SP.map q ≤ Subgroup.normalizer J :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJS).mp hJn
  have hnormL : SP ≤ Subgroup.normalizer L := by
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs l hl
    refine ⟨SP.mul_mem (SP.mul_mem hs hl.1) (SP.inv_mem hs), ?_⟩
    change q (s * l * s⁻¹) ∈ J
    simpa only [map_mul, map_inv] using
      (Subgroup.le_normalizer_iff.mp hnormJ (q s) (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
        (q l) hl.2)
  have hTnormal : (T.subgroupOf S).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hTS).mpr
    apply Subgroup.le_normalizer_iff.mpr
    intro s hs t ht
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp ht
    let sP : P := ⟨s, hSP hs⟩
    exact Subgroup.mem_map.mpr ⟨sP * l * sP⁻¹,
      Subgroup.le_normalizer_iff.mp hnormL sP hs l hl, rfl⟩
  have hcommT : ⁅twoResidualAmbient P, T⁆ = twoResidualAmbient P := by
    rcases lemma_three_four S h P hP T ⟨hTS, hTnormal⟩ hsolv with hc | hc
    · exact False.elim (hnot (hTmap ▸ hc))
    · exact hc
  have hcomm : ⁅R, L⁆ = R := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_commutator]
    exact hcommT
  let C := Subgroup.normalClosure (J : Set X)
  have hLC : L.map q ≤ C :=
    (Subgroup.map_le_iff_le_comap.mpr inf_le_right).trans Subgroup.le_normalClosure
  have hRC : R.map q ≤ C := by
    have hm := congrArg (Subgroup.map q) hcomm
    rw [Subgroup.map_commutator] at hm
    rw [← hm]
    exact (Subgroup.commutator_mono le_rfl hLC).trans
      (Subgroup.commutator_le_right _ C)
  have hRn : R.Normal := by
    unfold R twoResidualSubgroup
    rw [sInf_eq_iInf]
    exact Subgroup.normal_iInf_normal
      (fun N => Subgroup.normal_iInf_normal (fun hN => hN.1))
  let : R.Normal := hRn
  let : (R.map q).Normal := Subgroup.Normal.map hRn q hq
  have hgen : R ⊔ SP = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, hSPmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact twoResidual_sup_sylowImage hP.1.2.1
  have hgenq : R.map q ⊔ SP.map q = ⊤ := by
    rw [← Subgroup.map_sup, hgen, ← MonoidHom.range_eq_map, q.range_eq_top_of_surjective hq]
  let K := R.map q ⊔ J
  have hKnormal : K.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hgenq]
    refine sup_le (le_sup_left.trans K.le_normalizer) ?_
    apply le_trans (le_inf (show SP.map q ≤ Subgroup.normalizer (R.map q) by
      rw [Subgroup.normalizer_eq_top]; exact le_top) hnormJ)
    exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup _ _
  let : K.Normal := hKnormal
  have hRK : ((twoResidualAmbient P).subgroupOf P) = R := by
    apply Subgroup.map_injective P.subtype_injective
    change ((R.map P.subtype).subgroupOf P).map P.subtype = R.map P.subtype
    exact Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_subtype_le R)
  rw [hRK]
  apply le_antisymm
  · exact Subgroup.normalClosure_le_normal (show (J : Set X) ⊆ K from fun _ hx =>
      (show J ≤ K from le_sup_right) hx)
  · exact sup_le hRC Subgroup.le_normalClosure

end Stellmacher.SectionThree

