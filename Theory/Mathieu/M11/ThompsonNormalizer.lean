module
public import Theory.GroupTheory.SemidihedralThompson
public import Theory.Mathieu.M11.Properties.FourNormalizer
public import Theory.Mathieu.M11.Properties.SylowOvergroups
public import Theory.GroupTheory.SpecificGroups.DihedralAut
public import Theory.GroupTheory.ElementaryThompsonRelative
public import Theory.GroupTheory.SylowNormalJoinIntersection
public import Theory.GroupTheory.PPerfectHom
public import Theory.GroupTheory.PResidual.PerfectCover

/-!
# The M11 Thompson normalizer and its residual in an overgroup

The actual semidihedral Sylow has dihedral Thompson subgroup of order
eight. Its automorphism group is a two-group, and the centralizer of a
four-subgroup controls the conjugation kernel. Therefore its normalizer
in M11 is exactly the supplied Sylow subgroup.

A normal M11 is a direct factor because it is centerless and every
automorphism is inner. The elementary Thompson product formula identifies
the image of J(S) under the actual projection. The normalizer's image is
therefore a two-group, so its two-residual centralizes the M11 factor.

Source: Aschbacher--Smith 15.1.22(6), printed p.1100. The result retains
the literal normalizer and its residual embedding, without source-specific
ambient hypotheses.
-/

public section
open Subgroup Stellmacher
namespace Sporadic.Mathieu

/-- Every specified Sylow two-subgroup of M11 has dihedral Thompson subgroup of order eight. -/
theorem m11_thompson_dihedral (P : Sylow 2 M11) :
    Nonempty (elementaryAbelianMaxJ (P : Subgroup M11) ≃* DihedralGroup 4) := by
  obtain ⟨Q,a,b,ha,hb,hab,hgen⟩ := m11_exists_semidihedral_sylow
  have hc : Nat.card Q = 16 := by rw [Q.card_eq_multiplicity,m11_order]; decide +kernel
  obtain ⟨e⟩ := Semidihedral.thompson_sixteen a b hc ha hb hab hgen
  let f := Q.equiv P
  have hmap : (elementaryAbelianMaxJ (⊤ : Subgroup Q)).map f.toMonoidHom =
      elementaryAbelianMaxJ (⊤ : Subgroup P) := by
    rw [←elementaryAbelianMaxJ_map_injective _ f.injective,map_top_of_surjective _ f.surjective]
  let eJ := (f.subgroupMap (elementaryAbelianMaxJ (⊤ : Subgroup Q))).trans
    (MulEquiv.subgroupCongr hmap)
  have hP : (elementaryAbelianMaxJ (⊤ : Subgroup P)).map (P : Subgroup M11).subtype =
      elementaryAbelianMaxJ (P : Subgroup M11) := by
    rw [←elementaryAbelianMaxJ_map_injective _ (P : Subgroup M11).subtype_injective,
      ←MonoidHom.range_eq_map,range_subtype]
  let eA := ((elementaryAbelianMaxJ (⊤ : Subgroup P)).equivMapOfInjective
    (P : Subgroup M11).subtype (P : Subgroup M11).subtype_injective).trans
      (MulEquiv.subgroupCongr hP)
  exact ⟨eA.symm.trans (eJ.symm.trans e)⟩

/-- The actual Thompson normalizer has two-group kernel and automorphism image. -/
theorem m11_thompson_normalizer_two (P : Sylow 2 M11) :
    IsPGroup 2 (normalizer (elementaryAbelianMaxJ (P : Subgroup M11) : Set M11)) := by
  let J := elementaryAbelianMaxJ (P : Subgroup M11)
  obtain ⟨e⟩ := m11_thompson_dihedral P
  obtain ⟨E,hE⟩ := elementaryAbelianMaxSubgroups_nonempty J
  obtain ⟨hEJ,helem,hcard⟩ := (dihedral_maxFamily_iff J (by decide : 2≤2) e E).mp hE
  let := helem
  let : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  let : IsKleinFour E := ⟨hcard,IsElementaryAbelian.exponent_eq_prime⟩
  have hC : IsPGroup 2 (centralizer (J : Set M11)) :=
    (IsElementaryAbelian.isPGroup 2 E).to_le
      ((centralizer_le hEJ).trans_eq (m11_four_centralizer E))
  have hAut : IsPGroup 2 (MulAut J) :=
    (DihedralGroup.isPGroup_mulAut_of_two_lt (by decide : 2<4)
      (IsPGroup.of_card (p:=2) (n:=3) (by rw [DihedralGroup.nat_card]; decide))).of_equiv
        (MulAut.congr e).symm
  have hk : IsPGroup 2 J.normalizerMonoidHom.ker := by
    rw [normalizerMonoidHom_ker]
    exact hC.comap_subtype
  have hh := (hAut.to_subgroup ⊤).comap_of_ker_isPGroup J.normalizerMonoidHom hk
  rw [comap_top] at hh
  exact hh.of_equiv topEquiv

/-- The Thompson normalizer is precisely the supplied Sylow subgroup. -/
theorem m11_thompson_normalizer_eq (P : Sylow 2 M11) :
    normalizer (elementaryAbelianMaxJ (P : Subgroup M11) : Set M11) = P := by
  exact P.is_maximal' (m11_thompson_normalizer_two P)
    ((P : Subgroup M11).le_normalizer.trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ _))
end Sporadic.Mathieu

namespace Sporadic.Mathieu
variable {G : Type*} [Group G] [Finite G]

/-- In any finite overgroup with a normal M11, the literal Thompson-normalizer
two-residual centralizes that M11 factor. -/
theorem normal_m11_thompson_residual (K : Subgroup G) [K.Normal]
    (e : K ≃* M11) (S : Sylow 2 G) :
    (pResidual 2 (normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G))).map
      (normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G)).subtype ≤
        centralizer (K : Set G) := by
  let C := centralizer (K : Set G)
  have hz : center K = ⊥ := by
    apply (center K).eq_bot_iff_card.mpr
    rw [Nat.card_congr (centerCongr e).toEquiv,m11_center_eq_bot,card_bot]
  have hi : MulAut.innerSubgroup K = ⊤ := MonoidHom.range_eq_top.mpr
    (fun α => by obtain ⟨k,hk⟩ := automorphism_inner_of_equiv_m11 e α; exact ⟨k,hk.symm⟩)
  have hgen : K ⊔ C = ⊤ := by
    rw [←MulAut.conjNormal_comap_innerSubgroup,hi,comap_top]
  have hd : Disjoint K C := by
    apply disjoint_def.mpr
    intro x hxK hxC
    have hx : (⟨x,hxK⟩ : K) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      exact Subtype.ext (hxC k k.property)
    have hh : (⟨x,hxK⟩ : K) = 1 := mem_bot.mp (hz ▸ hx)
    exact congrArg Subtype.val hh
  let A := (S : Subgroup G) ⊓ K
  let B := (S : Subgroup G) ⊓ C
  have hS : (S : Subgroup G) = A ⊔ B := by
    have hh := S.inf_sup_eq_sup_inf_normal K C
    rwa [hgen,inf_top_eq] at hh
  have hAB : Disjoint A B := hd.mono inf_le_right inf_le_right
  have hAC : A ≤ centralizer (B : Set G) := inf_le_right.trans
    (le_centralizer_iff.mpr (show B ≤ centralizer (K : Set G) from inf_le_right))
  have hJ : elementaryAbelianMaxJ (S : Subgroup G) =
      elementaryAbelianMaxJ A ⊔ elementaryAbelianMaxJ B := by
    rw [hS]
    exact elementaryAbelianMaxJ_sup_of_disjoint_of_commuting A B hAB hAC
  obtain ⟨q,hq,hqK⟩ := exists_normal_m11_projection K e
  have hqC (c : G) (hc : c ∈ C) : q c = 1 := by
    apply mem_bot.mp
    rw [←m11_center_eq_bot]
    apply mem_center_iff.mpr
    intro y
    obtain ⟨k,rfl⟩ := e.surjective y
    have hh := congrArg q (hc k k.property)
    simpa only [map_mul,hqK] using hh
  obtain ⟨P,hP⟩ := S.exists_sylow_map_eq_inf_of_normal K
  change (P : Subgroup K).map K.subtype = A at hP
  let Q := P.mapSurjective (f:=e.toMonoidHom) e.surjective
  have hJAq : (elementaryAbelianMaxJ A).map q = elementaryAbelianMaxJ (Q : Subgroup M11) := by
    rw [←hP,elementaryAbelianMaxJ_map_injective _ K.subtype_injective,map_map]
    have he : q.comp K.subtype = e.toMonoidHom := MonoidHom.ext hqK
    rw [he,←elementaryAbelianMaxJ_map_injective _ e.injective]
    rfl
  have hJBq : (elementaryAbelianMaxJ B).map q = ⊥ := by
    apply eq_bot_iff.mpr
    rintro _ ⟨x,hx,rfl⟩
    exact mem_bot.mpr (hqC x ((show elementaryAbelianMaxJ B ≤ B from
      sSup_le fun _ hE => hE.1) hx).2)
  have hJq : (elementaryAbelianMaxJ (S : Subgroup G)).map q =
      elementaryAbelianMaxJ (Q : Subgroup M11) := by rw [hJ,Subgroup.map_sup,hJAq,hJBq,sup_bot_eq]
  let N := normalizer (elementaryAbelianMaxJ (S : Subgroup G) : Set G)
  let D := normalizer (elementaryAbelianMaxJ (Q : Subgroup M11) : Set M11)
  have hnq : ∀ x : N, q (x : G) ∈ D := by
    intro x
    have hh := (elementaryAbelianMaxJ (S : Subgroup G)).le_normalizer_map q
      (mem_map_of_mem q x.property)
    rwa [hJq] at hh
  let f : N →* D := (q.comp N.subtype).codRestrict D hnq
  have hzero := (isPPerfect_pResidual (G:=N) 2).hom_eq_one_of_isPGroup
    (m11_thompson_normalizer_two Q) (f.comp (pResidual 2 N).subtype)
  rintro _ ⟨x,hx,rfl⟩ k hk
  have hqx : q (x : G) = 1 := congrArg (fun g : pResidual 2 N →* D =>
    (g ⟨x,hx⟩ : M11)) hzero
  have hkn : x.val*k*x.val⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance k hk x.val
  have he : (⟨x.val*k*x.val⁻¹,hkn⟩ : K) = ⟨k,hk⟩ := by
    apply e.injective
    rw [←hqK,←hqK]
    simp only [map_mul,map_inv,hqx,one_mul,mul_one,inv_one]
  exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
end Sporadic.Mathieu

