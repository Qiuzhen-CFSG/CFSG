module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.JankoReduction.RankTwo
public import Theory.GroupTheory.PerfectRankTwoCoreInvolution
public import Theory.GroupTheory.PGroup.AbelianOmega
public import CFSG.Quasithin.ChapterC.Section05.NormalizerControl.NoncubicSource.EmbeddingSelection.Parameters

/-!
# The two-core of the actual residual image

In a quotient of two-rank at most two, a nontrivial two-core of the perfect
residual image gives an involution centralized by that image and its full
Sylow. If the Sylow center is cyclic, this involution is unique and hence
fixed by the original T and odd supplement. These groups and the residual
generate the enlarged local group containing K. The involution would then
be central in K/O₂(K), contradicting its trivial two-core.

The original residual quotient therefore identifies its image with
PSL₂(2ⁿ). The same argument excludes two-rank at most one. These results
supply the nonquasisimple and odd classical exclusions for the actual
moved component; no abstract model is substituted for its quotient.

Source: Aschbacher--Smith, 3.3.12, printed p.589, applied in the proof of
3.3.16, pp.590--591, and 11.2.3, pp.768--769.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c} {A : OddSupplement T}

omit [Finite G] in
private theorem quotient_action_preserves (K B : Subgroup G)
    (g : normalizer (K : Set G)) (hg : (g : G) ∈ normalizer (B : Set G)) :
    ((B.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map
      (coreQuotientAction K g).toMonoidHom =
        (B.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K)) := by
  have he : (B.subgroupOf K).map (K.normalizerMonoidHom g).toMonoidHom = B.subgroupOf K := by
    apply le_antisymm
    · rintro _ ⟨b,hb,rfl⟩
      exact (hg b).mp hb
    · intro b hb
      refine ⟨K.normalizerMonoidHom g⁻¹ b,?_,?_⟩
      · exact ((normalizer (B : Set G)).inv_mem hg b).mp hb
      · rw [map_inv K.normalizerMonoidHom]
        exact (K.normalizerMonoidHom g).apply_symm_apply b
  change ((B.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map
    (quotientAut (pCore 2 K) (K.normalizerMonoidHom g)).toMonoidHom = _
  have hq : (quotientAut (pCore 2 K) (K.normalizerMonoidHom g)).toMonoidHom.comp
      (QuotientGroup.mk' (pCore 2 K)) =
      (QuotientGroup.mk' (pCore 2 K)).comp (K.normalizerMonoidHom g).toMonoidHom := by
    ext x
    exact quotientAut_apply_mk _ _ x
  rw [map_map,hq,←map_map,he]

omit [Finite G] in
private theorem quotient_action_internal (K : Subgroup G) (k : K) :
    coreQuotientAction K ⟨k,K.le_normalizer k.property⟩ =
      MulAut.conj (QuotientGroup.mk' (pCore 2 K) k) := by
  ext x
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) x
  rw [coreQuotientAction,MonoidHom.comp_apply,quotientAut_apply_mk]
  change QuotientGroup.mk' (pCore 2 K) (k * x * k⁻¹) = _
  rw [map_mul,map_mul,map_inv,MulAut.conj_apply]


private theorem fixes_central_involution {Q : Type*} [Group Q] [Finite Q]
    (P : Subgroup Q) [IsCyclic (center P)] (z : P) (hz : z ∈ center P)
    (ho : orderOf z = 2) (a : MulAut Q) (ha : P.map a.toMonoidHom = P) : a z = z := by
  let e : P ≃* P := (a.subgroupMap P).trans (MulEquiv.subgroupCongr ha)
  let d := centerCongr e
  have he : d ⟨z,hz⟩ = ⟨z,hz⟩ := IsCyclic.eq_of_orderOf_eq_two
    ((d.orderOf_eq ⟨z,hz⟩).trans ((orderOf_coe ⟨z,hz⟩).symm.trans ho))
    ((orderOf_coe ⟨z,hz⟩).symm.trans ho)
  exact congrArg (fun x : center P => ((x : P) : Q)) he

namespace MovedComponent
variable (E : MovedComponent S f A)

/-- A cyclic Sylow center forces the literal residual image to have trivial two-core. -/
theorem residualImage_core_eq_bot_of_cyclic_center
    (hr : primeRank 2 (E.component ⧸ pCore 2 E.component) ≤ 2)
    (hc : IsCyclic (center E.quotientSylow)) : pCore 2 E.residualImage = ⊥ := by
  let Q := E.component ⧸ pCore 2 E.component
  let B := E.residualImage
  let : Group.IsPerfect B := by
    let := E.residualImage_local.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ E.quotientSylow from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  let : IsCyclic (center P) := hP.symm ▸ hc
  by_contra hcore
  obtain ⟨z,hzB,hz,hzC⟩ := exists_involution_centralized_by_perfect_sup_sylow
    P B hr (hP.symm ▸ E.quotientSylow_normalizes_residualImage) hcore
  have hzP : z ∈ (P : Subgroup Q) := by
    have hn : (P : Subgroup Q) ≤ normalizer (zpowers z : Set Q) := by
      intro p hp
      apply mem_normalizer_iff_map_conj_eq.mpr
      rw [MonoidHom.map_zpowers]
      have he : (MulAut.conj p) z = z := by
        rw [MulAut.conj_apply,mul_inv_eq_iff_eq_mul]
        exact mem_centralizer_singleton_iff.mp (hzC (mem_sup_right hp))
      change zpowers ((MulAut.conj p) z) = zpowers z
      rw [he]
    have ht : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hz]; rfl)
    have he := P.is_maximal' (ht.to_sup_of_normal_left' P.isPGroup' hn) le_sup_right
    exact he.le (mem_sup_left (mem_zpowers z))
  let zP : P := ⟨z,hzP⟩
  have hzc : zP ∈ center P := mem_center_iff.mpr (fun p =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hzC (mem_sup_right p.property))))
  have hzo : orderOf zP = 2 := (orderOf_coe zP).symm.trans hz
  let N : Subgroup G := ((MulAction.stabilizer (MulAut Q) z).comap
    (coreQuotientAction E.component)).map (normalizer (E.component : Set G)).subtype
  have lift_fixed (x : G) (hx : x ∈ normalizer (E.component : Set G))
      (hf : coreQuotientAction E.component ⟨x,hx⟩ z = z) : x ∈ N :=
    ⟨⟨x,hx⟩,hf,rfl⟩
  have hYN : f.Li E.index ≤ N := by
    intro y hy
    apply lift_fixed y (E.component.le_normalizer (E.contains.le hy))
    rw [quotient_action_internal E.component ⟨y,E.contains.le hy⟩]
    rw [MulAut.conj_apply,mul_inv_eq_iff_eq_mul]
    exact mem_centralizer_singleton_iff.mp (hzC (mem_sup_left
      (mem_map_of_mem (QuotientGroup.mk' (pCore 2 E.component)) hy)))
  have hTN : (T : Subgroup G) ≤ N := by
    intro t ht
    have htk := E.local_normalizes (mem_sup_left (mem_sup_right ht))
    apply lift_fixed t htk
    apply fixes_central_involution (P : Subgroup Q) zP hzc hzo
    rw [hP]
    exact quotient_action_preserves E.component (T : Subgroup G) _
      ((T : Subgroup G).le_normalizer ht)
  have hAN : A.subgroup ≤ N := by
    intro a ha
    apply lift_fixed a (E.local_normalizes (mem_sup_right ha))
    apply fixes_central_involution (P : Subgroup Q) zP hzc hzo
    rw [hP]
    exact E.oddAction_preserves_quotientSylow ⟨⟨a,ha⟩,rfl⟩
  have hKN : E.component ≤ N := E.normal_component.1.1.trans (sup_le (sup_le hYN hTN) hAN)
  have hcenter : z ∈ center Q := by
    apply mem_center_iff.mpr
    intro g
    obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 E.component) g
    obtain ⟨a,ha,hak⟩ := hKN k.property
    have he : a = ⟨k,E.component.le_normalizer k.property⟩ := Subtype.ext hak
    rw [he] at ha
    change coreQuotientAction E.component _ z = z at ha
    rw [quotient_action_internal,MulAut.conj_apply,mul_inv_eq_iff_eq_mul] at ha
    exact ha
  have hn : (zpowers z).Normal := by
    constructor
    intro x hx g
    have hxc := (zpowers_le.mpr hcenter : zpowers z ≤ center Q) hx
    simpa only [(mem_center_iff.mp hxc g),mul_inv_cancel_right] using hx
  have ht : IsPGroup 2 (zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers,hz]; rfl)
  have hle : zpowers z ≤ pCore 2 Q := le_sSup ⟨hn,ht⟩
  rw [pCore_quotient_pCore_eq_bot 2] at hle
  have he : z = 1 := mem_bot.mp (hle (mem_zpowers z))
  simp only [he,orderOf_one] at hz
  omega

/-- Transport through the original quotient map, retaining its exact two-core kernel. -/
theorem residualImage_isPSL_of_core_eq_bot
    (hc : pCore 2 E.residualImage = ⊥) :
    ClassicalGroup.IsPSL E.residualImage 2 (2 ^ S.field.degree) := by
  let B := (f.Li E.index).subgroupOf E.component
  let q := QuotientGroup.mk' (pCore 2 E.component)
  let r := q.subgroupMap B
  have hk : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  have he : r.ker = pCore 2 B := by
    have hh := r.comap_pCore_of_ker_isPGroup (q.subgroupMap_surjective B) hk
    rw [show pCore 2 (B.map q) = ⊥ from hc] at hh
    simpa only [MonoidHom.comap_bot] using hh
  let a : (B ⧸ pCore 2 B) ≃* E.residualImage :=
    (QuotientGroup.quotientMulEquivOfEq he.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective r (q.subgroupMap_surjective B))
  let b := subgroupOfEquivOfLe E.contains.le
  let d : (B ⧸ pCore 2 B) ≃* (f.Li E.index ⧸ pCore 2 (f.Li E.index)) :=
    QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  exact ((invariantFlag_geometry D S f).2.2.model E.index).of_mulEquiv (a.symm.trans d)

/-- The moved-component quotient has two-rank at least two. -/
theorem quotient_rank_two_ge_two :
    2 ≤ primeRank 2 (E.component ⧸ pCore 2 E.component) := by
  by_contra hsmall
  have hr : primeRank 2 (E.component ⧸ pCore 2 E.component) ≤ 1 := by omega
  obtain ⟨P,hP⟩ := E.quotientSylow_isSylow
  have hpr : primeRank 2 P ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 (P : Subgroup _).subtype Subtype.val_injective).trans hr
  have hzr : primeRank 2 (center P) ≤ 1 :=
    (Theory.GroupTheory.primeRank_le_of_injective 2 (center P).subtype Subtype.val_injective).trans hpr
  have hcyc : IsCyclic (center P) := by
    apply (P.isPGroup'.to_subgroup (center P)).isCyclic_of_card_omega_one_le_two
    simpa only [pow_one] using
      (primeRank_le_iff_elementary_card_le (center P)).mp hzr _
        (IsElementaryAbelian.omega₁_of_isMulCommutative (p := 2) (center P))
  have hB := E.residualImage_isPSL_of_core_eq_bot
    (E.residualImage_core_eq_bot_of_cyclic_center (by omega) (hP ▸ hcyc))
  have hl := ChapterC.Section05.NormalizerControl.EmbeddingSelection.binary_rank_lower hB
  have hu := (Theory.GroupTheory.primeRank_le_of_injective 2 E.residualImage.subtype Subtype.val_injective).trans hr
  have hd := S.nonbinary
  omega

end MovedComponent

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
