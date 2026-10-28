module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.TwoBlock.FactorFamily
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.AlternatingFamily
/-!
# The full two-block core is maximum elementary

The genuine conjugate factors form a direct product with D. Each original
module is maximum elementary in its factor, and the no-common-normal
hypothesis has already made D elementary. The product-family theorem
therefore puts C_S(U₁U₂)=U₁U₂D in A(R). Its conjugate spans S with it,
which proves S=J(R). The actual block exchange forces the choices in the
two factors to match, so precisely Q and Qˣ are T_H-invariant members of A(R).

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/

public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G]

private theorem maxFamily_elementary (D : Subgroup G) (hD : IsElementaryAbelian 2 D) :
    elementaryAbelianMaxSubgroups D = {D} := by
  ext A
  constructor
  · intro hA
    exact eq_of_le_of_card_ge hA.1 (hA.2.2 D le_rfl hD)
  · rintro rfl
    exact ⟨le_rfl, hD, fun B hB _ => card_le_of_le hB⟩

private theorem maxFamily_three (F₁ F₂ D : Subgroup G)
    (hd₁ : Disjoint F₁ (F₂ ⊔ D)) (hc₁ : F₁ ≤ centralizer (F₂ ⊔ D : Subgroup G))
    (hd₂ : Disjoint F₂ D) (hc₂ : F₂ ≤ centralizer (D : Set G))
    (hD : IsElementaryAbelian 2 D) (A : Subgroup G) :
    A ∈ elementaryAbelianMaxSubgroups (F₁ ⊔ (F₂ ⊔ D)) ↔
      ∃ A₁ ∈ elementaryAbelianMaxSubgroups F₁, ∃ A₂ ∈ elementaryAbelianMaxSubgroups F₂,
        A = A₁ ⊔ (A₂ ⊔ D) := by
  rw [maxFamily_sup_iff_of_disjoint_of_commuting F₁ (F₂ ⊔ D) hd₁ hc₁]
  constructor
  · rintro ⟨A₁,h1,B,hB,rfl⟩
    obtain ⟨A₂,h2,D',hD',rfl⟩ := (maxFamily_sup_iff_of_disjoint_of_commuting F₂ D hd₂ hc₂ B).mp hB
    have he : D' = D := by simpa only [maxFamily_elementary D hD, Set.mem_singleton_iff] using hD'
    exact ⟨A₁,h1,A₂,h2,he ▸ rfl⟩
  · rintro ⟨A₁,h1,A₂,h2,rfl⟩
    refine ⟨A₁,h1,A₂ ⊔ D,?_,rfl⟩
    exact (maxFamily_sup_iff_of_disjoint_of_commuting F₂ D hd₂ hc₂ _).mpr
      ⟨A₂,h2,D,by rw [maxFamily_elementary D hD]; exact Set.mem_singleton _,rfl⟩

omit [Finite G] in
private theorem product_factor_intersection (F E A B : Subgroup G)
    (hdisj : Disjoint F E) (hcomm : F ≤ centralizer (E : Set G))
    (hA : A ≤ F) (hB : B ≤ E) : (A ⊔ B) ⊓ F = A := by
  apply le_antisymm
  · rintro g ⟨hg,hgF⟩
    have hcommAB : B ≤ normalizer (A : Set G) :=
      ((hB.trans (le_centralizer_iff.mp hcomm)).trans (centralizer_le hA)).trans
        (Subgroup.centralizer_le_normalizer _)
    have hm : g ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A B hcommAB]
      exact hg
    obtain ⟨a,ha,b,hb,rfl⟩ := hm
    have hbF : b ∈ F := by simpa using F.mul_mem (F.inv_mem (hA ha)) hgF
    have hb1 : b = 1 := (show b ∈ (⊥ : Subgroup G) from hdisj.eq_bot ▸ ⟨hbF,hB hb⟩)
    change a * b ∈ A
    rw [hb1,mul_one]
    exact ha
  · exact le_inf le_sup_left hA

omit [Finite G] in
private theorem paired_exchange {M T U V : Subgroup G} {x : G}
    (h : FourModuleOrbit.SourceInputs M T U V x) :
    ∃ t : M, (t : G) ∈ T ∧ U.conjBy (t : G) = V ∧
      (U.conjBy x⁻¹).conjBy (t : G) = V.conjBy x⁻¹ := by
  obtain ⟨t,ht⟩ := FourModuleOrbit.source_setup h.toInputs
  have htable := ht.table t
  have h02 : FourModuleOrbit.action h.toInputs t 0 = 1 ∧
      FourModuleOrbit.action h.toInputs t 2 = 3 := by
    rcases htable with h0 | h1 | h2 | h3
    · have hh := ht.t_zero
      rw [h0.1] at hh
      contradiction
    · exact ⟨h1.1,h1.2.2.1⟩
    · have hh := ht.t_zero
      rw [h2.1] at hh
      contradiction
    · have hh := ht.t_zero
      rw [h3.1] at hh
      contradiction
  have he0 := FourModuleOrbit.action_apply h.toInputs t 0
  have he2 := FourModuleOrbit.action_apply h.toInputs t 2
  rw [h02.1] at he0
  rw [h02.2] at he2
  exact ⟨t,ht.t_mem,he0.symm,he2.symm⟩

variable {R K L : Subgroup G}

theorem AlternatingPairSetup.two_block_maximum_core
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K ⊔ sourceModule L
    let Q := S ⊓ centralizer (U : Set G)
    Q ∈ elementaryAbelianMaxSubgroups R ∧ S = elementaryAbelianMaxJ R := by
  let S := ChapterB.baumann R
  let U₁ := sourceModule K
  let U₂ := sourceModule L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let F₁ := U₁ ⊔ V₁
  let F₂ := U₂ ⊔ V₂
  let U := U₁ ⊔ U₂
  let Q := S ⊓ centralizer (U : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  have hi := h.fourModuleSourceInputs h'.module_le M T_H x hx (hMR hx) hindex hpair ht hnc
  have hp := h.two_block_source_product h' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hd := h.two_block_direct_product h' M T_H x hx (hMR hx) hindex hpair ht hnc
  have hD : IsElementaryAbelian 2 D := by
    let : IsElementaryAbelian 2 Q := hp.2.2.2.2.2
    exact IsElementaryAbelian.of_le (show D ≤ Q from le_sup_right.trans_eq hp.1.symm)
  obtain ⟨B₀,B₁,hf1,_,_⟩ := h.conjugate_factor_family x (hMR hx) hnc
  obtain ⟨C₀,C₁,hf2,_,_⟩ := h'.conjugate_factor_family x (hMR hx) hi.second_noncommuting
  change elementaryAbelianMaxSubgroups F₁ = {U₁,V₁,B₀,B₁} at hf1
  change elementaryAbelianMaxSubgroups F₂ = {U₂,V₂,C₀,C₁} at hf2
  have hU₁ : U₁ ∈ elementaryAbelianMaxSubgroups F₁ := by rw [hf1]; simp
  have hU₂ : U₂ ∈ elementaryAbelianMaxSubgroups F₂ := by rw [hf2]; simp
  have hdspan : S = F₁ ⊔ (F₂ ⊔ D) := hd.1
  have hQS : Q ∈ elementaryAbelianMaxSubgroups S := by
    rw [hdspan]
    apply (maxFamily_three F₁ F₂ D hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 hD Q).mpr
    refine ⟨U₁,hU₁,U₂,hU₂,?_⟩
    exact hp.1.trans (sup_assoc U₁ U₂ D)
  have hQR : Q ∈ elementaryAbelianMaxSubgroups R := by rwa [baumann_maxFamily R] at hQS
  refine ⟨hQR,?_⟩
  have hRx : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem (hMR hx))
  have hQx : Q.map (MulAut.conj x⁻¹).toMonoidHom ∈ elementaryAbelianMaxSubgroups R := by
    have hh := (maxFamily_map_injective_iff (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective R Q).mpr hQR
    rwa [hRx] at hh
  apply le_antisymm
  · have hs : S = U.map (MulAut.conj x⁻¹).toMonoidHom ⊔ Q :=
      (h.two_block_factorization h' M T_H x hx (hMR hx) hindex hpair ht hnc).2.2.1
    change S ≤ elementaryAbelianMaxJ R
    rw [hs]
    exact sup_le ((map_mono (show U ≤ Q from le_sup_left.trans_eq hp.1.symm)).trans (le_sSup hQx))
      (le_sSup hQR)
  · apply sSup_le
    intro A hA
    exact (baumann_maxFamily R ▸ hA).1


private theorem two_block_invariant_choice
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (H M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups R)
    (hTA : T_H ≤ normalizer (A : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K ⊔ sourceModule L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    A = Q ∨ A = V ⊔ D := by
  let S := ChapterB.baumann R
  let U₁ := sourceModule K
  let U₂ := sourceModule L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let F₁ := U₁ ⊔ V₁
  let F₂ := U₂ ⊔ V₂
  let U := U₁ ⊔ U₂
  let Q := S ⊓ centralizer (U : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  have hi := h.fourModuleSourceInputs h'.module_le M T_H x hx (hMR hx) hindex hpair ht hnc
  have hp := h.two_block_source_product h' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hd := h.two_block_direct_product h' M T_H x hx (hMR hx) hindex hpair ht hnc
  have hdspan : S = F₁ ⊔ (F₂ ⊔ D) := hd.1
  have hD : IsElementaryAbelian 2 D := by
    let : IsElementaryAbelian 2 Q := hp.2.2.2.2.2
    exact IsElementaryAbelian.of_le (show D ≤ Q from le_sup_right.trans_eq hp.1.symm)
  have hAS : A ∈ elementaryAbelianMaxSubgroups (F₁ ⊔ (F₂ ⊔ D)) := by
    rw [← hdspan,baumann_maxFamily R]
    exact hA
  obtain ⟨A₁,h1,A₂,h2,hAA⟩ := (maxFamily_three F₁ F₂ D hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 hD A).mp hAS
  have hi1 : A ⊓ F₁ = A₁ := by
    rw [hAA]
    exact product_factor_intersection F₁ (F₂ ⊔ D) A₁ (A₂ ⊔ D) hd.2.1 hd.2.2.1 h1.1
      (sup_le (h2.1.trans le_sup_left) le_sup_right)
  have hirest : A ⊓ (F₂ ⊔ D) = A₂ ⊔ D := by
    rw [hAA,sup_comm A₁]
    exact product_factor_intersection (F₂ ⊔ D) F₁ (A₂ ⊔ D) A₁ hd.2.1.symm
      (le_centralizer_iff.mp hd.2.2.1) (sup_le (h2.1.trans le_sup_left) le_sup_right) h1.1
  have hi2 : A ⊓ F₂ = A₂ := by
    calc
      A ⊓ F₂ = (A ⊓ (F₂ ⊔ D)) ⊓ F₂ := by rw [inf_assoc,inf_eq_right.mpr (show F₂ ≤ F₂ ⊔ D from le_sup_left)]
      _ = (A₂ ⊔ D) ⊓ F₂ := by rw [hirest]
      _ = A₂ := product_factor_intersection F₂ D A₂ D hd.2.2.2.1 hd.2.2.2.2 h2.1 le_rfl
  have hn := h.transvection_normalizes x (hMR hx)
  have hRKF : R ⊓ K ≤ normalizer (F₁ : Set G) :=
    (le_inf (hn.2.2.trans hn.1) (hn.2.2.trans hn.2.1)).trans
      (normalizer_inf_normalizer_le_normalizer_sup U₁ V₁)
  have hn1 : R ⊓ K ≤ normalizer (A₁ : Set G) := by
    rw [← hi1]
    exact (le_inf ((inf_le_left.trans hRTH).trans hTA) hRKF).trans inf_normalizer_le_normalizer_inf
  have hfamily : {B ∈ elementaryAbelianMaxSubgroups F₁ | R ⊓ K ≤ normalizer (B : Set G)} = {U₁,V₁} :=
    h.conjugate_factor_invariant_family x (hMR hx) hnc
  have hchoice : A₁ = U₁ ∨ A₁ = V₁ := by
    have hm : A₁ ∈ {U₁,V₁} := hfamily ▸ (show A₁ ∈ {B ∈ elementaryAbelianMaxSubgroups F₁ |
      R ⊓ K ≤ normalizer (B : Set G)} from ⟨h1,hn1⟩)
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hm
  obtain ⟨t,htT,htU,htV⟩ := paired_exchange hi
  change U₁.map (MulAut.conj (t : G)).toMonoidHom = U₂ at htU
  change V₁.map (MulAut.conj (t : G)).toMonoidHom = V₂ at htV
  have heF : F₁.map (MulAut.conj (t : G)).toMonoidHom = F₂ := by
    change (U₁ ⊔ V₁).map (MulAut.conj (t : G)).toMonoidHom = U₂ ⊔ V₂
    rw [Subgroup.map_sup,htU,htV]
  have heA : A.map (MulAut.conj (t : G)).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp (hTA htT)
  have he12 : A₁.map (MulAut.conj (t : G)).toMonoidHom = A₂ := by
    rw [← hi1,Subgroup.map_inf _ _ _ (MulAut.conj (t : G)).injective,heA,heF,hi2]
  rcases hchoice with he1 | he1
  · left
    have he2 : A₂ = U₂ := by rw [he1,htU] at he12; exact he12.symm
    change A = Q
    rw [hAA,he1,he2]
    exact (sup_assoc U₁ U₂ D).symm.trans hp.1.symm
  · right
    have he2 : A₂ = V₂ := by rw [he1,htV] at he12; exact he12.symm
    change A = U.map (MulAut.conj x⁻¹).toMonoidHom ⊔ D
    rw [hAA,he1,he2]
    exact (sup_assoc V₁ V₂ D).symm.trans (congrArg (fun B => B ⊔ D) (Subgroup.map_sup _ _ _).symm)


theorem AlternatingPairSetup.two_block_invariant_family
    (h : AlternatingPairSetup R K L) (h' : AlternatingPairSetup R L K)
    (H M T_H : Subgroup G) (hRTH : R ≤ T_H) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (sourceModule K : Set G)) :
    let S := ChapterB.baumann R
    let U := sourceModule K ⊔ sourceModule L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    Q ∈ elementaryAbelianMaxSubgroups R ∧ S = elementaryAbelianMaxJ R ∧
      V ⊔ D = Q.map (MulAut.conj x⁻¹).toMonoidHom ∧
      {A ∈ elementaryAbelianMaxSubgroups R | T_H ≤ normalizer (A : Set G)} =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let S := ChapterB.baumann R
  let U := sourceModule K ⊔ sourceModule L
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Q := S ⊓ centralizer (U : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let e := MulAut.conj x⁻¹
  let Q' := Q.map e.toMonoidHom
  have hmax := h.two_block_maximum_core h' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hprod := h.two_block_source_product h' H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hi := h.fourModuleSourceInputs h'.module_le M T_H x hx (hMR hx) hindex hpair ht hnc
  have hTU : T_H ≤ normalizer (U : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · change (sourceModule K ⊔ sourceModule L).map (MulAut.conj g).toMonoidHom ≤ U
      rw [Subgroup.map_sup]
      apply sup_le
      · rcases hi.pair_zero g hg with he | he
        · exact he.le.trans le_sup_left
        · exact he.le.trans le_sup_right
      · rcases hi.pair_one g hg with he | he
        · exact he.le.trans le_sup_left
        · exact he.le.trans le_sup_right
    · exact (card_map_of_injective (MulAut.conj g).injective).ge
  have hNC : normalizer (U : Set G) ≤ normalizer (centralizer (U : Set G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer (U : Set G))).mp inferInstance
  have hTQ : T_H ≤ normalizer (Q : Set G) :=
    (le_inf ((hTHM.trans hMR).trans (normalizer_le_normalizer_baumann R)) (hTU.trans hNC)).trans
      inf_normalizer_le_normalizer_inf
  have hnorm : (T_H.subgroupOf M).Normal := normal_of_index_eq_two hindex
  have hMT : M ≤ normalizer (T_H : Set G) := (normal_subgroupOf_iff_le_normalizer hTHM).mp hnorm
  have heT : T_H.map e.toMonoidHom = T_H := mem_normalizer_iff_map_conj_eq.mp (hMT (M.inv_mem hx))
  have hTQ' : T_H ≤ normalizer (Q' : Set G) := by
    rw [← heT]
    exact (map_mono hTQ).trans (le_normalizer_map e.toMonoidHom)
  have heR : R.map e.toMonoidHom = R := mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (R : Set G)).inv_mem (hMR hx))
  have hQ'max : Q' ∈ elementaryAbelianMaxSubgroups R := by
    have hm := (maxFamily_map_injective_iff e.toMonoidHom e.injective R Q).mpr hmax.1
    rwa [heR] at hm
  have hneq : Q' ≠ Q := by
    intro he
    have hUQ : sourceModule K ≤ Q := le_sup_left.trans (le_sup_left.trans_eq hprod.1.symm)
    exact hnc (((map_mono (f := e.toMonoidHom) hUQ).trans_eq he).trans
      (inf_le_right.trans (centralizer_le (show sourceModule K ≤ U from le_sup_left))))
  have hQ' : Q' = V ⊔ D := by
    rcases two_block_invariant_choice h h' H M T_H hRTH hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
      Q' hQ'max hTQ' with he | he
    · exact (hneq he).elim
    · exact he
  refine ⟨hmax.1,hmax.2,hQ'.symm,?_⟩
  change {A ∈ elementaryAbelianMaxSubgroups R | T_H ≤ normalizer (A : Set G)} = {Q,Q'}
  ext A
  constructor
  · rintro ⟨hA,hTA⟩
    have hc := two_block_invariant_choice h h' H M T_H hRTH hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc A hA hTA
    change A = Q ∨ A = V ⊔ D at hc
    rw [← hQ'] at hc
    exact hc
  · intro ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨hmax.1,hTQ⟩
    · have ha := Set.mem_singleton_iff.mp ha
      subst A
      exact ⟨hQ'max,hTQ'⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource
