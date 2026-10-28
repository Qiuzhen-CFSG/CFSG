module
public import CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne.TwoBlock.Family

/-!
# The full core and the two invariant natural choices

The actual four-member family puts Q in A(R), and its conjugate spans S
with it, proving S=J(R). Intersecting a family member with either natural
factor recovers its choice. The genuine block-exchange element carries
the first choice to the second, so the T_H-invariant family is {Q,Qˣ}.

Source: Aschbacher–Smith, C.5.6(7), printed p.159.
-/
public section
open Subgroup Stellmacher
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
variable {G : Type*} [Group G] [Finite G]

private theorem baumann_maxFamily (R : Subgroup G) :
    elementaryAbelianMaxSubgroups (S R) = elementaryAbelianMaxSubgroups R := by
  have hJR : elementaryAbelianMaxJ R ≤ S R := by
    apply le_inf (sSup_le fun _ hB => hB.1)
    apply le_centralizer_iff.mpr
    intro a ha
    exact mem_centralizer_iff.mpr ((mem_omegaOneCenterAmbient_iff _ _).mp ha).2.2
  obtain ⟨A, hA⟩ := elementaryAbelianMaxSubgroups_nonempty R
  have hAS : A ≤ S R := (le_sSup hA).trans hJR
  ext B
  constructor
  · intro hB
    refine ⟨hB.1.trans inf_le_left, hB.2.1, ?_⟩
    intro C hCR hC
    exact (hA.2.2 C hCR hC).trans (hB.2.2 A hAS hA.2.1)
  · intro hB
    refine ⟨(le_sSup hB).trans hJR, hB.2.1, ?_⟩
    intro C hCS hC
    exact hB.2.2 C (hCS.trans inf_le_left) hC

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

omit [Finite G] in
private theorem central_factor_intersection (F A B : Subgroup G)
    (hAF : A ≤ F) (hBC : B ≤ centralizer (F : Set G))
    (hZ : F ⊓ centralizer (F : Set G) ≤ A) : (A ⊔ B) ⊓ F = A := by
  apply le_antisymm
  · rintro g ⟨hg,hgF⟩
    have hm : g ∈ (A : Set G) * (B : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A B
        ((hBC.trans (centralizer_le hAF)).trans (Subgroup.centralizer_le_normalizer _))]
      exact hg
    obtain ⟨a,ha,b,hb,rfl⟩ := hm
    have hbF : b ∈ F := by simpa using F.mul_mem (F.inv_mem (hAF ha)) hgF
    exact A.mul_mem ha (hZ ⟨hbF,hBC hb⟩)
  · exact le_inf le_sup_left hAF

variable {R K L : Subgroup G} {𝔽 𝔽' : Type*} [Field 𝔽] [Field 𝔽']

theorem Setup.two_block_maximum_core
    (h : Setup R K 𝔽) (h' : Setup R L 𝔽') (hKL : L ≤ centralizer (K : Set G))
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    let S := ChapterB.baumann R
    let U := RankOne.U K ⊔ RankOne.U L
    let Q := S ⊓ centralizer (U : Set G)
    Q ∈ elementaryAbelianMaxSubgroups R ∧ S = elementaryAbelianMaxJ R := by
  let S := ChapterB.baumann R
  let U₁ := RankOne.U K
  let U₂ := RankOne.U L
  let V₁ := U₁.map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := U₂.map (MulAut.conj x⁻¹).toMonoidHom
  let U := U₁ ⊔ U₂
  let Q := S ⊓ centralizer (U : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  have hp := h.two_block_source_product h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hQS : Q ∈ elementaryAbelianMaxSubgroups S := by
    apply (h.two_block_family h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc Q).mpr
    exact ⟨U₁,Set.mem_insert _ _,U₂,Set.mem_insert _ _,hp.1⟩
  have hQR : Q ∈ elementaryAbelianMaxSubgroups R := by rwa [baumann_maxFamily R] at hQS
  refine ⟨hQR,?_⟩
  have hRx : R.map (MulAut.conj x⁻¹).toMonoidHom = R :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer (R : Set G)).inv_mem (hMR hx))
  have hQx : Q.map (MulAut.conj x⁻¹).toMonoidHom ∈ elementaryAbelianMaxSubgroups R := by
    have hh := (maxFamily_map_injective_iff (MulAut.conj x⁻¹).toMonoidHom (MulAut.conj x⁻¹).injective R Q).mpr hQR
    rwa [hRx] at hh
  apply le_antisymm
  · have hs : S = U.map (MulAut.conj x⁻¹).toMonoidHom ⊔ Q :=
      (h.two_block_factorization h' hKL M T_H x hx (hMR hx) hindex hpair ht hnc).2.2.1
    change S ≤ elementaryAbelianMaxJ R
    rw [hs]
    exact sup_le ((map_mono (show U ≤ Q from le_sup_left.trans_eq hp.1.symm)).trans (le_sSup hQx))
      (le_sSup hQR)
  · apply sSup_le
    intro A hA
    exact (baumann_maxFamily R ▸ hA).1


private theorem two_block_invariant_choice
    (h : Setup R K 𝔽) (h' : Setup R L 𝔽') (hKL : L ≤ centralizer (K : Set G))
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G))
    (A : Subgroup G) (hA : A ∈ elementaryAbelianMaxSubgroups R)
    (hTA : T_H ≤ normalizer (A : Set G)) :
    let S := ChapterB.baumann R
    let U := RankOne.U K ⊔ RankOne.U L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    A = Q ∨ A = V ⊔ D := by
  let V₁ := (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom
  let V₂ := (RankOne.U L).map (MulAut.conj x⁻¹).toMonoidHom
  let D := S R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  have hxR := hMR hx
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc
  have hd₁ := h.conjugate_factor_structure hxR hnc
  have hd₂ := h'.conjugate_factor_structure hxR (second_noncommuting hi)
  have hAS : A ∈ elementaryAbelianMaxSubgroups (S R) := by
    rw [baumann_maxFamily]
    exact hA
  obtain ⟨a,ha,b,hb,hAeq⟩ := (h.two_block_family h' hKL H M T_H hTHM hMR hTHKL hH hno
    x hx hindex hpair ht hnc A).mp hAS
  have hc : factor K x ≤ centralizer (factor L x : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (h.four_module_geometry hKL h'.module_le M T_H x hx hxR hindex hpair ht hnc).2.2.2
  have hD₁ : D ≤ RankOne.D R K := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (show K ≤ K ⊔ L from le_sup_left)))
  have hD₂ : D ≤ RankOne.D R L := le_inf inf_le_left
    (inf_le_right.trans (centralizer_le (show L ≤ K ⊔ L from le_sup_right)))
  have hleft : a ≤ factor K x ∧ factor K x ⊓ centralizer (factor K x : Set G) ≤ a := by
    have hZ : factor K x ⊓ centralizer (factor K x : Set G) ≤ RankOne.U K ⊓ V₁ := by
      apply le_inf hd₁.2.2.2.2
      intro z hz
      have hh : z ∈ RankOne.U K ⊓ centralizer (V₁ : Set G) :=
        ⟨hd₁.2.2.2.2 hz,centralizer_le (show V₁ ≤ factor K x from le_sup_right) hz.2⟩
      rw [← (h.commutator_eq_fixed hxR hnc).1,(h.commutator_eq_fixed hxR hnc).2] at hh
      exact hh.2
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨le_sup_left,hZ.trans inf_le_left⟩
    · obtain rfl := Set.mem_singleton_iff.mp ha
      exact ⟨le_sup_right,hZ.trans inf_le_right⟩
  have hright : b ≤ factor L x ∧ factor L x ⊓ centralizer (factor L x : Set G) ≤ b := by
    have hZ : factor L x ⊓ centralizer (factor L x : Set G) ≤ RankOne.U L ⊓ V₂ := by
      apply le_inf hd₂.2.2.2.2
      intro z hz
      have hh : z ∈ RankOne.U L ⊓ centralizer (V₂ : Set G) :=
        ⟨hd₂.2.2.2.2 hz,centralizer_le (show V₂ ≤ factor L x from le_sup_right) hz.2⟩
      rw [← (h'.commutator_eq_fixed hxR (second_noncommuting hi)).1,
        (h'.commutator_eq_fixed hxR (second_noncommuting hi)).2] at hh
      exact hh.2
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · exact ⟨le_sup_left,hZ.trans inf_le_left⟩
    · obtain rfl := Set.mem_singleton_iff.mp hb
      exact ⟨le_sup_right,hZ.trans inf_le_right⟩
  have he1 : A ⊓ factor K x = a := by
    rw [hAeq,sup_assoc]
    exact central_factor_intersection _ a (b ⊔ D) hleft.1
      (sup_le (hright.1.trans (le_centralizer_iff.mp hc)) (hD₁.trans hd₁.2.1)) hleft.2
  have he2 : A ⊓ factor L x = b := by
    have he : A = b ⊔ (a ⊔ D) := by rw [hAeq]; dsimp only [D]; ac_rfl
    rw [he]
    exact central_factor_intersection _ b (a ⊔ D) hright.1
      (sup_le (hleft.1.trans hc) (hD₂.trans hd₂.2.1)) hright.2
  obtain ⟨t,htT,htU,htV⟩ := paired_exchange hi
  change (RankOne.U K).map (MulAut.conj (t : G)).toMonoidHom = RankOne.U L at htU
  change V₁.map (MulAut.conj (t : G)).toMonoidHom = V₂ at htV
  have heF : (factor K x).map (MulAut.conj (t : G)).toMonoidHom = factor L x := by
    change (RankOne.U K ⊔ V₁).map (MulAut.conj (t : G)).toMonoidHom = RankOne.U L ⊔ V₂
    rw [Subgroup.map_sup,htU,htV]
  have heA : A.map (MulAut.conj (t : G)).toMonoidHom = A := mem_normalizer_iff_map_conj_eq.mp (hTA htT)
  have hab : a.map (MulAut.conj (t : G)).toMonoidHom = b := by
    rw [← he1,Subgroup.map_inf _ _ _ (MulAut.conj (t : G)).injective,heA,heF,he2]
  rcases Set.mem_insert_iff.mp ha with he | he
  · left
    have hb : b = RankOne.U L := by rw [he,htU] at hab; exact hab.symm
    have hp := h.two_block_factorization h' hKL M T_H x hx hxR hindex hpair ht hnc
    exact (hAeq.trans (by rw [he,hb])).trans hp.1.symm
  · right
    have he := Set.mem_singleton_iff.mp he
    have hb : b = V₂ := by rw [he,htV] at hab; exact hab.symm
    rw [hAeq,he,hb,Subgroup.map_sup]

theorem Setup.two_block_invariant_family
    (h : Setup R K 𝔽) (h' : Setup R L 𝔽') (hKL : L ≤ centralizer (K : Set G))
    (H M T_H : Subgroup G) (hTHM : T_H ≤ M)
    (hMR : M ≤ normalizer (R : Set G))
    (hTHKL : T_H ≤ normalizer ((K ⊔ L : Subgroup G) : Set G))
    (hH : H = (K ⊔ L) ⊔ T_H)
    (hno : ∀ W : Subgroup G, W ≤ R → H ≤ normalizer (W : Set G) →
      M ≤ normalizer (W : Set G) → W = ⊥)
    (x : G) (hx : x ∈ M) (hindex : T_H.relIndex M = 2)
    (hpair : ∀ g ∈ T_H, K.conjBy g = K ∨ K.conjBy g = L)
    (ht : ∃ t : M, (t : G) ∈ T_H ∧ K.conjBy (t : G) = L)
    (hnc : ¬ (RankOne.U K).map (MulAut.conj x⁻¹).toMonoidHom ≤ centralizer (RankOne.U K : Set G)) :
    let S := ChapterB.baumann R
    let U := RankOne.U K ⊔ RankOne.U L
    let V := U.map (MulAut.conj x⁻¹).toMonoidHom
    let Q := S ⊓ centralizer (U : Set G)
    let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
    Q ∈ elementaryAbelianMaxSubgroups R ∧ S = elementaryAbelianMaxJ R ∧
      V ⊔ D = Q.map (MulAut.conj x⁻¹).toMonoidHom ∧
      {A ∈ elementaryAbelianMaxSubgroups R | T_H ≤ normalizer (A : Set G)} =
        {Q,Q.map (MulAut.conj x⁻¹).toMonoidHom} := by
  let S := ChapterB.baumann R
  let U := RankOne.U K ⊔ RankOne.U L
  let V := U.map (MulAut.conj x⁻¹).toMonoidHom
  let Q := S ⊓ centralizer (U : Set G)
  let D := S ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)
  let e := MulAut.conj x⁻¹
  let Q' := Q.map e.toMonoidHom
  have hmax := h.two_block_maximum_core h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hprod := h.two_block_source_product h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
  have hi := h.fourModuleSourceInputs hKL h'.module_le M T_H x hx (hMR hx) hindex hpair ht hnc
  have hTU : T_H ≤ normalizer (U : Set G) := by
    intro g hg
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · change (RankOne.U K ⊔ RankOne.U L).map (MulAut.conj g).toMonoidHom ≤ U
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
    have hUQ : RankOne.U K ≤ Q := le_sup_left.trans (le_sup_left.trans_eq hprod.1.symm)
    exact hnc (((map_mono (f := e.toMonoidHom) hUQ).trans_eq he).trans
      (inf_le_right.trans (centralizer_le (show RankOne.U K ≤ U from le_sup_left))))
  have hQ' : Q' = V ⊔ D := by
    rcases two_block_invariant_choice h h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc
      Q' hQ'max hTQ' with he | he
    · exact (hneq he).elim
    · exact he
  refine ⟨hmax.1,hmax.2,hQ'.symm,?_⟩
  change {A ∈ elementaryAbelianMaxSubgroups R | T_H ≤ normalizer (A : Set G)} = {Q,Q'}
  ext A
  constructor
  · rintro ⟨hA,hTA⟩
    have hc := two_block_invariant_choice h h' hKL H M T_H hTHM hMR hTHKL hH hno x hx hindex hpair ht hnc A hA hTA
    change A = Q ∨ A = V ⊔ D at hc
    rw [← hQ'] at hc
    exact hc
  · intro ha
    rcases Set.mem_insert_iff.mp ha with rfl | ha
    · exact ⟨hmax.1,hTQ⟩
    · have ha := Set.mem_singleton_iff.mp ha
      subst A
      exact ⟨hQ'max,hTQ'⟩

end CFSG.Quasithin.ChapterC.Section05.ConjugateSource.RankOne
