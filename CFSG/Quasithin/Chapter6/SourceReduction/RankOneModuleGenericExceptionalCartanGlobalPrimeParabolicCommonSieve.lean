module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeParabolicCommonContainer
public import Theory.SpecificGroups.OddThreeSectionRank

/-!
# The ordinary common-container sieve for the selected diagram parabolic

The original residual has radical quotient of two-rank at least four.
Every section of odd-field PSL₃ or PSU₃ has two-rank at most three,
while odd-field PSL₂ has dihedral Sylow sections. The literal map from
the original residual into the common two-core quotient has solvable
kernel, so these bounds exclude all odd-characteristic containers.
For SL₃ and SU₃ the projective kernel is retained and factored only
through a solvable-kernel equivalence. The same argument excludes
A₅, A₆, A₇, their cubic covers, and J₁ by the two-part of their orders.

A Bender common container is also impossible. Full-Sylow restriction
first identifies it with the original residual, and then identifies
that residual with its proper selected parabolic. This uses the
original Sylow in the residual, not an assumed full Sylow on R in H.

The actual source pair consequently retains only rank-two, binary
linear, A₈ and sporadic simple containers, or binary ternary and M₂₂
cubic covers. All literal embeddings, the changed full Sylow, both
original Cartans and their original field parameters are preserved.
The remaining containers and zero-core branch are not excluded here.

Source: Aschbacher–Smith A.3.6, A.3.12, 5.1.12 and 5.2.2,
printed pp.43–48,635,648–649, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Matrix BenderSuzuki.MatrixGroups
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
open Chapter1.Section02 LocalModels

private theorem radical_rank_of_solvableKernel
    {Y Z : Type*} [Group Y] [Group Z] [Finite Y] [Finite Z]
    (f : Y →* Z) [Group.IsSolvable f.ker]
    (hr : ∀ P : Subgroup Z, primeRank 2 (P ⧸ solvableRadical P) ≤ 3) :
    primeRank 2 (Y ⧸ solvableRadical Y) ≤ 3 := by
  let : Group.IsSolvable f.rangeRestrict.ker := by rwa [MonoidHom.ker_rangeRestrict]
  let e := solvableRadicalQuotientEquiv f.rangeRestrict f.rangeRestrict_surjective
  rw [primeRank_equiv 2 e]
  exact hr f.range

private theorem radical_rank_of_projective_ternary
    {Y Z : Type*} [Group Y] [Group Z] [Finite Y] [Finite Z]
    (f : Y →* Z) [Group.IsSolvable f.ker]
    {q : ℕ} (ho : Odd q)
    (hm : ClassicalGroup.IsPSL Z 3 q ∨ ClassicalGroup.IsPSU Z 3 q) :
    primeRank 2 (Y ⧸ solvableRadical Y) ≤ 3 := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,_,⟨e⟩⟩
  · let g := e.toMonoidHom.comp f
    let : Group.IsSolvable g.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      infer_instance
    exact radical_rank_of_solvableKernel g (fun P =>
      Theory.SpecificGroups.OddThreeSectionRank.psl3_subgroup_quotient_twoRank_le_three
        (hF.symm ▸ ho) P (solvableRadical P))
  · let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) := Finite.of_equiv Z e.toEquiv
    let g := e.toMonoidHom.comp f
    let : Group.IsSolvable g.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      infer_instance
    exact radical_rank_of_solvableKernel g (fun P =>
      Theory.SpecificGroups.OddThreeSectionRank.psu3_subgroup_quotient_twoRank_le_three
        J (hF.symm ▸ ho.pow) P (solvableRadical P))

private theorem radical_rank_of_special_ternary
    {Y Z : Type*} [Group Y] [Group Z] [Finite Y] [Finite Z]
    (f : Y →* Z) [Group.IsSolvable f.ker]
    {q : ℕ} (ho : Odd q) (hm : IsSL Z 3 q ∨ IsSU Z 3 q) :
    primeRank 2 (Y ⧸ solvableRadical Y) ≤ 3 := by
  rcases hm with ⟨F,_,_,hF,⟨e⟩⟩ | ⟨F,_,_,J,hF,hconj,⟨e⟩⟩
  · let g := e.toMonoidHom.comp f
    let : Group.IsSolvable g.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      infer_instance
    let r := QuotientGroup.mk' (center SL(3,F))
    let : Group.IsSolvable r.ker := by
      rw [QuotientGroup.ker_mk']
      exact Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
    let : Group.IsSolvable (r.comp g).ker := by
      rw [←MonoidHom.comap_ker]
      exact isSolvable_comap_of_solvable_ker g r.ker
    exact radical_rank_of_projective_ternary (r.comp g) ho
      (.inl ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)
  · let g := e.toMonoidHom.comp f
    let : Group.IsSolvable g.ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      infer_instance
    let r := J.specialToProjective
    let : Group.IsSolvable (center J.specialSubgroup) :=
      Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
    let : Group.IsSolvable r.ker := Group.isSolvable_of_isSolvable_injective
      (f := inclusion J.specialToProjective_ker_le_center)
      (inclusion_injective _)
    let : Group.IsSolvable (r.comp g).ker := by
      rw [←MonoidHom.comap_ker]
      exact isSolvable_comap_of_solvable_ker g r.ker
    let : Finite (ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective r J.specialToProjective_surjective
    exact radical_rank_of_projective_ternary (r.comp g) ho
      (.inr ⟨F,inferInstance,inferInstance,J,hF,hconj,⟨MulEquiv.refl _⟩⟩)

private theorem dihedral_image_rank
    {Y Z : Type*} [Group Y] [Group Z] [Finite Y] [Finite Z] {n : ℕ}
    (j : Y →* DihedralGroup (2^n)) (hj : Function.Injective j)
    (f : Y →* Z) (hf : Function.Surjective f) : primeRank 2 Z ≤ 2 := by
  let R := zpowers (DihedralGroup.r 1 : DihedralGroup (2^n))
  have hiR : R.index = 2 := by
    have hc : Nat.card R = 2^n := by rw [Nat.card_zpowers,DihedralGroup.orderOf_r_one]
    have hi := R.card_mul_index
    rw [hc,DihedralGroup.nat_card] at hi
    have hp : 0 < 2^n := pow_pos (by decide) _
    nlinarith
  let A := R.comap j
  let : IsCyclic A := isCyclic_of_injective (j.subgroupComap R)
    (by intro x y he; exact Subtype.ext (hj (congrArg Subtype.val he)))
  let : IsCyclic (A.map f) := isCyclic_of_surjective (f.subgroupMap A)
    (f.subgroupMap_surjective A)
  have hiA : A.index ≤ 2 := by
    rw [show A = R.comap j from rfl,index_comap]
    calc
      R.relIndex j.range ≤ R.index := by
        simpa only [relIndex_top_right] using
          (relIndex_le_of_le_right (H := R) (K := j.range) (L := ⊤) le_top (by
            simpa only [relIndex_top_right] using R.index_ne_zero_of_finite))
      _ = 2 := hiR
  have hiAf : (A.map f).index ≤ 2^1 :=
    (Nat.le_of_dvd (Nat.pos_of_ne_zero A.index_ne_zero_of_finite)
      (A.index_map_dvd hf)).trans hiA
  let P : Sylow 2 (A.map f) := Classical.choice inferInstance
  have hr : primeRank 2 (A.map f) ≤ 1 := P.primeRank_le_one_of_isCyclic inferInstance
  have hb := primeRank_le_add_of_index_le (A.map f) hiAf
  omega

private theorem pgl_subgroup_radical_rank
    {F : Type*} [Field F] [Finite F]
    (hF : GorensteinWalter.IsOddPrimePower (Nat.card F))
    (B : Subgroup (GorensteinWalter.PGL2 F)) :
    primeRank 2 (B ⧸ solvableRadical B) ≤ 3 := by
  let : Finite (GorensteinWalter.PGL2 F) := Finite.of_surjective
    ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let T : Sylow 2 B := Classical.choice inferInstance
  let rho := B.subtype.comp (T : Subgroup B).subtype
  have hir : Function.Injective rho := B.subtype_injective.comp (T : Subgroup B).subtype_injective
  obtain ⟨P,hP⟩ := (T.isPGroup'.of_surjective rho.rangeRestrict rho.rangeRestrict_surjective).exists_le_sylow
  obtain ⟨n,_,⟨e⟩⟩ := GorensteinWalter.pgl2_odd_hasDihedralSylowTwo_model F hF P
  let r : T →* P := rho.codRestrict (P : Subgroup _) (fun x => hP ⟨x,rfl⟩)
  have hi : Function.Injective r := by
    intro x y he
    exact hir (congrArg (fun z : P => (z : GorensteinWalter.PGL2 F)) he)
  let q := QuotientGroup.mk' (solvableRadical B)
  let S := T.mapSurjective (QuotientGroup.mk'_surjective (solvableRadical B))
  rw [S.primeRank_eq]
  exact (dihedral_image_rank (e.toMonoidHom.comp r) (e.injective.comp hi)
    (q.subgroupMap (T : Subgroup B)) (q.subgroupMap_surjective _)).trans (by decide)

private theorem radical_rank_of_odd_linear_two
    {Y Z : Type*} [Group Y] [Group Z] [Finite Y] [Finite Z]
    (f : Y →* Z) [Group.IsSolvable f.ker]
    {q k : ℕ} (hq : q.Prime) (ho : Odd q) (hk : 0 < k)
    (hm : ClassicalGroup.IsPSL Z 2 (q^k)) :
    primeRank 2 (Y ⧸ solvableRadical Y) ≤ 3 := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Finite (GorensteinWalter.PGL2 F) := Finite.of_surjective
    ProjGenLinGroup.mk ProjGenLinGroup.mk_surjective
  let r : Z →* GorensteinWalter.PGL2 F :=
    ProjectiveSpecialLinearGroup.toPGL.comp e.toMonoidHom
  have hr : Function.Injective r := ProjectiveSpecialLinearGroup.toPGL_injective.comp e.injective
  let : Group.IsSolvable (r.comp f).ker := by
    rw [MonoidHom.ker_comp_of_injective _ _ hr]
    infer_instance
  exact radical_rank_of_solvableKernel (r.comp f)
    (pgl_subgroup_radical_rank ⟨q,k,hq,ho,hk,hF⟩)

variable {G : Type*} [Group G] [Finite G]

private theorem SelectedSourceModels.original_residual_common_section_rank
    {H R X I : Subgroup G} (hs : SelectedSourceModels H R)
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hIX : I ≤ X) (hKI : residual H ≤ I)
    (hb : let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      ∀ (j : residual H →* Ibar) [Group.IsSolvable j.ker],
        primeRank 2 ((residual H) ⧸ solvableRadical (residual H)) ≤ 3) : False := by
  let q := QuotientGroup.mk' (pCore 2 X)
  let r := q.subgroupMap (I.subgroupOf X)
  let a := (subgroupOfEquivOfLe hIX).symm
  let j := (r.comp a.toMonoidHom).comp (inclusion hKI)
  have hk : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let : Group.IsNilpotent r.ker := hk.isNilpotent
  let : Group.IsSolvable r.ker := inferInstance
  let : Group.IsSolvable (r.comp a.toMonoidHom).ker := by
    change Group.IsSolvable (r.ker.comap a.toMonoidHom)
    exact Group.isSolvable_of_isSolvable_injective
      (f := a.toMonoidHom.subgroupComap r.ker)
      (by intro x y hh; exact Subtype.ext (a.injective (congrArg Subtype.val hh)))
  let : Group.IsSolvable j.ker := by
    change Group.IsSolvable ((r.comp a.toMonoidHom).ker.comap (inclusion hKI))
    exact Group.isSolvable_of_isSolvable_injective
      (f := (inclusion hKI).subgroupComap (r.comp a.toMonoidHom).ker)
      (by intro x y hh; exact Subtype.ext ((inclusion_injective hKI) (congrArg Subtype.val hh)))
  have hu := hb j
  have hl := hs.original_residual_radical_two_rank hn
  omega

/-- All odd-characteristic common containers, including cubic covers,
are excluded by the radical quotient of the original diagram residual. -/
theorem SelectedSourceModels.parabolic_common_not_odd
    {H R X I : Subgroup G} (hs : SelectedSourceModels H R)
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hIX : I ≤ X) (hKI : residual H ≤ I)
    {q : ℕ} (hq : q.Prime) (ho : Odd q) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    (∀ k : ℕ, 0 < k → ¬ ClassicalGroup.IsPSL Ibar 2 (q^k)) ∧
      ¬ (ClassicalGroup.IsPSL Ibar 3 q ∨ ClassicalGroup.IsPSU Ibar 3 q ∨
        IsSL Ibar 3 q ∨ IsSU Ibar 3 q) := by
  constructor
  · intro k hk hm
    apply hs.original_residual_common_section_rank hn hIX hKI
    dsimp only
    intro j _
    exact radical_rank_of_odd_linear_two j hq ho hk hm
  · intro hm
    apply hs.original_residual_common_section_rank hn hIX hKI
    dsimp only
    intro j _
    rcases hm with hm | hm | hm | hm
    · exact radical_rank_of_projective_ternary j ho (.inl hm)
    · exact radical_rank_of_projective_ternary j ho (.inr hm)
    · exact radical_rank_of_special_ternary j ho (.inl hm)
    · exact radical_rank_of_special_ternary j ho (.inr hm)

private theorem radical_rank_of_not_sixteen
    {Z : Type*} [Group Z] [Finite Z] (h16 : ¬ 16 ∣ Nat.card Z)
    (P : Subgroup Z) : primeRank 2 (P ⧸ solvableRadical P) ≤ 3 := by
  by_contra! hn
  obtain ⟨E,_,hE⟩ := exists_elementaryAbelian_card_primeRank
    (G := P ⧸ solvableRadical P) (p := 2)
  have hd : 16 ∣ Nat.card E := by
    rw [hE]
    exact Nat.pow_dvd_pow 2 (show 4 ≤ primeRank 2 (P ⧸ solvableRadical P) by omega)
  exact h16 (hd.trans (E.card_subgroup_dvd_card.trans
    ((card_quotient_dvd_card _).trans P.card_subgroup_dvd_card)))

private theorem alternating_small_not_sixteen {m : ℕ} (hl : 5 ≤ m) (hu : m ≤ 7) :
    ¬ 16 ∣ Nat.card (alternatingGroup (Fin m)) := by
  interval_cases m <;> rw [nat_card_alternatingGroup,Nat.card_fin] <;> norm_num

/-- Small alternating, their cubic covers, and J₁ cannot contain the
original diagram residual through the common two-core quotient. -/
theorem SelectedSourceModels.parabolic_common_not_small
    {H R X I : Subgroup G} (hs : SelectedSourceModels H R)
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hIX : I ≤ X) (hKI : residual H ≤ I) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    (∀ m : ℕ, 5 ≤ m → m ≤ 7 → ¬ IsAlternating Ibar m) ∧
      (∀ m : ℕ, 5 ≤ m → m ≤ 7 → ¬ IsAlternatingCover Ibar m) ∧
      ¬ Nonempty (Ibar ≃* Janko1.Model) := by
  refine ⟨?_,?_,?_⟩
  · intro m hl hu ⟨e⟩
    apply hs.original_residual_common_section_rank hn hIX hKI
    dsimp only
    intro j _
    let : Group.IsSolvable (e.toMonoidHom.comp j).ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      infer_instance
    exact radical_rank_of_solvableKernel (e.toMonoidHom.comp j)
      (radical_rank_of_not_sixteen (alternating_small_not_sixteen hl hu))
  · intro m hl hu ⟨_,_,⟨e⟩⟩
    apply hs.original_residual_common_section_rank hn hIX hKI
    dsimp only
    intro j _
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    let q := QuotientGroup.mk' (center Ibar)
    let : Group.IsSolvable q.ker := by
      rw [QuotientGroup.ker_mk']
      exact Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp b.property a))
    let : Group.IsSolvable (q.comp j).ker := by
      rw [←MonoidHom.comap_ker]
      exact isSolvable_comap_of_solvable_ker j q.ker
    let : Group.IsSolvable (e.toMonoidHom.comp (q.comp j)).ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      infer_instance
    exact radical_rank_of_solvableKernel (e.toMonoidHom.comp (q.comp j))
      (radical_rank_of_not_sixteen (alternating_small_not_sixteen hl hu))
  · intro ⟨e⟩
    apply hs.original_residual_common_section_rank hn hIX hKI
    dsimp only
    intro j _
    let : Group.IsSolvable (e.toMonoidHom.comp j).ker := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
      infer_instance
    apply radical_rank_of_solvableKernel (e.toMonoidHom.comp j)
    apply radical_rank_of_not_sixteen
    rw [Janko1.card_model]
    norm_num


/-- A Bender common container forces equality first with the original
residual and then with its proper selected parabolic, a contradiction. -/
theorem LocalData.parabolic_common_not_bender
    {T : Sylow 2 G} {L H A B D R X I : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D R) (hs : SelectedSourceModels H R)
    (hTH : (T : Subgroup G) ≤ H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I) :
    ¬ ClassificationModels.IsBenderModel
      ((I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) := by
  intro hm
  let K := residual H
  have hKH : K ≤ H := map_subtype_le _
  have hKX : K ≤ X := hKH.trans hHX
  have hKlocal : K ∈ ChapterA.Section03.localCComponents (T : Subgroup G) := by
    change (K.subgroupOf (K ⊔ (T : Subgroup G))).IsCComponent
    rw [show K ⊔ (T : Subgroup G) = H from residual_sup_sylow T H hTH]
    exact hs.residual_component_of_not_right hn
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  let eI := (cComponentTwoCoreQuotientEquiv hI).symm.trans
    (QuotientGroup.congr _ _ (subgroupOfEquivOfLe hIX)
      (pCore_map_iso 2 (subgroupOfEquivOfLe hIX)))
  have heX : K.subgroupOf X = I.subgroupOf X :=
    Chapter1.Section02.MovedMaximality.eq_of_bender_quotient (T.subtype (hTH.trans hHX))
      (ChapterA.Section03.SourceEmbeddings.local_restrict hKlocal hKX)
      hI (subgroupOf_mono X hKI) (hm.of_mulEquiv (cComponentTwoCoreQuotientEquiv hI))
  have he : K = I := by
    simpa only [map_subgroupOf_eq_of_le hKX,map_subgroupOf_eq_of_le hIX] using
      congrArg (map X.subtype) heX
  have hb : ClassificationModels.IsBenderModel (K ⧸ pCore 2 K) := by
    rw [he]
    exact hm.of_mulEquiv eI.symm
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [K,subgroupOf_self] using
      (hs.residual_component_of_not_right hn).subgroupOf_of_le (le_refl K) hKH
  obtain ⟨S,_,hR⟩ := d.right_local_in_residual hTH
  let eTop := QuotientGroup.congr _ _ (topEquiv (G := K))
    (pCore_map_iso 2 (topEquiv (G := K)))
  have heR : R.subgroupOf K = ⊤ :=
    Chapter1.Section02.MovedMaximality.eq_of_bender_quotient S hR htop le_top
      (hb.of_mulEquiv eTop)
  exact (d.right_lt_residual hTH c hd hz).not_ge (subgroupOf_eq_top.mp heR)

/-- The ordinary common container has only rank-two or binary linear, A₈ or
sporadic simple models; its cubic cover is binary ternary or 3.M₂₂. -/
theorem LocalData.parabolic_common_model_sieve
    {T : Sylow 2 G} {L H A B D R X I : Subgroup G} {p : ℕ}
    (d : LocalData T L H B D R) (hs : SelectedSourceModels H R)
    (hTH : (T : Subgroup G) ≤ H) (c : CartanPair T L H A B)
    (hd : CartanPrimeActor A H p D) (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hn : ¬ (R.subgroupOf H).IsCComponent) (hHX : H ≤ X)
    (hIX : I ≤ X) (hI : (I.subgroupOf X).IsCComponent) (hKI : residual H ≤ I)
    (hm : let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
      (IsSimpleGroup Ibar ∧ TheoremCModel Ibar) ∨
        (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧ ThreeCoverModel Ibar)) :
    let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
    (IsSimpleGroup Ibar ∧
      (IsAlternating Ibar 8 ∨
        RankTwoTheoremC Ibar ∨
        (∃ m : ℕ, (m = 4 ∨ m = 5) ∧ ClassicalGroup.IsPSL Ibar m 2) ∨
        ∃ name : ClassificationModels.SporadicName, name ≠ .j3 ∧ Nonempty (Ibar ≃* name.Carrier))) ∨
      (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
        ((∃ (unitary : Bool) (f : ℕ), 1 ≤ f ∧
          (2^f) % 3 = (if unitary then 2 else 1) ∧ IsSLSign Ibar unitary 3 (2^f)) ∨
          IsM22Cover Ibar)) := by
  have hnodd := fun {q : ℕ} (hq : q.Prime) (ho : Odd q) =>
    hs.parabolic_common_not_odd hn hIX hKI hq ho
  obtain ⟨ha,hac,hj⟩ := hs.parabolic_common_not_small hn hIX hKI
  rcases hm with ⟨hsimple,hm⟩ | ⟨hc,hm⟩
  · left
    refine ⟨hsimple,?_⟩
    cases hm with
    | alternating m hm he =>
        have he8 : m = 8 := by
          by_contra hne
          exact ha m hm.1 (by omega) he
        exact .inl (he8 ▸ he)
    | linear_odd q k hq ho hk _ he =>
        exact ((hnodd hq ho).1 k (by rcases hk with rfl | rfl <;> decide) he).elim
    | three_odd q hq ho u he =>
        apply ((hnodd hq ho).2 ?_).elim
        cases u
        · exact .inl he
        · exact .inr (.inl he)
    | rank_one he => exact (d.parabolic_common_not_bender hs hTH c hd hz hn hHX hIX hI hKI he).elim
    | rank_two he => exact .inr (.inl he)
    | binary_linear m hm he => exact .inr (.inr (.inl ⟨m,hm,he⟩))
    | sporadic name hname he => exact .inr (.inr (.inr ⟨name,hname,he⟩))
    | janko_one he => exact (hj he).elim
  · right
    refine ⟨hc,?_⟩
    cases hm with
    | classical u q hq he =>
        rcases hq with ⟨f,hf,rfl,hmod⟩ | ⟨hq,ho⟩
        · exact .inl ⟨u,f,hf,hmod,he⟩
        · apply ((hnodd hq ho).2 ?_).elim
          cases u
          · exact .inr (.inr (.inl he))
          · exact .inr (.inr (.inr he))
    | alternating_six he => exact (hac 6 (by decide) (by decide) he).elim
    | alternating_seven he => exact (hac 7 (by decide) (by decide) he).elim
    | mathieu he => exact .inr he

/-- The same original prime pair with every odd and Bender common container
and the small alternating and J₁ rows excluded, preserving full Sylow and quotient markings. -/
theorem source_prime_pair_parabolic_common_sieve
    {T : Sylow 2 G} {L W H A B D : Subgroup G} {n p : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D) :
    ∃ R : Subgroup G, LocalData T L H B D R ∧ SelectedSourceModels H R ∧
      (((generated L H D R).pCoreIn 2 = ⊥ ∧
        ChapterF.Source.HypothesisF11 ![D ⊔ Global.sourceS L H,R] (Global.sourceS L H)) ∨
       ((generated L H D R).pCoreIn 2 ≠ ⊥ ∧
        ¬ D ≤ normalizer (R : Set G) ∧
        (normalizingSylow T R).relIndex (T : Subgroup G) = 2 ∧
        (ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4 → p = 5 ∧ n ≠ 2) ∧
        ∃ P : Sylow 2 (extension T L H B D R),
          let T₁ := (P : Subgroup (extension T L H B D R)).map (extension T L H B D R).subtype
          normalizingSylow T R < T₁ ∧
          T₁ ≤ normalizer ((D ⊔ normalizingSylow T R : Subgroup G) : Set G) ∧
          ∃ U : Sylow 2 G, (U : Subgroup G) = T₁ ∧
            ¬ (R.subgroupOf H).IsCComponent ∧
            (∃ f : ℕ, 1 < f ∧ ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 (2 ^ f) ∧
              (ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               LocalModels.IsSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 (2 ^ f) ∨
               ClassicalGroup.IsPSp ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 (2 ^ f))) ∧
            let X := normalizer (normalizingSylow T R : Set G) ⊔ H
            ∃ I : Subgroup G, residual H ≤ I ∧ I ≤ X ∧
              (I.subgroupOf X).IsCComponent ∧ (I.subgroupOf X).Normal ∧
              conjugateSpanBy R (U : Subgroup G) < I ∧
              let Ibar := (I.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
              IsQuasisimple Ibar ∧
                ((IsSimpleGroup Ibar ∧
                  (IsAlternating Ibar 8 ∨
                    RankTwoTheoremC Ibar ∨
                    (∃ m : ℕ, (m = 4 ∨ m = 5) ∧ ClassicalGroup.IsPSL Ibar m 2) ∨
                    ∃ name : ClassificationModels.SporadicName,
                      name ≠ .j3 ∧ Nonempty (Ibar ≃* name.Carrier))) ∨
                  (Nonempty (center Ibar ≃* Multiplicative (ZMod 3)) ∧
                    ((∃ (unitary : Bool) (f : ℕ), 1 ≤ f ∧
                      (2^f) % 3 = (if unitary then 2 else 1) ∧
                      IsSLSign Ibar unitary 3 (2^f)) ∨ IsM22Cover Ibar))))) := by
  obtain ⟨R,d,hs,hcases⟩ := source_prime_pair_parabolic_ordinary_common_container h hH hgen hthree c hd
  refine ⟨R,d,hs,?_⟩
  rcases hcases with hz | ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,hm⟩
  · exact .inl hz
  exact .inr ⟨hz,hD,hi,hA5,P,hlt,hDT,U,hU,hn,hfield,I,hKI,hIX,hI,hIn,horbit,hquasi,
    d.parabolic_common_model_sieve hs hH.1.1.2 c hd hz hn le_sup_right hIX hI hKI hm⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
