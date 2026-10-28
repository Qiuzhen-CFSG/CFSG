module
public import CFSG.Quasithin.ChapterC.Section06.AlternatingKernel
public import CFSG.Quasithin.ChapterC.Section06.Thompson.AlternatingOriginal
public import Theory.GroupTheory.FourFamilyAction.Thompson
/-!
# The original A₅ global alternative of C.6.1

The genuine four-family is labelled by its four distinct permutation images.
The original core normalizer bound, the faithful family kernel, and proved
Thompson stability identify the chosen index-two group with N_Λ(R).
The four-point normalizer theorem then gives either Λ=N_Λ(R), or the literal
dihedral quotient N_Λ(N_Λ(R))/J(R), together with the mixed-product normalizer
bound. Every action and quotient premise is discharged from the original C.5
configuration; the Chapter 2 consumer constructs that configuration.

Source: Aschbacher--Smith C.6.1(6a),(6c), printed pp.165--166.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
open ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.AlternatingFamily
variable {G : Type*} [Group G] [Finite G] {H M K R L : Subgroup G}

theorem alternating_labelled_family_from_original
    (c : OriginalHypotheses H M K R R) (h : AlternatingPairSetup R K L)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    ∃ f : Fin 4 → Subgroup G, Function.Injective f ∧
      Set.range f = elementaryAbelianMaxSubgroups R ∧
      f 0 = H.pCoreIn 2 ∧ f 1 = (H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom ∧
      (H.pCoreIn 2).relIndex (f 2) = 2 ∧
      {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {f 0,f 1} := by
  have hRK := c.R_le_H.trans c.normalizes_residual
  have hH : H = K ⊔ R := c.residual_sup_sylow.symm
  have hno (W : Subgroup G) (hWR : W ≤ R) (hHW : H ≤ normalizer (W : Set G))
      (hMW : M ≤ normalizer (W : Set G)) : W = ⊥ :=
    c.no_common_normal W hWR ((normal_subgroupOf_iff_le_normalizer
      (hWR.trans (c.R_le_M.trans le_sup_left))).mpr (sup_le hMW hHW))
  have hphi := h.frattini_eq_bot_of_index_two H M R c.T_le c.R_normal hRK hH hno hi x hx hnc
  have hf := alternating_family_from_original c h hi x hx hnc
  let S := ChapterB.baumann R
  let Q := (K ⊔ S).pCoreIn 2
  let W := (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ⊔ (S ⊓ centralizer (K : Set G))
  obtain ⟨B₀,B₁,hfam,h0,h1⟩ := h.family_eq_four x (c.R_normal hx) hnc hphi
  change elementaryAbelianMaxSubgroups R = {Q,W,B₀,B₁} at hfam
  change actionImage h.action B₀ = line 0 at h0
  change actionImage h.action B₁ = line 1 at h1
  have hQi : actionImage h.action Q = ⊥ := by
    unfold actionImage
    rw [Subgroup.map_eq_bot_iff,h.action_kernel]
    intro q hq
    exact (h.core.le (show (q : G) ∈ Q from hq)).2
  have hWi : actionImage h.action W = ChapterB.Offenders.D 5 := by
    have hVS : (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤ S :=
      (map_mono h.module_le).trans_eq (mem_normalizer_iff_map_conj_eq.mp
        (normalizer_le_normalizer_baumann R (c.R_normal (M.inv_mem hx))))
    rw [actionImage_sup h.action (hVS.trans le_sup_right) (inf_le_left.trans le_sup_right)]
    have hd : actionImage h.action (S ⊓ centralizer (K : Set G)) = ⊥ :=
      le_bot_iff.mp ((actionImage_mono h.action (show S ⊓ centralizer (K : Set G) ≤ Q
        from le_sup_right.trans_eq h.product.symm)).trans hQi.le)
    rw [hd,sup_bot_eq]
    exact h.conjugate_action_image x (c.R_normal hx) hnc
  have hDbot : ChapterB.Offenders.D 5 ≠ ⊥ := by
    intro he
    have hh := congrArg (fun B : Subgroup FivePerm => Nat.card B) he
    rw [Enumeration.actor_card,Nat.card_unique] at hh
    omega
  let f : Fin 4 → Subgroup G := ![Q,W,B₀,B₁]
  have himages : actionImage h.action ∘ f =
      ![⊥,ChapterB.Offenders.D 5,line 0,line 1] := by
    funext i
    fin_cases i
    · exact hQi
    · exact hWi
    · exact h0
    · exact h1
  have hinj : Function.Injective f := by
    have h0bot := line_ne_bot 0
    have h1bot := line_ne_bot 1
    have h0D := line_ne_actor 0
    have h1D := line_ne_actor 1
    have h01 := line_zero_ne_one
    have hi : Function.Injective (actionImage h.action ∘ f) := by
      rw [himages]
      intro i j he
      fin_cases i <;> fin_cases j
      all_goals simp only [Matrix.cons_val,Fin.reduceFinMk,Fin.isValue] at he
      all_goals first
      | rfl
      | exact (hDbot he).elim
      | exact (hDbot he.symm).elim
      | exact (h0bot he).elim
      | exact (h0bot he.symm).elim
      | exact (h1bot he).elim
      | exact (h1bot he.symm).elim
      | exact (h0D he).elim
      | exact (h0D he.symm).elim
      | exact (h1D he).elim
      | exact (h1D he.symm).elim
      | exact (h01 he).elim
      | exact (h01 he.symm).elim
    exact fun i j he => hi (congrArg (actionImage h.action) he)
  have hrange : Set.range f = elementaryAbelianMaxSubgroups R := by
    rw [hfam]
    simp only [f,Matrix.range_cons,Matrix.range_empty,Set.union_empty,Set.singleton_union]
  have hW : W = (H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom :=
    (h.family_structure hRK x (c.R_normal hx) hnc hphi).1.trans
      (congrArg (fun Q : Subgroup G => Q.map (MulAut.conj x⁻¹).toMonoidHom) hf.1)
  have hB : B₀ ∈ elementaryAbelianMaxSubgroups R := by rw [hfam]; simp
  refine ⟨f,hinj,hrange,hf.1,hW,?_,?_⟩
  · have hh := h.extra_family_index B₀ hB h0
    rw [hf.1] at hh
    exact hh
  · change _ = {Q,W}
    have hQ : Q = H.pCoreIn 2 := hf.1
    rw [hQ,hW]
    exact hf.2.2.2.2.2.2.1

theorem alternating_global_from_original
    (c : OriginalHypotheses H M K R R) (h : AlternatingPairSetup R K L)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hRΛ : R < Λ) (hMΛ : M ≤ Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let N₀ := Λ ⊓ normalizer (R : Set G)
    let S := elementaryAbelianMaxJ R
    let N₁ := Λ ⊓ normalizer (N₀ : Set G)
    M = N₀ ∧ elementaryAbelianMaxJ N₀ = S ∧
      (N₀ = Λ ∨ ∃ hn : (S.subgroupOf N₁).Normal,
        letI := hn
        Nonempty ((N₁ ⧸ S.subgroupOf N₁) ≃* DihedralGroup 4) ∧
        ∃ A ∈ elementaryAbelianMaxSubgroups R,
          (H.pCoreIn 2).relIndex A = 2 ∧
          Nat.card R ≤ Nat.card (Λ ⊓ normalizer ((H.pCoreIn 2 ⊔ A : Subgroup G) : Set G) : Subgroup G)) := by
  have hn := alternating_normalizer_from_original c h Λ hΛ hRΛ hcontrol hi x hx hnc
  let N₀ := Λ ⊓ normalizer (R : Set G)
  have hMN : M ≤ N₀ := le_inf hMΛ c.R_normal
  have hM : M = N₀ := by
    apply le_antisymm hMN
    have hh := relIndex_mul_relIndex R M N₀ c.R_le_M hMN
    rw [hi,hn.1] at hh
    exact relIndex_eq_one.mp (by omega)
  have hJ := alternating_thompson_stable_from_original c h hi x hx hnc
  obtain ⟨f,hfinj,hfam,h0,h1,h2,hpair⟩ := alternating_labelled_family_from_original c h hi x hx hnc
  have hQ : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    have hf := alternating_family_from_original c h hi x hx hnc
    have hu := le_sup_left.trans_eq (h.product.symm.trans hf.1)
    exact moduleLayer_ne_bot h.block.2.1 (bot_unique (he ▸ hu))
  have hQR : H.pCoreIn 2 ≤ R := by
    simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hkernel := alternating_family_kernel_from_original c h Λ (hcontrol _ hQ hQR hHQ) hi x hx hnc
  have ha := alternating_action_from_original c h hi x hx hnc
  have hg := FourFamilyAction.thompson_global Λ M R hΛ c.R_le_M hMΛ hi ha.1 hJ f hfinj hfam hpair hkernel
  refine ⟨hM,(congrArg elementaryAbelianMaxJ hM.symm).trans hJ,?_⟩
  rcases hg.2 with hall | hdihedral
  · exact Or.inl (hM.symm.trans hall)
  · right
    let S := elementaryAbelianMaxJ R
    let N := Λ ⊓ normalizer (S : Set G)
    let : (S.subgroupOf N).Normal := normal_subgroupOf_of_le_normalizer inf_le_right
    have hh : Nonempty ((N ⧸ S.subgroupOf N) ≃* DihedralGroup 4) ∧
        ∃ A ∈ elementaryAbelianMaxSubgroups R,
          (H.pCoreIn 2).relIndex A = 2 ∧
          Nat.card R ≤ Nat.card (Λ ⊓ normalizer ((H.pCoreIn 2 ⊔ A : Subgroup G) : Set G) : Subgroup G) := by
      refine ⟨hdihedral.1,f 2,hfam ▸ ⟨2,rfl⟩,h2,?_⟩
      have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) S R bot_le
        (show S ≤ R from sSup_le (fun _ h => h.1))
      rw [relIndex_bot_left,relIndex_bot_left,ha.1] at hcard
      simpa only [h0,←hcard,mul_comm] using hdihedral.2
    let C (N : Subgroup G) : Prop := ∃ hn : (S.subgroupOf N).Normal,
      letI := hn
      Nonempty ((N ⧸ S.subgroupOf N) ≃* DihedralGroup 4) ∧
      ∃ A ∈ elementaryAbelianMaxSubgroups R,
        (H.pCoreIn 2).relIndex A = 2 ∧
        Nat.card R ≤ Nat.card (Λ ⊓ normalizer ((H.pCoreIn 2 ⊔ A : Subgroup G) : Set G) : Subgroup G)
    have hc : C N := ⟨inferInstance,hh⟩
    have he : N = Λ ⊓ normalizer (N₀ : Set G) :=
      hg.1.trans (congrArg (fun B : Subgroup G => Λ ⊓ normalizer (B : Set G)) hM)
    exact he ▸ hc

end CFSG.Quasithin.ChapterC.Section06
