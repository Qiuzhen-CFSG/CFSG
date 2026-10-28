module
public import CFSG.Quasithin.ChapterC.Section06.Thompson.CubicPairOriginal
public import Theory.GroupTheory.FourFamilyAction.Geometry
/-!
# The original paired A₃ global alternative of C.6.1

The actual cubic actions give Thompson stability, the family kernel and the
index of its original Sylow group over J(R). Their four-family geometry
feeds the finite permutation endgame. Thus the chosen index-two overgroup
is N_Λ(R), and either it is Λ or its normalizer has the literal D₈ quotient
and required mixed-product normalizer bound.

Source: Aschbacher--Smith C.6.1(4),(6), printed pp.164--166.
-/

public section
open Subgroup Stellmacher
open Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.Section06
open Section05.BlockAnalysis Section05.ConjugateSource
variable {G : Type*} [Group G] [Finite G] {H M K L R : Subgroup G}

theorem cubic_pair_global_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
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
  have hf := rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
  have hQ : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    let := h.elementary
    have hUC : sourceModule K ≤ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) :=
      le_centralizer_iff.mpr (sup_le (le_centralizer (RankOne.U K))
        ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))))
    have hu := (le_inf (h.module_le.trans inf_le_left) hUC).trans hfull.le
    exact moduleLayer_ne_bot h.short (bot_unique (he ▸ hu))
  have hQR : H.pCoreIn 2 ≤ R := by
    simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hk := cubic_pair_family_kernel_from_original c h h' hK hL hKL hpair ht hfull
    Λ (hcontrol _ hQ hQR hHQ) hi x hx hnc
  have hidx := hk.1
  have hkernel := hk.2
  have hJ := cubic_pair_thompson_stable_from_original c h h' hK hL hKL hpair ht hfull hi x hx hnc
  have hn := rankOne_pair_normalizer_from_original c h h' hKL hpair ht hfull Λ hΛ hRΛ hcontrol hi x hx hnc
  let N₀ := Λ ⊓ normalizer (R : Set G)
  have hMN : M ≤ N₀ := le_inf hMΛ c.R_normal
  have hM : M = N₀ := by
    apply le_antisymm hMN
    have hh := relIndex_mul_relIndex R M N₀ c.R_le_M hMN
    rw [hi,hn.1] at hh
    exact relIndex_eq_one.mp (by omega)
  obtain ⟨P,P',hfamily,hgeometry,_⟩ :=
    cubic_pair_geometry_from_original c h h' hK hL hKL hpair ht hfull hi x hx hnc
  obtain ⟨f,hfinj,hfam,h0,h1,h2,h3,hindex⟩ :=
    FourFamilyAction.labelled_geometry R (ChapterB.baumann R) (H.pCoreIn 2)
      ((H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom) P P' _ hfamily hgeometry
  have hpf : {A ∈ elementaryAbelianMaxSubgroups R | R ≤ normalizer (A : Set G)} = {f 0,f 1} := by
    rw [h0,h1]
    exact hf.2.2.2.2.2.1
  have hg := FourFamilyAction.thompson_global Λ M R hΛ c.R_le_M hMΛ hi hidx hJ f hfinj hfam hpf hkernel
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
      refine ⟨hdihedral.1,f 2,hfam ▸ ⟨2,rfl⟩,hindex,?_⟩
      have hcard := relIndex_mul_relIndex (⊥ : Subgroup G) S R bot_le
        (show S ≤ R from sSup_le (fun _ h => h.1))
      rw [relIndex_bot_left,relIndex_bot_left,hidx] at hcard
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

theorem cubic_pair_normalizer_family_from_original
    (c : OriginalHypotheses H M (K ⊔ L) R R)
    {F F' : Type*} [Field F] [Field F']
    (h : RankOne.Setup R K F) (h' : RankOne.Setup R L F')
    (hK : IsAlternatingBlock K 3) (hL : IsAlternatingBlock L 3)
    (hKL : L ≤ centralizer (K : Set G))
    (hpair : ∀ r ∈ R, K.conjBy r = K ∨ K.conjBy r = L)
    (ht : ∃ t : M, (t : G) ∈ R ∧ K.conjBy (t : G) = L)
    (hfull : R ⊓ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) = H.pCoreIn 2)
    (Λ : Subgroup G) (hΛ : IsPGroup 2 Λ) (hRΛ : R < Λ)
    (hcontrol : ∀ W : Subgroup G, W ≠ ⊥ → W ≤ R → H ≤ normalizer (W : Set G) →
      Λ ⊓ normalizer (W : Set G) = R)
    (hi : R.relIndex M = 2) (x : G) (hx : x ∈ M)
    (hnc : ¬ (sourceModule K).map (MulAut.conj x⁻¹).toMonoidHom ≤
      centralizer (sourceModule K : Set G)) :
    let N₀ := Λ ⊓ normalizer (R : Set G)
    let Q := H.pCoreIn 2
    let S := elementaryAbelianMaxJ R
    R.relIndex N₀ = 2 ∧ ChapterB.baumann R = S ∧
      Q = (K ⊔ L).pCoreIn 2 ⊔ (R ⊓ centralizer ((K ⊔ L : Subgroup G) : Set G)) ∧
      ∀ y ∈ N₀, y ∉ R →
        S = Q ⊔ Q.map (MulAut.conj y⁻¹).toMonoidHom ∧
        ∃ A : Subgroup G, ∃ r : G,
          r ∈ R ∧ r ∉ S ∧ Q.relIndex A = 2 ∧
          elementaryAbelianMaxSubgroups R =
            {Q,Q.map (MulAut.conj y⁻¹).toMonoidHom,A,A.map (MulAut.conj r⁻¹).toMonoidHom} := by
  have hf := rankOne_pair_family_from_original c h h' hKL hpair ht hfull hi x hx hnc
  have hQ : H.pCoreIn 2 ≠ ⊥ := by
    intro he
    let := h.elementary
    have hUC : sourceModule K ≤ centralizer ((sourceModule K ⊔ sourceModule L : Subgroup G) : Set G) :=
      le_centralizer_iff.mpr (sup_le (le_centralizer (RankOne.U K))
        ((map_subtype_le _).trans (hKL.trans (centralizer_le (map_subtype_le _)))))
    have hu := (le_inf (h.module_le.trans inf_le_left) hUC).trans hfull.le
    exact moduleLayer_ne_bot h.short (bot_unique (he ▸ hu))
  have hQR : H.pCoreIn 2 ≤ R := by
    simpa only [c.sylow_image] using pCoreIn_le_sylow H c.sylow
  have hHQ : H ≤ normalizer (H.pCoreIn 2 : Set G) :=
    H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hk := cubic_pair_family_kernel_from_original c h h' hK hL hKL hpair ht hfull
    Λ (hcontrol _ hQ hQR hHQ) hi x hx hnc
  have hn := rankOne_pair_normalizer_from_original c h h' hKL hpair ht hfull Λ hΛ hRΛ hcontrol hi x hx hnc
  obtain ⟨P,P',hfamily,hgeometry,_⟩ :=
    cubic_pair_geometry_from_original c h h' hK hL hKL hpair ht hfull hi x hx hnc
  rw [hf.1] at hgeometry
  have hstrict : elementaryAbelianMaxJ R < R := by
    apply lt_of_le_of_ne (sSup_le (fun _ h => h.1))
    intro he
    change elementaryAbelianMaxJ R = R at he
    have hh := hk.1
    rw [he,relIndex_self] at hh
    omega
  have hall := FourFamilyAction.normalizer_four_family Λ R (elementaryAbelianMaxJ R)
    (H.pCoreIn 2) ((H.pCoreIn 2).map (MulAut.conj x⁻¹).toMonoidHom) P P' _ hRΛ.le hstrict
    hfamily hgeometry hf.2.2.2.2.2.1 hk.2 (hcontrol _ hQ hQR hHQ)
  exact ⟨hn.1,hf.1,hf.2.1,fun y hy hyr => ⟨hn.2.2 y hy hyr,hall y hy hyr⟩⟩

end CFSG.Quasithin.ChapterC.Section06
