module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanGlobalPrimeOriginalComponent
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.OddThreeFiveSection

/-!
# Odd ternary containers of the selected A₅ section

Restrict the original normalizing Sylow and right factor to the containing
component in X/O₂(X). The local A₅ section theorem identifies that right
image as SL₂(5) and forces the odd ternary field parameter to be five.
For SL₃ and SU₃ covers, the actual projective kernel is a three-group.
Its intersection with the perfect A₅ section is also a two-group, so the
restriction is injective and the same SL₂(5) identification lifts.

In particular a genuine cubic SL₃ cover is excluded: SL₃(5) has trivial
center. The PSU₃(5) and SU₃(5) possibilities remain distinct. The literal
changed-Sylow application also recovers the original actor p=5 and n≠2
from both Cartan markings. These are conditional restrictions on the A₅
branch, not an assertion of the full Cartan normalization theorem.

Source: Aschbacher–Smith A.3.12(9), A.3.14 and A.3.21(a), pp.47–50,55,
applied in 5.2.2, pp.648–649 of `refs/quasithin.pdf`.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
variable {G : Type*} [Group G] [Finite G]

private theorem five_section_through_cubic_kernel
    {Y Z : Type*} [Group Y] [Finite Y] [Group Z] [Finite Z]
    (S : Sylow 2 Y) (U : Subgroup Y)
    (hl : U ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Y) ≤ normalizer (U : Set Y))
    (e5 : (U ⧸ pCore 2 U) ≃* alternatingGroup (Fin 5))
    (f : Y →* Z) (hf : Function.Surjective f) (hk : IsPGroup 3 f.ker)
    {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL Z 3 q ∨ ClassicalGroup.IsPSU Z 3 q) :
    q = 5 ∧ Chapter1.Section02.LocalModels.IsSL U 2 5 := by
  let : Group.IsNilpotent f.ker := hk.isNilpotent
  let r := f.subgroupMap U
  have h3 : IsPGroup 3 r.ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let : Group.IsNilpotent r.ker := h3.isNilpotent
  let : Group.IsPerfect U := by
    let := hl.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show U ≤ U ⊔ (S : Subgroup Y) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (U ⧸ pCore 2 U) := e5.isSimpleGroup
  have h2 := PerfectCoreTwoExtension.ker_isTwoGroup r
  have hi : Function.Injective r := (MonoidHom.ker_eq_bot_iff r).mp
    (disjoint_self.mp (h2.disjoint_of_coprime h3 (by decide)))
  let e : U ≃* U.map f := MulEquiv.ofBijective r ⟨hi,f.subgroupMap_surjective U⟩
  let eq := QuotientGroup.congr _ _ e (pCore_map_iso 2 e)
  let e5' := eq.symm.trans e5
  have hl' := Chapter1.Section02.localCComponents_map_of_solvable_ker hl f
  have hn' := (map_mono (f := f) hn).trans (le_normalizer_map f)
  have hq5 := ChapterA.Section03.SourceEmbeddings.odd_three_five_section_parameter
    (S.mapSurjective hf) (U.map f) hl' hn' ⟨e5'⟩ hq ho hm
  obtain ⟨F,_,_,hF,⟨a⟩⟩ :=
    (ChapterA.Section03.SourceEmbeddings.odd_three_five_section_models
      (S.mapSurjective hf) (U.map f) hl' hn' e5' hq ho hm).2
  exact ⟨hq5,F,inferInstance,inferInstance,hF,⟨e.trans a⟩⟩

private theorem odd_ternary_five_section
    {Y : Type*} [Group Y] [Finite Y]
    (S : Sylow 2 Y) (U : Subgroup Y)
    (hl : U ∈ ChapterA.Section03.localCComponents S)
    (hn : (S : Subgroup Y) ≤ normalizer (U : Set Y))
    (e5 : (U ⧸ pCore 2 U) ≃* alternatingGroup (Fin 5))
    {q : ℕ} (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL Y 3 q ∨ ClassicalGroup.IsPSU Y 3 q ∨
      Chapter1.Section02.LocalModels.IsSL Y 3 q ∨
      Chapter1.Section02.LocalModels.IsSU Y 3 q) :
    q = 5 ∧ Chapter1.Section02.LocalModels.IsSL U 2 5 := by
  rcases hm with hm | hm | hm | hm
  · exact ⟨ChapterA.Section03.SourceEmbeddings.odd_three_five_section_parameter
        S U hl hn ⟨e5⟩ hq ho (.inl hm),
      (ChapterA.Section03.SourceEmbeddings.odd_three_five_section_models
        S U hl hn e5 hq ho (.inl hm)).2⟩
  · exact ⟨ChapterA.Section03.SourceEmbeddings.odd_three_five_section_parameter
        S U hl hn ⟨e5⟩ hq ho (.inr hm),
      (ChapterA.Section03.SourceEmbeddings.odd_three_five_section_models
        S U hl hn e5 hq ho (.inr hm)).2⟩
  · obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    let f := (Matrix.PSL3.projection F).comp e.toMonoidHom
    have hf : Function.Surjective f := (Matrix.PSL3.projection_surjective F).comp e.surjective
    have hk : IsPGroup 3 f.ker := by
      have hz : IsPGroup 3 (center (Matrix.SpecialLinearGroup (Fin 3) F)) := by
        intro x
        refine ⟨1,?_⟩
        exact orderOf_dvd_iff_pow_eq_one.mp
          ((orderOf_dvd_natCard x).trans (Matrix.SL3.card_center_dvd_three F))
      rw [show f.ker = (Matrix.PSL3.projection F).ker.comap e.toMonoidHom from rfl,
        Matrix.PSL3.projection_ker]
      exact hz.comap_of_injective e.toMonoidHom e.injective
    exact five_section_through_cubic_kernel S U hl hn e5 f hf hk hq ho
      (.inl ⟨F,inferInstance,inferInstance,hF,⟨MulEquiv.refl _⟩⟩)
  · obtain ⟨F,_,_,J,hF,hc,⟨e⟩⟩ := hm
    let f := J.specialToProjective.comp e.toMonoidHom
    have hf : Function.Surjective f := J.specialToProjective_surjective.comp e.surjective
    let : Finite (BenderSuzuki.MatrixGroups.ProjectiveSpecialUnitaryMatrixGroup J) :=
      Finite.of_surjective f hf
    have hk : IsPGroup 3 f.ker := by
      have hz : IsPGroup 3 J.specialToProjective.ker :=
        fun x => ⟨1,by simpa using J.specialToProjective_ker_cube x⟩
      exact hz.comap_of_injective e.toMonoidHom e.injective
    exact five_section_through_cubic_kernel S U hl hn e5 f hf hk hq ho
      (.inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨MulEquiv.refl _⟩⟩)

/-- The literal right image in an odd ternary container is SL₂(5), and the
containing field has order five. Both special and projective models are retained. -/
theorem LocalData.source_overcomponent_odd_ternary_A5_section
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n q : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 q ∨
      ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 q) :
    q = 5 ∧
      Chapter1.Section02.LocalModels.IsSL
        ((R.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 2 5 := by
  let π := QuotientGroup.mk' (pCore 2 X)
  let Rbar := (R.subgroupOf X).map π
  let Kbar := (K.subgroupOf X).map π
  obtain ⟨S,hS⟩ := hSyl
  have hTX : normalizingSylow T R ≤ X := hS ▸ map_subtype_le (S : Subgroup X)
  have heS : (S : Subgroup X) = (normalizingSylow T R).subgroupOf X := by
    apply map_injective X.subtype_injective
    rw [map_subgroupOf_eq_of_le hTX]
    exact hS
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 X))
  have hlocal : R.subgroupOf X ∈ Chapter1.L X ((normalizingSylow T R).subgroupOf X) :=
    (Chapter1.mem_LIn_iff_subgroupOf hTX hRX).mp ⟨hRX,d.right_mem_local_family h hH⟩
  have hlocalbar : Rbar ∈ ChapterA.Section03.localCComponents P := by
    change Rbar ∈ ChapterA.Section03.localCComponents ((S : Subgroup X).map π)
    rw [heS]
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hn : (P : Subgroup (X ⧸ pCore 2 X)) ≤ normalizer (Rbar : Set (X ⧸ pCore 2 X)) := by
    change (S : Subgroup X).map π ≤ _
    rw [heS]
    apply (map_mono (f := π) ?_).trans (le_normalizer_map π)
    rw [←subgroupOf_normalizer_eq hRX]
    exact comap_mono (show normalizingSylow T R ≤ normalizer (R : Set G) from inf_le_right)
  have hRKbar : Rbar ≤ Kbar := map_mono (comap_mono hRK)
  let : Group.IsNilpotent (pCore 2 X) := pCore_isNilpotent
  obtain ⟨Q,hQ,hU⟩ := ChapterA.Section03.SourceEmbeddings.exists_local_sylow_restriction
    P hlocalbar hRKbar (hK.map_quotient (pCore 2 X)).subnormal
  let U := Rbar.subgroupOf Kbar
  have hnU : (Q : Subgroup Kbar) ≤ normalizer (U : Set Kbar) := by
    rw [hQ,←subgroupOf_normalizer_eq hRKbar]
    exact comap_mono hn
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let eK : Kbar ≃* (K ⧸ pCore 2 K) :=
    (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  let r := π.subgroupMap (R.subgroupOf X)
  have hr : IsPGroup 2 r.ker := by
    rw [ker_subgroupMap,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_subtype
  let eRX := (subgroupOfEquivOfLe hRX).symm
  let e₁ := QuotientGroup.congr _ _ eRX (pCore_map_iso 2 eRX)
  let e₂ := r.pCoreQuotientEquiv (π.subgroupMap_surjective _) hr
  let b := (subgroupOfEquivOfLe hRKbar).symm
  let e₃ := QuotientGroup.congr _ _ b (pCore_map_iso 2 b)
  let eR : (R ⧸ pCore 2 R) ≃* (U ⧸ pCore 2 U) := e₁.trans (e₂.trans e₃)
  obtain ⟨F,_,_,hF,⟨a⟩⟩ := hA5
  let e5 := (Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four hF).some
  let eU : (U ⧸ pCore 2 U) ≃* alternatingGroup (Fin 5) :=
    eR.symm.trans (a.trans e5)
  have hmK : ClassicalGroup.IsPSL Kbar 3 q ∨ ClassicalGroup.IsPSU Kbar 3 q ∨
      Chapter1.Section02.LocalModels.IsSL Kbar 3 q ∨
      Chapter1.Section02.LocalModels.IsSU Kbar 3 q := by
    rcases hm with hh | hh | hh | hh
    · exact .inl (hh.of_mulEquiv eK)
    · exact .inr (.inl (hh.of_mulEquiv eK))
    · obtain ⟨E,_,_,hE,⟨a⟩⟩ := hh
      exact .inr (.inr (.inl ⟨E,inferInstance,inferInstance,hE,⟨eK.trans a⟩⟩))
    · obtain ⟨E,_,_,J,hE,hc,⟨a⟩⟩ := hh
      exact .inr (.inr (.inr ⟨E,inferInstance,inferInstance,J,hE,hc,⟨eK.trans a⟩⟩))
  obtain ⟨hfield,hmodel⟩ := odd_ternary_five_section Q U hU hnU eU hq ho hmK
  obtain ⟨E,_,_,hE,⟨eE⟩⟩ := hmodel
  exact ⟨hfield,E,inferInstance,inferInstance,hE,⟨b.trans eE⟩⟩

/-- The original A₅ section excludes the cubic linear-cover row, without
replacing its center by a projective quotient. -/
theorem LocalData.source_overcomponent_A5_not_cubic_linear
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n q : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hq : q.Prime) (ho : Odd q)
    (hcenter : Nat.card (center (K ⧸ pCore 2 K)) = 3)
    (hm : Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 q) : False := by
  have hfive := (d.source_overcomponent_odd_ternary_A5_section h hH hSyl
    hRX hKX hRK hK hA5 hq ho (.inr (.inr (.inl hm)))).1
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  have hc := Nat.card_congr (centerCongr e).toEquiv
  rw [hcenter,Atlas.ExceptionalSupport.card_sl_center,hF,hfive] at hc
  norm_num at hc

/-- At the actual smaller changed Sylow, the A₅ ternary branch has field
five, the original quintic actor, and the literal SL₂(5) right image. -/
theorem LocalData.changedSylow_A5_odd_ternary
    {T : Sylow 2 G} {L W H A B D R K : Subgroup G} {n p q : ℕ}
    (d : LocalData T L H B D R) (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H)
    (hthree : ¬ ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 3 4)
    (c : CartanPair T L H A B) (hd : CartanPrimeActor A H p D)
    (hz : (generated L H D R).pCoreIn 2 ≠ ⊥)
    (hs : SelectedSourceModels H R)
    (P : Sylow 2 (extension T L H B D R))
    (hP : (P : Subgroup (extension T L H B D R)).map
      (extension T L H B D R).subtype = normalizingSylow T R)
    (hKX : K ≤ generated L H D R ⊔ normalizingSylow T R) (hRK : R ≤ K)
    (hK : (K.subgroupOf (generated L H D R ⊔ normalizingSylow T R)).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hq : q.Prime) (ho : Odd q)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 q ∨
      ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSL (K ⧸ pCore 2 K) 3 q ∨
      Chapter1.Section02.LocalModels.IsSU (K ⧸ pCore 2 K) 3 q) :
    q = 5 ∧ p = 5 ∧ n ≠ 2 ∧
      let X := generated L H D R ⊔ normalizingSylow T R
      Chapter1.Section02.LocalModels.IsSL
        ((R.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))) 2 5 := by
  have hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R)
      (generated L H D R ⊔ normalizingSylow T R) :=
    Chapter1.IsSylowIn.restrict ⟨P,hP⟩ le_sup_right le_sup_left
  obtain ⟨hq5,hR5⟩ := d.source_overcomponent_odd_ternary_A5_section h hH hSyl
    (le_sup_left.trans (le_sup_right.trans le_sup_left)) hKX hRK hK hA5 hq ho hm
  have hp5 := d.selected_A5_actor_prime h hH hgen c hd hz hs hthree hA5
  refine ⟨hq5,hp5,?_,hR5⟩
  intro hn
  have hc := card_dvd_of_le hd.le_cartan
  rw [hd.card,c.left_card h.linear h.sylow_normalizes,hp5,hn] at hc
  norm_num at hc

open Chapter1.Section02 LocalModels

/-- The A₅ branch of the actual remaining catalogue: the odd ternary
parameter is five, and the only cubic ternary cover is unitary. -/
@[expose] def RemainingA5SourceContainer (X K : Subgroup G) : Prop :=
  let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  A36Common I ∧
    ((IsComponent (X ⧸ pCore 2 X) I ∧ IsSimpleGroup I ∧
      (Nonempty (I ≃* Janko4.Model) ∨
        ClassicalGroup.IsPSL I 3 5 ∨ ClassicalGroup.IsPSU I 3 5)) ∨
    (IsComponent (X ⧸ pCore 2 X) I ∧
      Nonempty (center I ≃* Multiplicative (ZMod 3)) ∧ IsSU I 3 5) ∨
    A36Natural I ∨ A36Nilpotent I)

/-- Apply the field and cubic-center restrictions to the existing catalogue
on its original containing image, retaining all nonternary alternatives. -/
theorem LocalData.remaining_A5_source_container
    {T : Sylow 2 G} {L W H B D R X K : Subgroup G} {n : ℕ} {κ : GroupClass}
    (d : LocalData T L H B D R) (h : Input κ T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hSyl : Chapter1.IsSylowIn 2 (normalizingSylow T R) X)
    (hRX : R ≤ X) (hKX : K ≤ X) (hRK : R ≤ K)
    (hK : (K.subgroupOf X).IsCComponent)
    (hA5 : ClassicalGroup.IsPSL (R ⧸ pCore 2 R) 2 4)
    (hm : RemainingSourceContainer X K) : RemainingA5SourceContainer X K := by
  let I := (K.subgroupOf X).map (QuotientGroup.mk' (pCore 2 X))
  let ec := QuotientGroup.congr _ _ (subgroupOfEquivOfLe hKX)
    (pCore_map_iso 2 (subgroupOfEquivOfLe hKX))
  let e : I ≃* (K ⧸ pCore 2 K) := (cComponentTwoCoreQuotientEquiv hK).symm.trans ec
  obtain ⟨hcommon,hcases⟩ := hm
  refine ⟨hcommon,?_⟩
  rcases hcases with ⟨hc,hs,hj | ⟨q,hq,ho,u,ht⟩⟩ | ⟨hc,hz,q,hq,ho,u,ht⟩ | hn | hn
  · exact .inl ⟨hc,hs,.inl hj⟩
  · have ht' : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 3 q ∨
        ClassicalGroup.IsPSU (K ⧸ pCore 2 K) 3 q := by
      cases u
      · exact .inl (ht.of_mulEquiv e.symm)
      · exact .inr (ht.of_mulEquiv e.symm)
    have heq := (d.source_overcomponent_odd_ternary_A5_section h hH hSyl hRX hKX hRK hK
      hA5 hq ho (ht'.imp_right (fun hh => .inl hh))).1
    subst q
    refine .inl ⟨hc,hs,.inr ?_⟩
    cases u
    · exact .inl ht
    · exact .inr ht
  · have ht' : IsSL (K ⧸ pCore 2 K) 3 q ∨ IsSU (K ⧸ pCore 2 K) 3 q := by
      cases u
      · obtain ⟨F,_,_,hF,⟨a⟩⟩ := ht
        exact .inl ⟨F,inferInstance,inferInstance,hF,⟨e.symm.trans a⟩⟩
      · obtain ⟨F,_,_,J,hF,hc,⟨a⟩⟩ := ht
        exact .inr ⟨F,inferInstance,inferInstance,J,hF,hc,⟨e.symm.trans a⟩⟩
    have heq := (d.source_overcomponent_odd_ternary_A5_section h hH hSyl hRX hKX hRK hK
      hA5 hq ho (.inr (.inr ht'))).1
    subst q
    cases u
    · obtain ⟨F,_,_,hF,⟨a⟩⟩ := ht
      have hzcard : Nat.card (center I) = 3 := by
        rw [Nat.card_congr hz.some.toEquiv]
        exact Nat.card_zmod 3
      have hh := Nat.card_congr (centerCongr a).toEquiv
      rw [hzcard,Atlas.ExceptionalSupport.card_sl_center,hF] at hh
      norm_num at hh
    · exact .inr (.inl ⟨hc,hz,ht⟩)
  · exact .inr (.inr (.inl hn))
  · exact .inr (.inr (.inr hn))

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Prime
