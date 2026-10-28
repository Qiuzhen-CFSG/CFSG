module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalPairedPrime
public import Theory.SpecificGroups.Triality.BinaryLocalResidual

/-!
# The actual binary-triality arms parabolic in local Cartan escape

The remaining rank-two row has an unmoved residual and a normal containing
component. In the original quotient Y/O₂(Y), restrict the full Sylow to
that component. Perfectness and the binary arms calculation identify the
whole residual image with the full arms parabolic. Thus its normalizer
inside the containing image is exactly itself, and it contains that
image's full Sylow two-subgroup. The original Cartan acts through
conjugation on this same quotient and moves the marked arms parabolic.
Its cyclicity, odd order, right-Hall normalization, Sylow permutability
and solvability are retained in the actual induced action.

The final source application retains the preceding containing exclusions
and constructs this marking on the same seed and component. This is a
marked reduction of the remaining binary-triality action case; it does
not assert the Cartan preserves that Sylow or that the original left
field degree equals three. The binary-triality exclusion, paired J₁ and
remaining non-Lie cases still belong to the local sieve assembly.

Source: Aschbacher--Smith 5.1.12--13, printed pp.635--638.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The literal residual and full Sylow images in the original Y/O₂(Y),
with an actual marking of their containing component. -/
@[expose] def BinaryArmsPlacement (T : Sylow 2 G) (H Y : Subgroup G) (C : Subgroup Y) : Prop :=
  let q := QuotientGroup.mk' (pCore 2 Y)
  let R := (((residual H).subgroupOf Y).map q).subgroupOf (C.map q)
  let S := (((T : Subgroup G).subgroupOf Y).map q).subgroupOf (C.map q)
  ∃ e : C.map q ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one,
    S.map e.toMonoidHom = Triality.Standard.Parabolics.unipotent
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) ∧
    R.map e.toMonoidHom = Triality.Standard.Parabolics.parabolic
      (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .arms ∧
    S ≤ R ∧ normalizer (R : Set (C.map q)) = R

/-- The action uses the original quotient and a marking of its same full
Sylow and residual images. -/
@[expose] def BinaryArmsAction (T : Sylow 2 G) (H A B Y : Subgroup G) (C : Subgroup Y) : Prop :=
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let R := (((residual H).subgroupOf Y).map q).subgroupOf Cbar
  let S := (((T : Subgroup G).subgroupOf Y).map q).subgroupOf Cbar
  ∃ hn : Cbar.Normal, letI : Cbar.Normal := hn
    ∃ e : Cbar ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one,
      S.map e.toMonoidHom = Triality.Standard.Parabolics.unipotent
        (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) ∧
      R.map e.toMonoidHom = Triality.Standard.Parabolics.parabolic
        (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .arms ∧
      let f := ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal).comp q
      let Dbar := (A.subgroupOf Y).map f
      let Bbar := (B.subgroupOf Y).map f
      let Tbar := ((T : Subgroup G).subgroupOf Y).map f
      IsCyclic Dbar ∧ Odd (Nat.card Dbar) ∧
      Bbar ≤ normalizer (Dbar : Set _) ∧
      Chapter1.IsSylowIn 2 Tbar f.range ∧
      (Dbar : Set (MulAut (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one))) * (Tbar : Set _) =
        (Tbar : Set _) * (Dbar : Set (MulAut (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one))) ∧
      Group.IsSolvable (Dbar ⊔ Tbar : Subgroup _) ∧
      ∃ d ∈ Dbar,
        (Triality.Standard.Parabolics.parabolic
          (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .arms).map d.toMonoidHom ≠
        Triality.Standard.Parabolics.parabolic
          (Triality.Standard.binaryParameters 1 Nat.zero_lt_one) .arms

namespace LocalSieve

/-- Binary triality identifies the whole original residual image as the
perfect arms parabolic, preserving the full Sylow and both quotient maps. -/
theorem binaryTriality_residual_arms
    {T : Sylow 2 G} {K H A Y : Subgroup G}
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hKH : K ≤ H) (hTH : (T : Subgroup G) ≤ H)
    (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    K = residual H ∧ C.Normal ∧ BinaryArmsPlacement T H Y C := by
  obtain ⟨hKR,hCn⟩ := binaryTriality_seed_eq_residual_and_normal hG hKH hTH hK hKT horbit
    hY hescape C hC hKC hm
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Kbar := (K.subgroupOf Y).map q
  let Cbar := C.map q
  let S := T.subtype (hTH.trans hY.2)
  let P := S.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 Y))
  have hlocal : K.subgroupOf Y ∈ Chapter1.L Y (S : Subgroup Y) :=
    (Chapter1.mem_LIn_iff_subgroupOf (hTH.trans hY.2) (hKH.trans hY.2)).mp
      ⟨hKH.trans hY.2,hK⟩
  have hlocalbar : Kbar ∈ ChapterA.Section03.localCComponents P := by
    change (K.subgroupOf Y).map q ∈ ChapterA.Section03.localCComponents ((S : Subgroup Y).map q)
    exact Chapter1.Section02.mem_L_map_twoCore_mem_localCComponents hlocal
  have hlt : Kbar < Cbar := seed_image_lt_container hG hKH hTH hK horbit hY hescape C hC hKC
  let := hCn
  let : Cbar.Normal := Subgroup.Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  have hn : (P : Subgroup (Y ⧸ pCore 2 Y)) ≤ normalizer (Kbar : Set _) := by
    apply (map_mono (f := q) ?_).trans (le_normalizer_map q)
    rw [←subgroupOf_normalizer_eq (hKH.trans hY.2)]
    exact comap_mono (hKR ▸ hTH.trans (le_normalizer_residual H))
  obtain ⟨U,hU⟩ := P.exists_subgroupOf_eq_of_normal Cbar
  let R := Kbar.subgroupOf Cbar
  let b : R ≃* Kbar := subgroupOfEquivOfLe hlt.le
  let := Chapter1.mem_L_isPerfect hlocal
  let : Group.IsPerfect Kbar := Group.IsPerfect.ofSurjective (q.subgroupMap_surjective _)
  let : Group.IsPerfect R := Group.IsPerfect.ofSurjective (f := b.symm.toMonoidHom) b.symm.surjective
  have hproper : R ≠ ⊤ := fun he => hlt.not_ge (subgroupOf_eq_top.mp he)
  have hns : ¬ Group.IsSolvable R := by
    intro hs
    let := hs
    let : Group.IsSolvable Kbar := Group.isSolvable_of_surjective (f := b.toMonoidHom) b.surjective
    exact hlocalbar.not_isSolvable (Group.isSolvable_of_isSolvable_injective
      (f := (subgroupOfEquivOfLe (show Kbar ≤ Kbar ⊔ (P : Subgroup _) from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).injective)
  have hUR : (U : Subgroup Cbar) ≤ normalizer (R : Set Cbar) := by
    rw [hU,←subgroupOf_normalizer_eq hlt.le]
    exact comap_mono hn
  have hm' : Triality.Standard.IsTrialityGroupAt (2 ^ 1) (C ⧸ pCore 2 C) := by
    simpa only [pow_one] using hm
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff _ 1 Nat.zero_lt_one).mp hm'
  let eC : Cbar ≃* Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one :=
    (cComponentTwoCoreQuotientEquiv hC).symm.trans e
  obtain ⟨a,ha,hR⟩ := Triality.Standard.BinaryLocalSections.marked_arms
    eC U R hproper hns hUR
  obtain ⟨hSR,hN⟩ := Triality.Standard.BinaryLocalSections.sylow_le_and_normalizer_eq
    eC U R hproper hns hUR
  refine ⟨hKR,hCn,?_⟩
  unfold BinaryArmsPlacement
  refine ⟨a,?_,?_,?_,?_⟩
  · simpa only [hU,P,S,Sylow.coe_mapSurjective,Sylow.coe_subtype] using ha
  · simpa only [R,Kbar,hKR] using hR
  · simpa only [hU,P,S,Sylow.coe_mapSurjective,Sylow.coe_subtype,R,Kbar,hKR] using hSR
  · simpa only [R,Kbar,hKR] using hN

private theorem normalizes_of_marked_fixed
    {Q : Type*} [Group Q] (C R : Subgroup G) [C.Normal]
    (hRC : R ≤ C) (e : C ≃* Q) (x : G)
    (he : ((R.subgroupOf C).map e.toMonoidHom).map
      ((MulAut.congr e) (MulAut.conjNormal x)).toMonoidHom =
        (R.subgroupOf C).map e.toMonoidHom) :
    x ∈ normalizer (R : Set G) := by
  apply mem_normalizer_fintype
  intro r hr
  have hh : (MulAut.congr e) (MulAut.conjNormal x) (e ⟨r,hRC hr⟩) ∈
      (R.subgroupOf C).map e.toMonoidHom :=
    he ▸ mem_map_of_mem _ (mem_map_of_mem e.toMonoidHom hr)
  obtain ⟨s,hs,heq⟩ := hh
  have heq' : e s = e (MulAut.conjNormal x ⟨r,hRC hr⟩) := by
    simpa only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.coe_toMonoidHom,
      e.symm_apply_apply] using heq
  have hv : (s : G) = x * r * x⁻¹ := congrArg Subtype.val (e.injective heq')
  exact hv ▸ hs

/-- The original escape produces a cyclic odd action moving the whole marked
arms parabolic, with the actual right Hall and full Sylow action. -/
theorem binaryTriality_escaping_arms_action
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (hKT : K ⊔ (T : Subgroup G) = H)
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C)) :
    BinaryArmsAction T H A B Y C := by
  obtain ⟨hKR,hCn,e,hS,hR,_,_⟩ := binaryTriality_residual_arms h.qtke hKH hH.1.1.2
    hK hKT horbit hY hescape C hC hKC hm
  let q := QuotientGroup.mk' (pCore 2 Y)
  let Cbar := C.map q
  let Rbar := ((residual H).subgroupOf Y).map q
  let : Cbar.Normal := Subgroup.Normal.map hCn q (QuotientGroup.mk'_surjective _)
  let f : Y →* MulAut (Triality.Standard.BinaryCarrier 1 Nat.zero_lt_one) :=
    ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal).comp q
  have hRCY : (residual H).subgroupOf Y ≤ C := by
    intro x hx
    obtain ⟨z,hz,he⟩ := hKC (hKR.symm ▸ hx)
    exact (show z = x from Subtype.ext he) ▸ hz
  have hRC : Rbar ≤ Cbar := map_mono hRCY
  have hTY := hH.1.1.2.trans hY.2
  let : IsCyclic A := (c.left_cyclic_and_card h.sylow_normalizes h.linear).1
  let j : A.subgroupOf Y →* A := {
    toFun x := ⟨x.val,x.property⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun a : A => (a : G)) he
  let : IsCyclic (A.subgroupOf Y) := isCyclic_of_injective j hj
  have ho : Odd (Nat.card A) := by
    rw [←Nat.card_congr (subgroupOfEquivOfLe c.left_le).toEquiv]
    exact OddHall.odd_hall_odd c.left_hall
  have ho' : Odd (Nat.card (A.subgroupOf Y)) :=
    ho.of_dvd_nat (card_dvd_of_injective j hj)
  have hBA : B.subgroupOf Y ≤ normalizer (A.subgroupOf Y : Set Y) := by
    intro b hb
    apply mem_normalizer_iff.mpr
    intro a
    exact mem_normalizer_iff.mp (c.right_normalizes_left hb) (a : G)
  unfold BinaryArmsAction
  refine ⟨inferInstance,e,hS,hR,?_,ho'.of_dvd_nat (card_map_dvd _ f),
    (map_mono hBA).trans (le_normalizer_map f),?_,
    c.image_intersection_permutes_sylow h.sylow_normalizes hTY f,
    h.cartan_sylow_action_isSolvable c hTY f,?_⟩
  · exact isCyclic_of_surjective (f.subgroupMap (A.subgroupOf Y))
      (f.subgroupMap_surjective _)
  · let S := (T.subtype hTY).mapSurjective f.rangeRestrict_surjective
    refine ⟨S,?_⟩
    change (((T : Subgroup G).subgroupOf Y).map f.rangeRestrict).map f.range.subtype = _
    rw [Subgroup.map_map]
    rfl
  · classical
    by_contra hno
    push Not at hno
    apply hescape
    apply (residual_escape_twoCore_iff h.qtke h.sylow_normalizes hH hgen hY.2).mp
    intro z hz
    obtain ⟨y,hy,rfl⟩ := hz
    apply normalizes_of_marked_fixed Cbar Rbar hRC e (q y)
    rw [hR]
    exact hno (f y) (mem_map_of_mem f hy)

end LocalSieve

open Chapter1.Section02.LocalModels
/-- The full original escape retains all checked exclusions and marks its
remaining binary-triality branch on the actual containing image, together
with the original escaping cyclic odd action on the whole parabolic. -/
theorem localCartan_escape_seed_binaryArms_reduction
    {T : Sylow 2 G} {L W H A B Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G)) :
    ∃ K : Subgroup G, K ≤ H ∧ (K.subgroupOf H).IsCComponent ∧
      IsQuasisimple (K ⧸ pCore 2 K) ∧ K ⊔ (T : Subgroup G) = H ∧
      K ∈ Chapter1.L G (T : Subgroup G) ∧
      componentOrbit K (T : Subgroup G) = residual H ∧
      ∃ C : Subgroup Y, C.IsCComponent ∧ K ≤ C.map Y.subtype ∧
        residual H < componentOrbit (C.map Y.subtype) (T : Subgroup G) ∧
        ((componentOrbit (C.map Y.subtype) (T : Subgroup G)).subgroupOf Y).Normal ∧
        (K.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 Y)) <
          C.map (QuotientGroup.mk' (pCore 2 Y)) ∧
        ¬ SolvableSylowOvergroups (C ⧸ pCore 2 C) ∧
        (∀ m : ℕ, 0 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨ IsSU (C ⧸ pCore 2 C) 3 (2 ^ m))) ∧
        (RankTwoTheoremC (C ⧸ pCore 2 C) →
          K = residual H ∧ C.Normal ∧
          Triality.Standard.IsTrialityGroupAt 2 (C ⧸ pCore 2 C) ∧
          ClassicalGroup.IsPSL ((pResidual 2 H) ⧸ pCore 2 (pResidual 2 H)) 2 8 ∧
          BinaryArmsPlacement T H Y C ∧ BinaryArmsAction T H A B Y C) ∧
        (∀ p : ℕ, p.Prime → Odd p →
          ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 p) ∧
        ¬ ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 2 25 ∧
        (C.Normal ∨ ((normalizer (C : Set Y)).index = 2 ∧
          K < residual H ∧ ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 4 ∧
          IsElementaryAbelian 3 B ∧ Nat.card B = 9 ∧
          Nonempty ((C ⧸ pCore 2 C) ≃* Janko1.Model))) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,hrank,hprime,h25,hpair⟩ :=
    localCartan_escape_seed_pairedPrime_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hqlt,hsol,hternary,?_,hprime,h25,hpair⟩
  intro hm
  obtain ⟨he,hCn,ht,hsection⟩ := hrank hm
  exact ⟨he,hCn,ht,hsection,
    (LocalSieve.binaryTriality_residual_arms h.qtke hKH hH.1.1.2 hKL hKT hR
      hY hescape C hC hKC ht).2.2,
    LocalSieve.binaryTriality_escaping_arms_action h hH hgen c hKH hKL hKT hR
      hY hescape C hC hKC ht⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
