module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Residual
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.CommonCore.Action.Cartan.Choice
public import Theory.SpecificGroups.SL2.TwoCoreBorel
public import Theory.SpecificGroups.SL2.SolvableSylowOvergroups
public import Theory.SpecificGroups.RankTwoCoreSolvableSylow
public import CFSG.Quasithin.Chapter3.Section01.LocalGeometry
/-!
# The actual odd Hall group in the rank-one shadow

An odd subgroup of H intersect N_G(L) lies in K = O²(H). The original
Sylow intersection in K maps to a Sylow subgroup of the marked SL2 quotient.
The proper-overgroup theorem places K intersect N_G(L) in its Borel and
embeds every odd subgroup in the field units. Thus its order divides q-1.

The same Borel makes H intersect N_G(L) solvable. The full SL3 and Sp4
solvable-overgroup theorems then give normalization of T intersect L.
H-star minimality identifies the residual intersection with the whole Sylow
normalizer, proving that the relative odd Hall group is nontrivial.
Its O³(A) Omega1(O3(A)) remains nontrivial by the finite 3-group argument.

Source: Aschbacher--Smith, 11.3.7(2,3,5), printed p.773.
-/

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
open CFSG.Quasithin.ChapterB.QuasisimpleSource
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall
@[expose] public noncomputable section
variable {G : Type*} [Group G] [Finite G]
private theorem odd_sylow_disjoint (P : Sylow 2 G) (A : Subgroup G)
    (ho : Odd (Nat.card A)) : Disjoint (P : Subgroup G) A := by
  obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
  apply disjoint_of_coprime_natCard
  rw [hn]
  exact (Nat.coprime_two_left.mpr ho).pow_left n

private theorem units_embedding {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 G)
    (hk : q.ker ≤ (P : Subgroup G)) (A : Subgroup G)
    (hn : A ≤ normalizer (P : Set G)) (ho : Odd (Nat.card A)) :
    ∃ f : A →* Fˣ, Function.Injective f := by
  obtain ⟨f, _, hf⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal q hq P hk
  refine ⟨f.comp (inclusion hn), ?_⟩
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply eq_bot_iff.mpr
  intro a ha
  apply Subtype.ext
  exact disjoint_def.mp (odd_sylow_disjoint P A ho) ((hf (inclusion hn a)).mp ha) a.property

private theorem solvable_proper_overgroup {F : Type*} [Field F] [Finite F] [CharP F 2]
    (q : G →* SL(2,F)) (hq : Function.Surjective q) (P : Sylow 2 G)
    (hk : q.ker ≤ (P : Subgroup G)) (B : Subgroup G)
    (hPB : (P : Subgroup G) ≤ B) (hB : B ≠ ⊤) : Group.IsSolvable B := by
  have hBq : B.map q ≠ ⊤ := by
    intro he
    have hh := comap_map_eq_self (hk.trans hPB)
    rw [he, comap_top] at hh
    exact hB hh.symm
  let := Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
    (P.mapSurjective hq) (B.map q) (map_mono hPB) hBq
  let := (P.isPGroup'.to_le hk).isNilpotent
  let := isSolvable_comap_of_solvable_ker q (B.map q)
  exact Group.isSolvable_of_isSolvable_injective (inclusion_injective (le_comap_map q B))

variable {T : Sylow 2 G} {L V H : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient}

def residualSylow (s : Hypothesis1131At D S U₁ H) : Sylow 2 (outsideResidual H) :=
  (NormalSylowQuotientAction.intersection_sylow T (outsideResidual H)
    (s.outside.1.1.2.trans (outsideResidual_normalized H))).choose

theorem residualSylow_coe (s : Hypothesis1131At D S U₁ H) :
    (residualSylow s : Subgroup (outsideResidual H)) = (T : Subgroup G).subgroupOf (outsideResidual H) :=
  (NormalSylowQuotientAction.intersection_sylow T (outsideResidual H)
    (s.outside.1.1.2.trans (outsideResidual_normalized H))).choose_spec

private theorem residual_intersection_proper (s : Hypothesis1131At D S U₁ H) :
    (normalizer (L : Set G)).subgroupOf (outsideResidual H) ≠ ⊤ := by
  intro he
  have hKM : outsideResidual H ≤ normalizer (L : Set G) := by
    intro k hk
    exact show (⟨k,hk⟩ : outsideResidual H) ∈ (normalizer (L : Set G)).subgroupOf _ from
      he.symm ▸ mem_top _
  apply s.outside.1.2
  rw [← outsideResidual_sup_sylow T H s.outside.1.1.2]
  exact sup_le hKM D.sylow_normalizes_component

private theorem residual_sylow_le (s : Hypothesis1131At D S U₁ H) :
    (residualSylow s : Subgroup (outsideResidual H)) ≤
      (normalizer (L : Set G)).subgroupOf (outsideResidual H) := by
  rw [residualSylow_coe]
  exact comap_mono D.sylow_normalizes_component

def quotientMap (c : NaturalQuotientMarking T H S.field) :
    outsideResidual H →* SL(2,S.field.Carrier) :=
  c.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' _)

theorem quotientMap_surjective (c : NaturalQuotientMarking T H S.field) :
    Function.Surjective (quotientMap c) :=
  c.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _)

theorem quotientMap_ker (c : NaturalQuotientMarking T H S.field) :
    (quotientMap c).ker = pCore 2 (outsideResidual H) := by
  ext x
  change c.quotientEquiv (QuotientGroup.mk' _ x) = 1 ↔ _
  rw [c.quotientEquiv.map_eq_one_iff]
  exact QuotientGroup.eq_one_iff x

theorem residual_intersection_normalizes (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) :
    (normalizer (L : Set G)).subgroupOf (outsideResidual H) ≤
      normalizer (residualSylow s : Set (outsideResidual H)) := by
  apply Matrix.SpecialLinearGroup.proper_overgroup_le_sylow_normalizer_of_two_kernel
    (quotientMap c) (quotientMap_surjective c) (residualSylow s)
  · rw [quotientMap_ker]
    exact pCore_isPGroup.le_sylow_of_normal _
  · exact residual_sylow_le s
  · exact residual_intersection_proper s

theorem residual_intersection_solvable (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) :
    Group.IsSolvable ((normalizer (L : Set G)).subgroupOf (outsideResidual H)) := by
  apply solvable_proper_overgroup (quotientMap c) (quotientMap_surjective c) (residualSylow s)
  · rw [quotientMap_ker]
    exact pCore_isPGroup.le_sylow_of_normal _
  · exact residual_sylow_le s
  · exact residual_intersection_proper s

theorem odd_le_residual (A : Subgroup G) (hAH : A ≤ H) (ho : Odd (Nat.card A)) :
    A ≤ outsideResidual H := by
  have hoH : Odd (Nat.card (A.subgroupOf H)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAH).toEquiv]
    exact ho
  have hr := OddHall.odd_subgroup_le (pResidual 2 H) _ (isPGroup_quotient_pResidual 2) hoH
  intro a ha
  exact ⟨⟨a,hAH ha⟩,hr ha,rfl⟩

theorem source_units_embedding (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G)) (ho : Odd (Nat.card A)) :
    ∃ f : A →* S.field.Carrierˣ, Function.Injective f := by
  have hAK := odd_le_residual A (hA.trans inf_le_left) ho
  have hoK : Odd (Nat.card (A.subgroupOf (outsideResidual H))) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hAK).toEquiv]
    exact ho
  obtain ⟨f,hf⟩ := units_embedding (quotientMap c) (quotientMap_surjective c)
    (residualSylow s) (by rw [quotientMap_ker]; exact pCore_isPGroup.le_sylow_of_normal _)
    (A.subgroupOf (outsideResidual H))
    ((comap_mono (hA.trans inf_le_right)).trans (residual_intersection_normalizes s c)) hoK
  exact ⟨f.comp (subgroupOfEquivOfLe hAK).symm.toMonoidHom,
    hf.comp (subgroupOfEquivOfLe hAK).symm.injective⟩

theorem source_card_dvd (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G)) (ho : Odd (Nat.card A)) :
    Nat.card A ∣ 2 ^ S.field.degree - 1 := by
  obtain ⟨f,hf⟩ := source_units_embedding s c A hA ho
  simpa only [Nat.card_units, S.field.card_eq] using card_dvd_of_injective f hf


theorem source_common_solvable (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) :
    Group.IsSolvable (H ⊓ normalizer (L : Set G) : Subgroup G) := by
  let B := H ⊓ normalizer (L : Set G)
  let r : B →* H ⧸ pResidual 2 H :=
    (QuotientGroup.mk' _).comp (inclusion (show B ≤ H from inf_le_left))
  let j : r.ker →* (normalizer (L : Set G)).subgroupOf (outsideResidual H) :=
    { toFun x := ⟨⟨x.val.val, ⟨inclusion inf_le_left x.val,
        (QuotientGroup.eq_one_iff _).mp x.property, rfl⟩⟩, x.val.property.2⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hj : Function.Injective j := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.val.val) he
  let := residual_intersection_solvable s c
  let := Group.isSolvable_of_isSolvable_injective hj
  let := (isPGroup_quotient_pResidual 2 (G := H)).isNilpotent
  exact Group.isSolvable_of_ker_le_range r.ker.subtype r (by rw [range_subtype])

theorem source_hall_prime_support (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G)))) :
    ∀ p : ℕ, p.Prime → p ∣ Nat.card A → p ∣ 2 ^ S.field.degree - 1 := by
  have ho : Odd (Nat.card A) := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe hA).toEquiv]
    exact OddHall.odd_hall_odd hHall
  exact fun _ _ hp => hp.trans (source_card_dvd s c A hA ho)

theorem source_normalizes_inner_sylow (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree)) :
    H ⊓ L ≤ normalizer (((T : Subgroup G) ⊓ L : Subgroup G) : Set G) := by
  obtain ⟨P,hP⟩ := NormalSylowQuotientAction.intersection_sylow T L
    D.sylow_normalizes_component
  let B := H.subgroupOf L
  let j : B →* (H ⊓ normalizer (L : Set G) : Subgroup G) :=
    { toFun x := ⟨x.val.val, x.property, L.le_normalizer x.val.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  let := source_common_solvable s c
  have hs : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := j) (by intro x y he; apply Subtype.ext; apply Subtype.ext; exact congrArg (fun z : (H ⊓ normalizer (L : Set G) : Subgroup G) => (z : G)) he)
  have hPB : (P : Subgroup L) ≤ B := by
    rw [hP]
    exact comap_mono s.outside.1.1.2
  have hn : B ≤ normalizer (P : Set L) := by
    rcases halt with ⟨F,hfield,hfinite,hcard,⟨e⟩⟩ | ⟨F,hfield,hfinite,hcard,⟨e⟩⟩
    · exact solvable_overgroup_normalizes_of_slThree_twoCore_quotient
        (by have := S.nonbinary; omega) hcard e P B hs hPB
    · exact solvable_overgroup_normalizes_of_spFour_twoCore_quotient
        (by have := S.nonbinary; omega) hcard e P B hs hPB
  have hm := (map_mono hn).trans ((P : Subgroup L).le_normalizer_map L.subtype)
  rw [hP, subgroupOf_map_subtype, subgroupOf_map_subtype] at hm
  simpa only [inf_comm] using hm


theorem source_residual_borel (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) :
    (normalizer (L : Set G)).subgroupOf (outsideResidual H) =
      normalizer (residualSylow s : Set (outsideResidual H)) := by
  apply le_antisymm (residual_intersection_normalizes s c)
  let K := outsideResidual H
  let R := (T : Subgroup G) ⊓ K
  have hR : ((residualSylow s : Subgroup K).map K.subtype) = R := by
    rw [residualSylow_coe, subgroupOf_map_subtype]
  have hRN : (normalizer (residualSylow s : Set K)).map K.subtype ≤
      normalizer (R : Set G) := hR ▸ (residualSylow s : Subgroup K).le_normalizer_map K.subtype
  have hNT : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (T : Subgroup G).le_normalizer
      (s.outside.1.1.2.trans (outsideResidual_normalized H))).trans
      inf_normalizer_le_normalizer_inf
  have hproper : H ⊓ normalizer (R : Set G) < H := by
    apply lt_of_le_of_ne inf_le_left
    intro he
    have hKN : K ≤ normalizer (R : Set G) :=
      (outsideResidual_le H).trans (he ▸ inf_le_right)
    have hfull : normalizer (residualSylow s : Set K) = ⊤ := by
      apply top_unique
      intro k _
      have hk : k ∈ (normalizer (R : Set G)).subgroupOf K := hKN k.property
      rw [subgroupOf_normalizer_eq (show R ≤ K from inf_le_right)] at hk
      have hsub : R.subgroupOf K = (residualSylow s : Subgroup K) := by
        rw [residualSylow_coe]
        exact inf_subgroupOf_right _ _
      rwa [hsub] at hk
    exact Matrix.SpecialLinearGroup.sylow_normalizer_ne_top_of_surjective
      (quotientMap c) (quotientMap_surjective c) (residualSylow s) hfull
  have hYM := Chapter3.HStar.proper_overgroup_le T s.outside
    (le_inf s.outside.1.1.2 hNT) hproper
  intro k hk
  exact hYM ⟨outsideResidual_le H k.property, hRN (mem_map_of_mem K.subtype hk)⟩

theorem source_hall_ne_bot (s : Hypothesis1131At D S U₁ H)
    (c : NaturalQuotientMarking T H S.field) (A : Subgroup G)
    (_hA : A ≤ H ⊓ normalizer (L : Set G))
    (hHall : IsHallSubgroup OddHall.oddPrimes
      (A.subgroupOf (H ⊓ normalizer (L : Set G)))) : A ≠ ⊥ := by
  intro hbot
  have hc := OddHall.sylow_complement_of_hall
    (T.subtype (le_inf s.outside.1.1.2 D.sylow_normalizes_component)) hHall
  have hgen := hc.sup_eq_top
  rw [hbot, bot_subgroupOf, sup_bot_eq] at hgen
  have hpB : IsPGroup 2 (H ⊓ normalizer (L : Set G) : Subgroup G) := by
    have hp := (T.subtype (le_inf s.outside.1.1.2 D.sylow_normalizes_component)).isPGroup'
    rw [hgen] at hp
    exact hp.of_equiv topEquiv
  let K := outsideResidual H
  let P := residualSylow s
  let N := normalizer (P : Set K)
  let j : N →* (H ⊓ normalizer (L : Set G) : Subgroup G) :=
    { toFun x := ⟨x.val.val, outsideResidual_le H x.val.property,
        (source_residual_borel s c).ge x.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hpN : IsPGroup 2 N := hpB.of_injective j (by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : (H ⊓ normalizer (L : Set G) : Subgroup G) => (z : G)) he)
  obtain ⟨f,hf,_⟩ := Matrix.SpecialLinearGroup.exists_sylowNormalizer_diagonal
    (quotientMap c) (quotientMap_surjective c) P
    (by rw [quotientMap_ker]; exact pCore_isPGroup.le_sylow_of_normal _)
  have hpu := hpN.of_surjective f hf
  have ho : Odd (Nat.card S.field.Carrierˣ) := by
    rw [Nat.card_units, S.field.card_eq]
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    have hq : 2 ∣ 2 ^ S.field.degree := dvd_pow_self 2 (by have := S.nonbinary; omega)
    have hpos := Nat.one_le_pow S.field.degree 2 (by decide : 0 < (2 : ℕ))
    omega
  have hu : Nat.card S.field.Carrierˣ = 1 := hpu.card_eq_or_dvd.resolve_right
    (by simpa only [← even_iff_two_dvd] using Nat.not_even_iff_odd.mpr ho)
  rw [Nat.card_units, S.field.card_eq] at hu
  have hl : 4 ≤ 2 ^ S.field.degree :=
    show 2 ^ 2 ≤ 2 ^ S.field.degree from
      Nat.pow_le_pow_right (by decide : 1 ≤ (2:ℕ)) (by have := S.nonbinary; omega)
  omega

/-- The source extraction cannot kill a nontrivial finite group: if its
3-residual vanishes, the group is a 3-group and has nontrivial omega. -/
theorem oddCartanPart_ne_bot (A : Subgroup G) (hne : A ≠ ⊥) :
    oddCartanPart A ≠ ⊥ := by
  intro he
  have hjoin : pResidual 3 A ⊔ (omega₁ (pCore 3 A) (p := 3)).map (pCore 3 A).subtype = ⊥ := by
    apply (map_injective A.subtype_injective)
    simpa only [oddCartanPart, Subgroup.map_bot] using he
  have hr : pResidual 3 A = ⊥ := eq_bot_iff.mpr (le_sup_left.trans hjoin.le)
  have hp : IsPGroup 3 A := (isPGroup_quotient_pResidual 3).of_injective
    (QuotientGroup.mk' (pResidual 3 A)) (by
      apply (MonoidHom.ker_eq_bot_iff _).mp
      simpa only [QuotientGroup.ker_mk'] using hr)
  have hc : pCore 3 A = ⊤ := top_unique (le_sSup ⟨inferInstance,hp.to_subgroup ⊤⟩)
  have hdiv : 3 ∣ Nat.card (pCore 3 A) := by
    rw [hc,card_top]
    exact hp.card_eq_or_dvd.resolve_left (fun h => hne (eq_bot_of_card_eq A h))
  exact omega₁_map_subtype_ne_bot (pCore 3 A) 3 hdiv
    (eq_bot_iff.mpr (le_sup_right.trans hjoin.le))

end
end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.CommonCore.Hall
