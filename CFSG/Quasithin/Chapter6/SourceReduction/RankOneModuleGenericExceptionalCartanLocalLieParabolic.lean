module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalCartanLocalParabolic
public import Theory.SpecificGroups.G2.OddSupplement
public import Theory.SpecificGroups.Triality.OddSupplement
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.G2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.FiveLocalFF.Triality
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.ReeLocal

/-!
# G₂, triality and Ree containing rows in the local Cartan sieve

At a fixed full Sylow, the proper local C-components in these nonbinary
rank-two models are exactly the two root-parabolic residuals. An odd
Sylow-preserving automorphism fixes each. Solvable Sylow control makes the
original Cartan intersection preserve the containing Sylow, so this fixes
every conjugate of the original seed and hence its entire residual orbit.

The actual quotient is C/O₂(C), identified with its image in Y/O₂(Y).
Its two-part forces C to be normal in Y by the nonnormal-container list.
The Ree argument inherits the top C-component from the original C and
uses q = 2^(2m+1), m ≥ 1. It needs no extra simplicity hypothesis.

The fixed-Sylow calculations refine the rank-one cover proofs in Chapter A's
SourceEmbeddings/FiveLocalFF/{G2,Triality} and SourceEmbeddings/ReeLocal.
The combined Chapter 12 consumer retains the original Cartan pair and both
Hall conditions. Unitary, binary endpoint and non-Lie rows and the escaping
inverted cubic remain obligations of the local sieve.

Source: Aschbacher--Smith 5.1.12--13, printed pp.635--638, using A.3.12
and 1.2.1(3), refs/quasithin.pdf. The imported octonion constructions retain
the ATLAS attribution in LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory
open scoped Pointwise MatrixGroups
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem local_perfect {S B : Subgroup G} (hB : B ∈ localCComponents S) :
    Group.IsPerfect B := by
  let := hB.perfect
  exact Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe (show B ≤ B ⊔ S from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe le_sup_left).surjective

omit [Finite G] in
private theorem proper_local_join [IsSimpleGroup G] {S B : Subgroup G}
    (hB : B ∈ localCComponents S) (hb : B ≠ ⊤) : B ⊔ S ≠ ⊤ := by
  intro ht
  have hc : B.IsCComponent := by
    change (B.subgroupOf (B ⊔ S)).IsCComponent at hB
    rw [ht] at hB
    simpa only [map_subgroupOf_eq_of_le le_top] using hB.map_subtype (.top)
  exact (hc.subnormal.eq_bot_or_top_of_isSimpleGroup inferInstance).elim hc.ne_bot hb

private theorem odd_local_fixed_of_standard
    (U : Sylow 2 G) (P Q : Subgroup G)
    (hc : ∀ R : Subgroup G, R ∈ localCComponents U → R ≠ ⊤ → R = P ∨ R = Q)
    (S : Sylow 2 G) (a : MulAut G)
    (ha : Odd (orderOf a)) (hS : (S : Subgroup G).map a.toMonoidHom = S)
    (R : Subgroup G) (hr : R ∈ localCComponents S) : R.map a.toMonoidHom = R := by
  obtain ⟨_,e,_,he⟩ := SolvableSylowControl.exists_aligned_equiv (MulEquiv.refl G) S U
  let : Group.IsSolvable e.toMonoidHom.ker := by
    rw [e.toMonoidHom.ker_eq_bot_iff.mpr e.injective]
    infer_instance
  have hl := Chapter1.Section02.localCComponents_map_of_solvable_ker hr e.toMonoidHom
  rw [he] at hl
  have hmap (B : Subgroup G) : (B.map a.toMonoidHom).map e.toMonoidHom =
      (B.map e.toMonoidHom).map (MulAut.congr e a).toMonoidHom := by
    rw [map_map, map_map]
    congr 1
    ext x
    simp [MulAut.congr_apply]
  have hs : (U : Subgroup G).map (MulAut.congr e a).toMonoidHom = U := by
    rw [←he,←hmap,hS]
  have ho : Odd (orderOf (MulAut.congr e a)) :=
    (orderOf_injective (MulAut.congr e).toMonoidHom (MulAut.congr e).injective _).symm ▸ ha
  have hh := odd_local_fixed_of_two P Q hc (MulAut.congr e a) ho hs _ hl
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [hmap]
  exact hh

section G2
open Atlas.G2 Atlas.G2.LieParabolicSetup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

private theorem g2_standard_locals (hq : 2 < Nat.card F)
    (B : Subgroup (Model F)) (hB : B ∈ localCComponents (sylow (F := F))) (hb : B ≠ ⊤) :
    B = local₁ ∨ B = local₂ := by
  let : IsSimpleGroup (Model F) := Atlas.G2.isSimple hq
  let := local_perfect hB
  have hp := ProperSylowOvergroups.le_parabolic (B ⊔ unipotent)
    le_sup_right (lt_top_iff_ne_top.mpr (proper_local_join hB hb))
  rcases hp with hp | hp
  · left
    let := local₁_isPerfect hq
    apply FiveLocalFF.local_eq_of_sl2_core_quotient local₁ hq
      (local₁CoreQuotientEquivPSL.trans longSLEquivPSL.symm) (sylow (F := F)) B hB
    · rw [← HigherFieldResiduals.parabolic₁_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    · exact unipotent_le_local₁
  · right
    let := local₂_isPerfect hq
    apply FiveLocalFF.local_eq_of_sl2_core_quotient local₂ hq
      (local₂CoreQuotientEquivPSL.trans longSLEquivPSL.symm) (sylow (F := F)) B hB
    · rw [← HigherFieldResiduals.parabolic₂_residual hq]
      exact le_map_solvableResidual_of_isPerfect _ _ (le_sup_left.trans hp)
    · exact unipotent_le_local₂

private theorem g2_odd_local_fixed (hq : 2 < Nat.card F)
    (S : Sylow 2 (Model F)) (a : MulAut (Model F))
    (ha : Odd (orderOf a)) (hS : (S : Subgroup (Model F)).map a.toMonoidHom = S)
    (R : Subgroup (Model F)) (hr : R ∈ localCComponents S) : R.map a.toMonoidHom = R :=
  odd_local_fixed_of_standard (sylow (F := F)) local₁ local₂ (g2_standard_locals hq) S a ha hS R hr
end G2

section Triality
open _root_.Triality.Standard _root_.Triality.Standard.Parabolics

private theorem triality_perfect_le_local (P : Parameters) (hp : P.prime = 2) (a : Node)
    (B : Subgroup (Carrier P)) [Group.IsPerfect B] (hB : B ≤ parabolic P a) :
    B ≤ localFactor P a := by
  let X := B.subgroupOf (parabolic P a)
  let : Group.IsPerfect X := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  let : IsCyclic (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    parabolic_quotient_isCyclic P hp a
  let : CommGroup (parabolic P a ⧸ (localFactor P a).subgroupOf (parabolic P a)) :=
    IsCyclic.commGroup
  have h := le_of_isPerfect_of_solvable_quotient X
    ((localFactor P a).subgroupOf (parabolic P a))
  intro x hx
  exact h (show (⟨x,hB hx⟩ : parabolic P a) ∈ X from hx)

private theorem triality_standard_locals (n : ℕ) (hn : 1 < n)
    (B : Subgroup (BinaryCarrier n (by omega)))
    (hB : B ∈ localCComponents (unipotentSylow (binaryParameters n (by omega)) rfl))
    (hb : B ≠ ⊤) :
    B = localFactor (binaryParameters n (by omega)) .arms ∨
      B = localFactor (binaryParameters n (by omega)) .central := by
  let P := binaryParameters n (by omega)
  let S := unipotentSylow P rfl
  have hq : 2 < P.q := by
    change 2 < 2 ^ n
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) (by omega))
  let := local_perfect hB
  obtain ⟨a,ha⟩ := OddSupplement.le_parabolic n (by omega)
    (B ⊔ (S : Subgroup (BinaryCarrier n (by omega)))) le_sup_right (proper_local_join hB hb)
  have hBK : B ≤ localFactor P a := triality_perfect_le_local P rfl a B (le_sup_left.trans ha)
  have hSK : (S : Subgroup (Carrier P)) ≤ localFactor P a :=
    sylow_le_localFactor P a S (le_sup_right.trans ha)
  let := localFactor_isPerfect P rfl hq a
  cases a with
  | arms =>
    left
    apply FiveLocalFF.local_eq_of_sl2_core_quotient (localFactor P .arms) ?_
      ((localFactorArmsQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (ExtensionField P)).symm) S B hB hBK hSK
    rw [card_extensionField]
    have hpow : 27 ≤ P.q ^ 3 := Nat.pow_le_pow_left (show 3 ≤ P.q by omega) 3
    omega
  | central =>
    right
    apply FiveLocalFF.local_eq_of_sl2_core_quotient (localFactor P .central) ?_
      ((localFactorCentralQuotientEquivPSL2 P rfl).trans
        (Theory.PSL2.sl2QuotientEquiv (GaloisField P.prime P.exponent)).symm) S B hB hBK hSK
    rw [card_baseField]
    exact hq

private theorem triality_odd_local_fixed (n : ℕ) (hn : 1 < n)
    (S : Sylow 2 (BinaryCarrier n (by omega))) (a : MulAut (BinaryCarrier n (by omega)))
    (ha : Odd (orderOf a))
    (hS : (S : Subgroup (BinaryCarrier n (by omega))).map a.toMonoidHom = S)
    (R : Subgroup (BinaryCarrier n (by omega))) (hr : R ∈ localCComponents S) :
    R.map a.toMonoidHom = R :=
  odd_local_fixed_of_standard (unipotentSylow (binaryParameters n (by omega)) rfl)
    (localFactor (binaryParameters n (by omega)) .arms)
    (localFactor (binaryParameters n (by omega)) .central)
    (triality_standard_locals n hn) S a ha hS R hr
end Triality

/-- The full original Cartan intersection normalizes the residual in a
normal nonbinary G₂ containing component. -/
theorem cartan_normalizes_of_g2_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hKC : K ≤ C.map Y.subtype) (hm : 1 < m)
    (he : ClassificationModels.IsG2At (C ⧸ pCore 2 C) (2 ^ m)) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hq : 2 < Nat.card F := by
    rw [hF]
    exact lt_of_lt_of_le (by decide : 2 < 2^2)
      (Nat.pow_le_pow_right (by decide) (by omega))
  apply cartan_normalizes_of_odd_local_model
    (E := Atlas.G2.Model F) ?_ (g2_odd_local_fixed hq)
    h hH hgen c hKH hK horbit hY C hC hCn hKC e
  intro S D hd hs
  exact Atlas.G2.solvable_sylow_overgroup_normalizes hq S D hs hd

/-- Escape excludes every nonbinary G₂ containing quotient. Its two-part
forces relative normality, so no normality or cubic premise is needed. -/
theorem not_g2_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : 1 < m) : ¬ ClassificationModels.IsG2At (C ⧸ pCore 2 C) (2 ^ m) := by
  intro he
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := he
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := m)
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  have hd : 16 ∣ Nat.card (C ⧸ pCore 2 C) := by
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (card_subgroup_dvd_card (Atlas.G2.unipotent (K := F)))
    rw [Atlas.G2.card_unipotent,hF,←pow_mul]
    exact pow_dvd_pow 2 (by omega : 4 ≤ m * 6)
  have hn := container_normal_of_sixteen_dvd h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC hd
  exact hescape (cartan_normalizes_of_g2_container h hH hgen c hKH hK horbit hY C hC hn hKC hm
    ⟨F,inferInstance,inferInstance,hF,⟨e⟩⟩)

/-- The full original Cartan intersection normalizes the residual in a
normal nonbinary genuine triality containing component. -/
theorem cartan_normalizes_of_triality_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hKC : K ≤ C.map Y.subtype) (hm : 1 < m)
    (he : Triality.Standard.IsTrialityGroupAt (2 ^ m) (C ⧸ pCore 2 C)) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
    (C ⧸ pCore 2 C) m (by omega)).mp he
  exact cartan_normalizes_of_odd_local_model
    (Triality.Standard.SolvableSylowControl.binary_control m hm) (triality_odd_local_fixed m hm)
    h hH hgen c hKH hK horbit hY C hC hCn hKC e

/-- Escape excludes every nonbinary genuine triality containing quotient,
retaining the actual seed, full Sylow, and two-core quotient. -/
theorem not_triality_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n m : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype)
    (hm : 1 < m) : ¬ Triality.Standard.IsTrialityGroupAt (2 ^ m) (C ⧸ pCore 2 C) := by
  intro he
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff
    (C ⧸ pCore 2 C) m (by omega)).mp he
  have hd : 16 ∣ Nat.card (C ⧸ pCore 2 C) := by
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (card_subgroup_dvd_card
      (Triality.Standard.Parabolics.unipotent (Triality.Standard.binaryParameters m (by omega))))
    rw [Triality.Standard.Parabolics.card_unipotent_binary _ rfl]
    change 16 ∣ (2 ^ m) ^ 12
    rw [←pow_mul]
    exact pow_dvd_pow 2 (by omega : 4 ≤ m * 12)
  have hn := container_normal_of_sixteen_dvd h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC hd
  exact hescape (cartan_normalizes_of_triality_container h hH hgen c hKH hK horbit hY
    C hC hn hKC hm he)


section Ree
set_option backward.isDefEq.respectTransparency true
open ReeF4 ReeF4.Parabolics ReeF4.LargeLocalSeeds
open BenderSuzuki.MatrixGroups

private theorem ree_perfect_le_local {m : ℕ} (s : Side)
    (B : Subgroup (Model m)) [Group.IsPerfect B] (hB : B ≤ parabolic m s) :
    B ≤ localFactor m s := by
  let P := parabolic m s
  let N := (localFactor m s).subgroupOf P
  let H := (borel m).subgroupOf P
  let : Group.IsSolvable (borel m) := OddSupplement.borel_isSolvable m
  let : Group.IsSolvable H := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (borel_le_parabolic m s)).toMonoidHom)
    (subgroupOfEquivOfLe (borel_le_parabolic m s)).injective
  have hsup : N ⊔ H = ⊤ := by
    apply map_injective P.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le (localFactor_le_parabolic m s),
      map_subgroupOf_eq_of_le (borel_le_parabolic m s),
      ← parabolic_eq_localFactor_sup_borel, ← MonoidHom.range_eq_map, range_subtype]
  let q := QuotientGroup.mk' N
  have hq : Function.Surjective (q.comp H.subtype) := by
    apply MonoidHom.range_eq_top.mp
    rw [MonoidHom.range_comp, range_subtype]
    have hNq : N.map q = ⊥ := (map_eq_bot_iff N).mpr (by rw [QuotientGroup.ker_mk'])
    have hh := congrArg (map q) hsup
    simpa only [Subgroup.map_sup, hNq, bot_sup_eq,
      map_top_of_surjective q (QuotientGroup.mk'_surjective N)] using hh
  let : Group.IsSolvable (P ⧸ N) := Group.isSolvable_of_surjective hq
  let : Group.IsPerfect (B.subgroupOf P) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hB).symm.toMonoidHom) (subgroupOfEquivOfLe hB).symm.surjective
  have hh := le_of_isPerfect_of_solvable_quotient (B.subgroupOf P) N
  intro x hx
  exact hh (show (⟨x,hB hx⟩ : P) ∈ B.subgroupOf P from hx)


private theorem ree_local_solvable_overgroups {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    SolvableSylowOvergroups (localFactor m s) := by
  apply isSolvable_proper_sylow_overgroup_of_twoCore_quotient
  cases s with
  | linear =>
    exact isSolvable_proper_sylow_overgroup_of_equiv
      ((linearLocalQuotientEquiv m).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm)
      Matrix.SpecialLinearGroup.isSolvable_of_proper_sylow_overgroup
  | suzuki =>
    exact isSolvable_proper_sylow_overgroup_of_equiv (suzukiLocalQuotientEquiv m)
      (bender_solvable_proper_sylow_overgroup (.suzuki m hm ⟨MulEquiv.refl _⟩))

private theorem ree_local_top_component {m : ℕ} (hm : 1 ≤ m) (s : Side) :
    (⊤ : Subgroup (localFactor m s)).IsCComponent := by
  let := OuterLocal.localFactor_perfect hm s
  let : IsSimpleGroup (localFactor m s ⧸ pCore 2 (localFactor m s)) := by
    cases s with
    | suzuki =>
      exact (suzukiLocalQuotientEquiv m).isSimpleGroup_congr.mpr
        (BenderSuzuki.External.huppert_blackburn_XI_3_6 m hm).1
    | linear =>
      let e := (linearLocalQuotientEquiv m).trans
        (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := CoefficientField m)).symm
      apply e.isSimpleGroup_congr.mpr
      apply Theory.SpecificGroups.SymplecticFour.NaturalExtension.model_simple
      rw [field_card]
      exact lt_of_lt_of_le (by decide : 2 < 2 ^ 3)
        (Nat.pow_le_pow_right (by decide) (by omega))
  let N := pCore 2 (localFactor m s)
  let : Group.IsNilpotent N := pCore_isNilpotent
  let : Group.IsSolvable N := IsNilpotent.to_isSolvable
  let : IsSimpleGroup (⊤ : Subgroup (localFactor m s ⧸ N)) := topEquiv.isSimpleGroup
  let : Group.IsPerfect (⊤ : Subgroup (localFactor m s ⧸ N)) :=
    Group.IsPerfect.ofSurjective (f := (topEquiv (G := localFactor m s ⧸ N)).symm.toMonoidHom)
      (topEquiv (G := localFactor m s ⧸ N)).symm.surjective
  have ht : (⊤ : Subgroup (localFactor m s ⧸ N)).IsCComponent :=
    isCComponent_of_isSimpleGroup_of_isPerfect .top
  obtain ⟨C,hC,he⟩ := ht.exists_map_quotient_eq N
  have hs : C ⊔ N = ⊤ := by
    simpa only [comap_map_eq,QuotientGroup.ker_mk',comap_top] using
      congrArg (Subgroup.comap (QuotientGroup.mk' N)) he
  let := hC.perfect
  have hc : C = ⊤ := (hC.subnormal.eq_solvableResidual_of_sup_eq_top N hs).trans
    Subgroup.solvableResidual_eq_top
  exact hc ▸ hC

private theorem ree_local_eq_of_le {m : ℕ} (hm : 1 ≤ m) (s : Side)
    (S : Sylow 2 (Model m)) (B : Subgroup (Model m))
    (hB : B ∈ localCComponents S) (hBK : B ≤ localFactor m s)
    (hSK : (S : Subgroup (Model m)) ≤ localFactor m s) : B = localFactor m s := by
  let K := localFactor m s
  let P := B ⊔ (S : Subgroup (Model m))
  have hPK : P ≤ K := sup_le hBK hSK
  have he : P.subgroupOf K = ⊤ := by
    by_contra hn
    let := ree_local_solvable_overgroups hm s (S.subtype hSK) (P.subgroupOf K)
      (fun _ hx => (show (S : Subgroup (Model m)) ≤ P from le_sup_right) hx) hn
    let : Group.IsSolvable P := Group.isSolvable_of_surjective
      (f := (subgroupOfEquivOfLe hPK).toMonoidHom) (subgroupOfEquivOfLe hPK).surjective
    exact hB.not_isSolvable inferInstance
  have heP : P = K := le_antisymm hPK (subgroupOf_eq_top.mp he)
  have hc : (B.subgroupOf K).IsCComponent := by
    change (B.subgroupOf P).IsCComponent at hB
    rwa [heP] at hB
  have hctop : B.subgroupOf K = ⊤ := by
    have hc' : ((B.subgroupOf K).map (topEquiv (G := K)).symm.toMonoidHom).IsCComponent :=
      hc.map_equiv (topEquiv (G := K)).symm
    have hh := (ree_local_top_component hm s).eq_top_of_isCComponent hc'
    apply map_injective (f := (topEquiv (G := K)).symm.toMonoidHom) (topEquiv (G := K)).symm.injective
    simpa only [map_top_of_surjective (topEquiv (G := K)).symm.toMonoidHom (topEquiv (G := K)).symm.surjective] using hh
  exact le_antisymm hBK (subgroupOf_eq_top.mp hctop)


private theorem ree_standard_locals {m : ℕ} (hm : 1 ≤ m)
    (htop : (⊤ : Subgroup (Model m)).IsCComponent)
    (B : Subgroup (Model m))
    (hB : B ∈ localCComponents (ThreeSylowContainment.positiveSylow m)) (hb : B ≠ ⊤) :
    B = localFactor m .linear ∨ B = localFactor m .suzuki := by
  let S := ThreeSylowContainment.positiveSylow m
  have hj : B ⊔ (S : Subgroup (Model m)) ≠ ⊤ := by
    intro he
    change (B.subgroupOf (B ⊔ (S : Subgroup (Model m)))).IsCComponent at hB
    rw [he] at hB
    exact hb (le_antisymm le_top (subgroupOf_eq_top.mp (htop.eq_top_of_isCComponent hB)))
  let := local_perfect hB
  obtain ⟨a,ha⟩ := OddSupplement.le_parabolic m hm
    (B ⊔ (S : Subgroup (Model m))) (by
      rw [show (S : Subgroup (Model m)) = unipotent m from ThreeSylowContainment.positiveSylow_coe m]
      exact le_sup_right) hj
  rw [MaximalSubgroups.AbelianCharacteristic.TwoLocalGeometry.parabolic_eq_rootParabolic] at ha
  have he := ree_local_eq_of_le hm a S B hB
    (ree_perfect_le_local a B (le_sup_left.trans ha)) (by
      rw [show (S : Subgroup (Model m)) = unipotent m from ThreeSylowContainment.positiveSylow_coe m]
      exact unipotent_le_localFactor m a)
  cases a with
  | linear => exact Or.inl he
  | suzuki => exact Or.inr he

private theorem ree_odd_local_fixed {m : ℕ} (hm : 1 ≤ m)
    (htop : (⊤ : Subgroup (Model m)).IsCComponent)
    (S : Sylow 2 (Model m)) (a : MulAut (Model m))
    (ha : Odd (orderOf a)) (hS : (S : Subgroup (Model m)).map a.toMonoidHom = S)
    (R : Subgroup (Model m)) (hr : R ∈ localCComponents S) : R.map a.toMonoidHom = R :=
  odd_local_fixed_of_standard (ThreeSylowContainment.positiveSylow m)
    (localFactor m .linear) (localFactor m .suzuki) (ree_standard_locals hm htop) S a ha hS R hr
end Ree


/-- The original Cartan intersection normalizes the residual for a normal
large Ree containing quotient. The top C-component is inherited from C. -/
theorem cartan_normalizes_of_ree_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hCn : C.Normal)
    (hKC : K ≤ C.map Y.subtype)
    (he : ReeF4.IsReeF4Model (C ⧸ pCore 2 C)) :
    A ⊓ Y ≤ normalizer (residual H : Set G) := by
  obtain ⟨m,hm,⟨e⟩⟩ := he
  have htop : (⊤ : Subgroup (ReeF4.Model m)).IsCComponent := by
    have hh : (⊤ : Subgroup C).IsCComponent := by
      simpa only [subgroupOf_self] using hC.subgroupOf le_rfl
    let := pCore_isNilpotent (p := 2) (G := C)
    have hq : (⊤ : Subgroup (C ⧸ pCore 2 C)).IsCComponent := by
      simpa only [map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] using
        hh.map_quotient (pCore 2 C)
    simpa only [map_top_of_surjective e.toMonoidHom e.surjective] using hq.map_equiv e
  exact cartan_normalizes_of_odd_local_model
    (ReeF4.OddSupplement.solvable_sylow_control m hm) (ree_odd_local_fixed hm htop)
    h hH hgen c hKH hK horbit hY C hC hCn hKC e

/-- The original escape excludes every large Ree quotient in the actual
exceptional-fixed-group convention q = 2^(2m+1), m ≥ 1. -/
theorem not_ree_container
    {T : Sylow 2 G} {L W H A B K Y : Subgroup G} {n : ℕ}
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hgen : 1 < ChapterE.generationParameter H) (c : CartanPair T L H A B)
    (hKH : K ≤ H) (hK : K ∈ Chapter1.L G (T : Subgroup G))
    (horbit : componentOrbit K (T : Subgroup G) = residual H)
    (hY : Y ∈ Chapter1.HOver G (H : Set G))
    (hescape : ¬ A ⊓ Y ≤ normalizer (residual H : Set G))
    (C : Subgroup Y) (hC : C.IsCComponent) (hKC : K ≤ C.map Y.subtype) :
    ¬ ReeF4.IsReeF4Model (C ⧸ pCore 2 C) := by
  intro he
  obtain ⟨m,hm,⟨e⟩⟩ := he
  have hd : 16 ∣ Nat.card (C ⧸ pCore 2 C) := by
    rw [Nat.card_congr e.toEquiv]
    apply dvd_trans _ (card_subgroup_dvd_card (ReeF4.Parabolics.unipotent m))
    rw [ReeF4.Parabolics.card_unipotent,←pow_mul]
    exact pow_dvd_pow 2 (by omega : 4 ≤ (2 * m + 1) * 12)
  have hn := container_normal_of_sixteen_dvd h.qtke hKH hH.1.1.2 hK horbit hY hescape C hC hKC hd
  exact hescape (cartan_normalizes_of_ree_container h hH hgen c hKH hK horbit hY
    C hC hn hKC ⟨m,hm,⟨e⟩⟩)

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LocalSieve

namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric
variable {G : Type*} [Group G] [Finite G]

/-- The original escape selects one actual seed and containing component
with the classical, G₂, genuine triality, and large Ree rows removed simultaneously.
The proper image and the normal full containing orbit use the original maps. -/
theorem localCartan_escape_seed_lie_parabolic_reduction
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
        ¬ ReeF4.IsReeF4Model (C ⧸ pCore 2 C) ∧
        ∀ m : ℕ, 1 < m → ¬ (ClassicalGroup.IsPSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          Chapter1.Section02.LocalModels.IsSL (C ⧸ pCore 2 C) 3 (2 ^ m) ∨
          ClassicalGroup.IsPSp (C ⧸ pCore 2 C) 2 (2 ^ m) ∨
          ClassificationModels.IsG2At (C ⧸ pCore 2 C) (2 ^ m) ∨
          Triality.Standard.IsTrialityGroupAt (2 ^ m) (C ⧸ pCore 2 C)) := by
  obtain ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,hclass⟩ :=
    localCartan_escape_seed_parabolic_reduction h hH hgen c hY hescape
  refine ⟨K,hKH,hK,hqs,hKT,hKL,hR,C,hC,hKC,hlt,hn,
    LocalSieve.seed_image_lt_container h.qtke hKH hH.1.1.2 hKL hR hY hescape C hC hKC,
    LocalSieve.not_ree_container h hH hgen c hKH hKL hR hY hescape C hC hKC,?_⟩
  intro m hm he
  rcases he with he | he | he | he | he
  · exact hclass m hm (Or.inl he)
  · exact hclass m hm (Or.inr (Or.inl he))
  · exact hclass m hm (Or.inr (Or.inr he))
  · exact LocalSieve.not_g2_container h hH hgen c hKH hKL hR hY hescape C hC hKC hm he
  · exact LocalSieve.not_triality_container h hH hgen c hKH hKL hR hY hescape C hC hKC hm he

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric
