module
public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.Centralizers.Pure.Sylows.Four.Swapped.CoreInterval

/-!
# The original module inside the remaining nonabelian containing core

Both O₂(K₀) and O₂(H) lie between O₂(X) and O₂(XT). Mapping through the
original LT action therefore identifies both images with the same marked
parabolic radical A₀. Each image has order sixteen, and its fixed subgroup
on the doubled module also has order sixteen. No action or quotient marking
is replaced by an abstract group-family label.

Sharp elementary replacement puts W inside the original J(T), without an
MS premise. Since H normalizes J(T), W lies in O₂(H); the already proved
noncentral action then rules out an abelian O₂(H). The final consumer
retains the actual swapped component, Fundamental Setup, congruences and
normal closure, and supplies the exact core indices from `CoreInterval`.

The nonabelian containing-core exclusion, ambient point-Sylow theorem,
point-core control and fusion/abelian closure remain with this task. The
explicit original fixed-subgroup premise remains with `qt-rank-two-ms93`
and final owner `qt-d-double-natural-centralizers`. This reduction does
not establish 12.1.4 or pure fusion.
Source: Aschbacher--Smith 12.1.4, printed pp.790--791, B.4.9(2iii),
pp.92,94, and H.9.3(4), p.391.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
open ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {B : DoubledBranch T L V 4}
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]
  (S : B.SourceModel)

include S in
/-- Every subgroup in the original core interval induces precisely the marked radical. -/
theorem four_core_interval_image
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G))
    {R : Subgroup G} (hlo : (PureFourXi.residual T L).pCoreIn 2 ≤ R)
    (hhi : R ≤ (PureFourXi.normalizerJoin T L).pCoreIn 2) :
    (R.subgroupOf (L ⊔ (T : Subgroup G))).map (B.joinActionProjection hTM) =
      A0 S.setup ((T.subtype hTM).mapSurjective B.actionProjection_surjective) := by
  let H := L ⊔ (T : Subgroup G)
  let N := (normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G)).subgroupOf H
  let f := B.joinActionProjection hTM
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  have hN : N.map f = normalizer (A0 S.setup P : Set B.ActionQuotient) :=
    S.four_thompson_normalizer_image hTM hWT hm
  have hnH : PureFourXi.normalizerJoin T L ≤ H := inf_le_right
  have hn : (PureFourXi.normalizerJoin T L).subgroupOf H = N := by
    ext x
    exact and_iff_left x.property
  have hactor : (normalizer (A0 S.setup P : Set B.ActionQuotient)).pCoreIn 2 = A0 S.setup P := by
    let e := permutation S.setup P
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [map_pCoreIn_of_injective 2 _ _ e.injective,S.setup.four_A0_normalizer P]
    have ha : (A0 S.setup P).map e.toMonoidHom =
        BinaryNaturalDual.FourActors.permutationA0 := by
      change (A0 S.setup P).map (BinaryNaturalDual.FourActors.permutationEquiv.toMonoidHom.comp
        (group S.setup P).toMonoidHom) = _
      rw [←map_map,actor_map]
      exact BinaryNaturalDual.FourActors.PermutationCatalogue.actor_map 0
    rw [ha,BinaryNaturalDual.FourActors.PermutationCatalogue.permutationA0_eq_kleinGroup]
    exact Theory.SpecificGroups.SymmetricEight.FourBlockCoreAction.fourStabilizer_pCoreIn
  have hc : (((PureFourXi.normalizerJoin T L).pCoreIn 2).subgroupOf H).map f =
      A0 S.setup P := by
    rw [←pCoreIn_subgroupOf 2 _ H hnH,hn,
      map_pCoreIn_of_ker_isPGroup f (S.four_join_action hTM).2.1,
      hN,hactor]
  apply le_antisymm
  · exact ((map_mono (comap_mono hhi)).trans_eq hc)
  · rw [←S.four_xi_core_image hTM hWT hm]
    exact map_mono (comap_mono hlo)

include S in
/-- The action on the original doubled module has image of order sixteen. -/
theorem four_core_interval_action_index
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G))
    {R : Subgroup G} (hlo : (PureFourXi.residual T L).pCoreIn 2 ≤ R)
    (hhi : R ≤ (PureFourXi.normalizerJoin T L).pCoreIn 2) :
    (centralizer (componentOrbit V (T : Subgroup G) : Set G)).relIndex R = 16 := by
  let H := L ⊔ (T : Subgroup G)
  let f := B.joinActionProjection hTM
  have hRH : R ≤ H := hhi.trans ((pCoreIn_le 2 _).trans inf_le_right)
  have hk : f.ker = (centralizer (componentOrbit V (T : Subgroup G) : Set G)).subgroupOf H := by
    ext x
    change B.actionProjection (inclusion (sup_le L.le_normalizer hTM) x) = 1 ↔ _
    have he : B.actionProjection (inclusion (sup_le L.le_normalizer hTM) x) = 1 ↔
        inclusion (sup_le L.le_normalizer hTM) x ∈ (normalizerAction T L V B.orbit_eq).ker :=
      QuotientGroup.eq_one_iff _
    rw [he,normalizerAction_ker]
    rfl
  rw [←relIndex_subgroupOf hRH,←hk,relIndex_ker,S.four_core_interval_image hTM hWT hm hlo hhi]
  exact actor_card S.setup ((T.subtype hTM).mapSurjective B.actionProjection_surjective) 0

include S in
/-- The same original radical fixes exactly sixteen elements of the doubled module. -/
theorem four_core_interval_fixed_card
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G))
    (hm : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤
      centralizer (componentOrbit V (T : Subgroup G) : Set G))
    {R : Subgroup G} (hlo : (PureFourXi.residual T L).pCoreIn 2 ≤ R)
    (hhi : R ≤ (PureFourXi.normalizerJoin T L).pCoreIn 2) :
    Nat.card (componentOrbit V (T : Subgroup G) ⊓ centralizer (R : Set G) : Subgroup G) = 16 := by
  let W := componentOrbit V (T : Subgroup G)
  let H := L ⊔ (T : Subgroup G)
  let f := B.joinActionProjection hTM
  let P := (T.subtype hTM).mapSurjective B.actionProjection_surjective
  have hRH : R ≤ H := hhi.trans ((pCoreIn_le 2 _).trans inf_le_right)
  have him := S.four_core_interval_image hTM hWT hm hlo hhi
  have hfix (w : W) : Additive.ofMul w ∈ S.setup.fixed (A0 S.setup P) ↔
      (w : G) ∈ centralizer (R : Set G) := by
    rw [←him]
    constructor
    · intro hw r hr
      have hh := hw ⟨f ⟨r,hRH hr⟩,mem_map_of_mem f hr⟩
      rw [S.representation_eq] at hh
      have he := congrArg (fun z : Additive W => (z.toMul : G)) hh
      change (B.quotientAction (B.actionProjection
        (inclusion (sup_le L.le_normalizer hTM) ⟨r,hRH hr⟩)) w : G) = w at he
      rw [B.quotientAction_projection_apply] at he
      exact mul_inv_eq_iff_eq_mul.mp he
    · intro hw a
      obtain ⟨r,hr,he⟩ := a.property
      change S.setup.representation a.val (Additive.ofMul w) = Additive.ofMul w
      rw [←he,S.representation_eq]
      apply Additive.toMul.injective
      apply Subtype.ext
      change (B.quotientAction (B.actionProjection
        (inclusion (sup_le L.le_normalizer hTM) r)) w : G) = w
      rw [B.quotientAction_projection_apply]
      exact mul_inv_eq_of_eq_mul (hw r hr)
  let e : (W ⊓ centralizer (R : Set G) : Subgroup G) ≃
      S.setup.fixed (A0 S.setup P) := {
    toFun := fun w => ⟨Additive.ofMul ⟨w,w.property.1⟩,(hfix _).mpr w.property.2⟩
    invFun := fun w => ⟨w.val.toMul, w.val.toMul.property,(hfix _).mp w.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Module.natCard_eq_pow_finrank (K := ZMod 2),
    (A0_parameters S.setup P).1,Nat.card_zmod]
  norm_num

include S in
/-- Sharp elementary replacement puts the original doubled module in J(T). -/
theorem four_orbit_le_thompson
    (hTM : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hWT : componentOrbit V (T : Subgroup G) ≤ (T : Subgroup G)) :
    componentOrbit V (T : Subgroup G) ≤ elementaryAbelianMaxJ (T : Subgroup G) := by
  let W := componentOrbit V (T : Subgroup G)
  obtain ⟨A,hA⟩ := elementaryAbelianMaxSubgroups_nonempty (T : Subgroup G)
  by_cases hn : A ≤ centralizer (W : Set G)
  · exact (maxElementary_contains_elementary_centralizer _ A W hA hWT
      (le_centralizer_iff.mp hn)).trans (le_sSup hA)
  let C := A ⊓ centralizer (W : Set G)
  let : IsElementaryAbelian 2 A := hA.2.1
  let : IsElementaryAbelian 2 C := IsElementaryAbelian.of_le (show C ≤ A from inf_le_left)
  let : IsElementaryAbelian 2 (W ⊓ centralizer (A : Set G) : Subgroup G) :=
    IsElementaryAbelian.of_le inf_le_left
  have hCW : W ⊓ centralizer (A : Set G) = W ⊓ A := by
    apply le_antisymm
      (le_inf inf_le_left (maxElementary_contains_elementary_centralizer _ A _ hA
        (inf_le_left.trans hWT) inf_le_right))
    exact le_inf inf_le_left (inf_le_right.trans (le_centralizer A))
  have hWC : W ⊓ C = W ⊓ A := by
    apply le_antisymm (le_inf inf_le_left (inf_le_right.trans inf_le_left))
    exact le_inf inf_le_left (le_inf inf_le_right (inf_le_left.trans (le_centralizer W)))
  have hcard := S.four_maxElementary_card_eq hTM hWT A hA hn
  change Nat.card W = Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) *
    (centralizer (W : Set G)).relIndex A at hcard
  rw [hCW] at hcard
  have hCA : Nat.card C * (centralizer (W : Set G)).relIndex A = Nat.card A := by
    have hh := relIndex_mul_relIndex (⊥ : Subgroup G) (centralizer (W : Set G) ⊓ A) A
      bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right] at hh
    simpa only [inf_comm,C] using hh
  have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes W C
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
  rw [hWC,hcard] at hprod
  have hBcard : Nat.card (W ⊔ C : Subgroup G) = Nat.card A := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := (W ⊓ A : Subgroup G)))
    calc
      Nat.card (W ⊓ A : Subgroup G) * Nat.card (W ⊔ C : Subgroup G) =
          (Nat.card (W ⊓ A : Subgroup G) *
            (centralizer (W : Set G)).relIndex A) * Nat.card C := hprod.symm
      _ = Nat.card (W ⊓ A : Subgroup G) *
          (Nat.card C * (centralizer (W : Set G)).relIndex A) := by ac_rfl
      _ = Nat.card (W ⊓ A : Subgroup G) * Nat.card A := by rw [hCA]
  have hBT : W ⊔ C ≤ (T : Subgroup G) :=
    sup_le hWT (inf_le_left.trans hA.1)
  have hBe : IsElementaryAbelian 2 (W ⊔ C : Subgroup G) :=
    IsElementaryAbelian.sup_of_le_centralizer inf_le_right
  have hB : W ⊔ C ∈ elementaryAbelianMaxSubgroups (T : Subgroup G) :=
    ⟨hBT,hBe,fun D hDT hDe => hBcard.symm ▸ hA.2.2 D hDT hDe⟩
  exact le_sup_left.trans (le_sSup hB)
end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch.SourceModel
namespace CFSG.Quasithin.Chapter12.Section02.ChosenModule
open Chapter12.Section01.DoubleNaturalSource Chapter1 Chapter1.XiEmbedding
open ChapterH.NaturalDual.SourceFourActors
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The actual remaining obstruction has exact core indices and the same original radical action. -/
theorem doubleNatural_four_pure_core_interval_of_many_of_omega_fixed
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L) (D : ChosenModule T L V)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (B : DoubledBranch T L V 4) :
    letI := D.doubledOrbit_elementary h
    ∀ S : B.SourceModel, ∀ w : componentOrbit V (T : Subgroup G), w ≠ 1 →
      ∀ hp : (B.coordinates w).toAdd.2 = 0,
      (⟨Additive.ofMul w,(S.natural_marking w).mpr hp⟩ : S.setup.natural) ∈
        S.setup.naturalFixed (S.setup.naturalSylowNormalizer
          ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective)) →
      ¬ IsSylowIn 2 (B.pointSylow w) (B.pointCentralizer w) →
      omegaCenterIn (B.pointSylow w) ⊓ centralizer (L : Set G) ≠ ⊥ →
      let X := PureFourXi.residual T L
      ∃ P : Sylow 2 G, B.pointSylow w < (P : Subgroup G) ∧
        (P : Subgroup G) ≤ B.pointCentralizer w ∧
        (P : Subgroup G) ⊓ normalizer (L : Set G) = B.pointSylow w ∧
        (P : Subgroup G) ≤ normalizer (B.pointSylow w : Set G) ∧
        (B.pointSylow w).relIndex (T : Subgroup G) = 2 ∧
        let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
        H ∈ HOver G ((X ⊔ (T : Subgroup G) : Subgroup G) : Set G) ∧
        H ≤ normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ∧
        ¬ H ≤ normalizer (L : Set G) ∧
        ∃ A : Sylow 3 X, ∃ K : Subgroup G,
          SwappedSylowInput KnownSimple.IsKnownSimple 3 (T : Subgroup G) X
            ((A : Subgroup X).map X.subtype) H K ∧
          conjugateSpanBy X H = componentOrbit K (T : Subgroup G) ∧
          X < componentOrbit K (T : Subgroup G) ∧
          (∃ p : ℕ, p.Prime ∧ Odd p ∧ ClassicalGroup.IsPSL (XiQuotient K) 2 p ∧
            (p % 8 = 3 ∨ p % 8 = 5) ∧ (p % 24 = 11 ∨ p % 24 = 13)) ∧
          quotientImage (componentOrbit K (T : Subgroup G)) (B.pointSylow w) =
            quotientImage (componentOrbit K (T : Subgroup G)) (T : Subgroup G) ∧
          X.pCoreIn 2 ≤ (componentOrbit K (T : Subgroup G)).pCoreIn 2 ∧
          (¬ (componentOrbit K (T : Subgroup G)).pCoreIn 2 ≤
            centralizer (componentOrbit V (T : Subgroup G) : Set G)) ∧
          (¬ H.pCoreIn 2 ≤ centralizer (componentOrbit V (T : Subgroup G) : Set G)) ∧
          ⁅(componentOrbit K (T : Subgroup G)).pCoreIn 2,
            ((A : Subgroup X).map X.subtype)⁆ = X.pCoreIn 2 ∧
          ¬ ClassicalGroup.IsPSL (XiQuotient K) 2 4 ∧
          K ∈ Chapter1.LStar G (T : Subgroup G) ∧
          K ∈ MainForward.faithfulLocalComponents T ∧
          Nonempty (Chapter3.Section02.FundamentalSetup KnownSimple.IsKnownSimple T K) ∧
          let Y := componentOrbit K (T : Subgroup G)
          let R := (X ⊔ ((T : Subgroup G) ⊓ Y)).pCoreIn 2
          Y.pCoreIn 2 ≤ R ∧ R ≤ (T : Subgroup G) ⊓ Y ∧
          (Y.pCoreIn 2).relIndex R = 4 ∧ R.relIndex ((T : Subgroup G) ⊓ Y) = 4 ∧
          ((Y.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map
            (B.joinActionProjection D.sylow_normalizes_component) =
            A0 S.setup ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective) ∧
          ((H.pCoreIn 2).subgroupOf (L ⊔ (T : Subgroup G))).map
            (B.joinActionProjection D.sylow_normalizes_component) =
            A0 S.setup ((T.subtype D.sylow_normalizes_component).mapSurjective B.actionProjection_surjective) ∧
          (centralizer (componentOrbit V (T : Subgroup G) : Set G)).relIndex (Y.pCoreIn 2) = 16 ∧
          (centralizer (componentOrbit V (T : Subgroup G) : Set G)).relIndex (H.pCoreIn 2) = 16 ∧
          Nat.card (componentOrbit V (T : Subgroup G) ⊓ centralizer (Y.pCoreIn 2 : Set G) : Subgroup G) = 16 ∧
          Nat.card (componentOrbit V (T : Subgroup G) ⊓ centralizer (H.pCoreIn 2 : Set G) : Subgroup G) = 16 ∧
          componentOrbit V (T : Subgroup G) ≤ H.pCoreIn 2 ∧
          ¬ IsMulCommutative (H.pCoreIn 2) := by
  let := D.doubledOrbit_elementary h
  intro S w hw hp hfix hf hne
  obtain ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,hodd,hfull,hcore,
      hmoveY,hmoveH,hcomm,hA5,hmax,hfaith,hFS⟩ :=
    D.doubleNatural_four_pure_noncentral_swapped_of_many_of_omega_fixed
      h hmany B S w hw hp hfix hf hne
  let X := PureFourXi.residual T L
  let H := (P : Subgroup G) ⊔ (X ⊔ (T : Subgroup G))
  let Y := componentOrbit K (T : Subgroup G)
  obtain ⟨p,hp',ho,hm,hmod,h24⟩ := hodd
  have hc := PureFourXi.collapsed_parabolic_core_relIndex T hs hp' ho hm hmod hcore
  have hb := PureFourXi.swapped_containing_core_bounds T hs
  have hXT := (D.doubleNatural_four_pure_xi_of_many h hmany B S w hw hp hfix hf).2.1
  have hhiH : H.pCoreIn 2 ≤ (PureFourXi.normalizerJoin T L).pCoreIn 2 := hXT ▸ hb.2
  have hhiY := hb.1.trans hhiH
  have hloH := hcore.trans hb.1
  have hWT := (D.doubledOrbit_E322 h).le_sylow
  have hmove := (D.doubleNatural_four_pure_thompson_moves_of_many h hmany B S w hw hp hfix hf).2
  have hJT : elementaryAbelianMaxJ (T : Subgroup G) ≤ (T : Subgroup G) :=
    sSup_le fun _ hA => hA.1
  have hJH : elementaryAbelianMaxJ (T : Subgroup G) ≤ H.pCoreIn 2 :=
    le_pCoreIn_of_normalizes (T.isPGroup'.to_le hJT)
      (hJT.trans (le_sup_right.trans le_sup_right)) hHN
  have hWH := (S.four_orbit_le_thompson D.sylow_normalizes_component hWT).trans hJH
  have hnonabelian : ¬ IsMulCommutative (H.pCoreIn 2) := by
    intro hh
    let := hh
    exact hmoveH ((le_centralizer (H.pCoreIn 2)).trans (centralizer_le hWH))
  exact ⟨P,hlt,hPC,hPM,hPN,hiT,hH,hHN,hout,A,K,hs,he,hstrict,
    ⟨p,hp',ho,hm,hmod,h24⟩,hfull,hcore,hmoveY,hmoveH,hcomm,hA5,hmax,hfaith,hFS,
    hc.1,hc.2.1,hc.2.2.1,hc.2.2.2,
    S.four_core_interval_image D.sylow_normalizes_component hWT hmove hcore hhiY,
    S.four_core_interval_image D.sylow_normalizes_component hWT hmove hloH hhiH,
    S.four_core_interval_action_index D.sylow_normalizes_component hWT hmove hcore hhiY,
    S.four_core_interval_action_index D.sylow_normalizes_component hWT hmove hloH hhiH,
    S.four_core_interval_fixed_card D.sylow_normalizes_component hWT hmove hcore hhiY,
    S.four_core_interval_fixed_card D.sylow_normalizes_component hWT hmove hloH hhiH,hWH,hnonabelian⟩
end CFSG.Quasithin.Chapter12.Section02.ChosenModule
