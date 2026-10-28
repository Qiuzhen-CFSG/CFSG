module

public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.RankOne.ActionReduction
public import CFSG.Quasithin.ChapterE.Section06.CentralizerStructure.Components.LieSieve.LinearThree.MarkedAction
public import Theory.SpecificGroups.Suzuki.RootCenter
public import Theory.GroupAction.AutomorphismFixedTransport
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity.BaseAutomorphisms.Suzuki
public import BenderSuzuki.ZD.Recognition.MinimalReduction.Radical.CentralLifting.Rigidity
public import Theory.GroupTheory.AutomorphismTowerSimple

/-!
# The Suzuki action in E.6.8(1)

This file is the concrete model calculation used by the rank-one assembly.
The Sylow normalizer is handled by `ActionReduction`; here the Suzuki root
group and its split-torus complement are transported to the marked Sylow.

Source: Aschbacher--Smith, combined manuscript (1 March 2004), E.6.8(1),
printed pp.247--248.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open BenderSuzuki.MatrixGroups
open CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree
open CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.LinearThree.MarkedAction

namespace CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne

variable {G : Type*} [Group G] [Finite G]
variable {K : GroupClass} {T : Sylow 2 G} {M V U L : Subgroup G}

private theorem suzuki_aligned_equiv {m : ℕ} (hm : 0 < m)
    (e : L ≃* SuzukiMatrixGroup m) (S : Sylow 2 L) :
    ∃ f : SuzukiMatrixGroup m ≃* L,
      (SuzukiRootSubgroup m).map f.toMonoidHom = (S : Subgroup L) := by
  obtain ⟨P, hP⟩ := suzukiRootSubgroup_isSylow m hm
  let P' : Sylow 2 L := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L P' S
  refine ⟨e.symm.trans (MulAut.conj g), ?_⟩
  have hh := congrArg Sylow.toSubgroup hg
  change ((P : Subgroup (SuzukiMatrixGroup m)).map e.symm.toMonoidHom).map
    (MulAut.conj g).toMonoidHom = (S : Subgroup L) at hh
  change (SuzukiRootSubgroup m).map
    ((MulAut.conj g).toMonoidHom.comp e.symm.toMonoidHom) = _
  simpa only [hP, map_map] using hh

private theorem suzuki_fixing_sylow_inner {m : ℕ} (hm : 1 ≤ m)
    (e : L ≃* SuzukiMatrixGroup m) (S : Sylow 2 L) (a : MulAut L)
    (hfix : ∀ s ∈ S, a s = s) :
    ∃ z ∈ (center S).map (S : Subgroup L).subtype, a = MulAut.conj z := by
  obtain ⟨f, hf⟩ := suzuki_aligned_equiv (m := m) (by omega) e S
  let β : MulAut (SuzukiMatrixGroup m) := (MulAut.congr f).symm a
  have hβ : ∀ x ∈ SuzukiRootSubgroup m, β x = x := by
    intro x hx
    have hfx : f x ∈ (S : Subgroup L) := by
      rw [← hf]
      exact mem_map_of_mem f.toMonoidHom hx
    have ha := congrArg (fun q : MulAut L => q (f x))
      (show MulAut.congr f β = a from (MulAut.congr f).apply_symm_apply a)
    apply f.injective
    have ha' : f (β x) = a (f x) := by
      change (f.symm.trans (β.trans f)) (f x) = a (f x) at ha
      simp only [MulEquiv.trans_apply, f.symm_apply_apply] at ha
      exact ha
    rw [hfix (f x) hfx] at ha'
    exact ha'
  obtain ⟨b, hb, hβb⟩ :=
    BenderSuzuki.ZD.BaseAutomorphisms.suzuki_aut_fixing_root_inner m hm β hβ
  let bR : SuzukiRootSubgroup m := ⟨b, hb⟩
  have hbcenter : bR ∈ center (SuzukiRootSubgroup m) := by
    apply mem_center_iff.mpr
    intro y
    have hy' := hβ (y : SuzukiMatrixGroup m) y.property
    rw [hβb] at hy'
    apply Subtype.ext
    exact (mul_inv_eq_iff_eq_mul.mp hy').symm
  let eR : SuzukiRootSubgroup m ≃* S :=
    ((SuzukiRootSubgroup m).equivMapOfInjective f.toMonoidHom f.injective).trans
      (MulEquiv.subgroupCongr hf)
  let z : S := eR bR
  have hz : z ∈ center S := (centerCongr eR ⟨bR, hbcenter⟩).property
  let zc : center S := ⟨z, hz⟩
  have hz' : (z : L) = f b := by
    rfl
  refine ⟨(z : L), ⟨zc, zc.property, rfl⟩, ?_⟩
  have ha : a = MulAut.congr f β := (MulAut.congr f).apply_symm_apply a |>.symm
  rw [ha, hβb, MulAut.congr_conj]
  exact congrArg MulAut.conj hz'

private theorem suzuki_center_transitive {m : ℕ} (hm : 1 ≤ m)
    (e : L ≃* SuzukiMatrixGroup m) (S : Sylow 2 L) :
    ∀ z ∈ (center S).map (S : Subgroup L).subtype, z ≠ 1 →
      ∀ w ∈ (center S).map (S : Subgroup L).subtype, w ≠ 1 →
        ∃ b ∈ normalizer (S : Set L), b * z * b⁻¹ = w := by
  obtain ⟨hcard, hcent, D, ⟨eD⟩, hsup, hdis⟩ :=
    suzukiSylow_borel_structure (Nat.succ_le_iff.mp hm) e S
  let Z₀ := {z : center S // (z : L) ≠ 1}
  have hZcard : Nat.card Z₀ = 2 ^ (2 * m + 1) - 1 := by
    let _ := Fintype.ofFinite (center S)
    let _ := Fintype.ofFinite Z₀
    let _ := Fintype.ofFinite {z : center S // (z : L) = 1}
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    have hc : Fintype.card (center S) = 2 ^ (2 * m + 1) := by
      simpa only [Nat.card_eq_fintype_card] using hcard
    rw [hc]
    simp
  have hDcard : Nat.card D = 2 ^ (2 * m + 1) - 1 := by
    rw [Nat.card_congr eD.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  intro z hz hzne w hw hwne
  obtain ⟨zs, hzs, rfl⟩ := hz
  obtain ⟨ws, hws, rfl⟩ := hw
  let φ : D → Z₀ := fun d => by
    let hdN : (d : L) ∈ normalizer (S : Set L) := by
      rw [← hsup]
      exact mem_sup_right d.property
    let hxS : (d : L) * (zs : L) * (d : L)⁻¹ ∈ (S : Subgroup L) := by
      exact (mem_normalizer_iff.mp hdN (zs : L)).mp zs.property
    let hxC : (⟨(d : L) * (zs : L) * (d : L)⁻¹, hxS⟩ : S) ∈ center S := by
      apply mem_center_iff.mpr
      intro y
      have hdinv : (d : L)⁻¹ ∈ normalizer (S : Set L) :=
        (normalizer (S : Set L)).inv_mem hdN
      have hy0 := (mem_normalizer_iff.mp hdinv (y : L)).mp y.property
      have hy : (d : L)⁻¹ * (y : L) * (d : L) ∈ (S : Subgroup L) := by
        simpa only [inv_inv] using hy0
      apply Subtype.ext
      apply Subtype.ext
      change (y : G) * ((d : G) * (zs : G) * (d : G)⁻¹) =
        ((d : G) * (zs : G) * (d : G)⁻¹) * (y : G)
      have hzy : ((d : G)⁻¹ * (y : G) * (d : G)) * (zs : G) =
          (zs : G) * ((d : G)⁻¹ * (y : G) * (d : G)) :=
        congrArg (fun q : S => (q : G)) ((mem_center_iff.mp hzs)
          (⟨(d : L)⁻¹ * (y : L) * (d : L), hy⟩ : S)
        )
      calc
        (y : G) * ((d : G) * (zs : G) * (d : G)⁻¹) =
            (d : G) * (((d : G)⁻¹ * (y : G) * (d : G)) * (zs : G)) * (d : G)⁻¹ := by group
        _ = (d : G) * ((zs : G) * ((d : G)⁻¹ * (y : G) * (d : G))) * (d : G)⁻¹ := by rw [hzy]
        _ = ((d : G) * (zs : G) * (d : G)⁻¹) * (y : G) := by group
    have hxne : (⟨(d : L) * (zs : L) * (d : L)⁻¹, hxS⟩ : S) ≠ 1 := by
      intro hh
      apply hzne
      have hh' : (d : L) * (zs : L) * (d : L)⁻¹ = (↑(1 : S) : L) := by
        have hhS : (⟨(d : L) * (zs : L) * (d : L)⁻¹, hxS⟩ : S) = 1 := hh
        exact congrArg (fun q : S => (q : L)) hhS
      have := congrArg (fun x : L => (d : L)⁻¹ * x * (d : L)) hh'
      calc
        (zs : L) = (d : L)⁻¹ * ((d : L) * (zs : L) * (d : L)⁻¹) * (d : L) := by group
        _ = (d : L)⁻¹ * (↑(1 : S) : L) * (d : L) := by rw [hh']
        _ = 1 := by simp
    exact ⟨⟨⟨(d : L) * (zs : L) * (d : L)⁻¹, hxS⟩, hxC⟩,
      fun hh => by
        have hhS : (⟨(d : L) * (zs : L) * (d : L)⁻¹, hxS⟩ : S) = (1 : S) := by
          apply Subtype.ext
          exact hh
        exact hxne hhS⟩
  have hφinj : Function.Injective φ := by
    intro d₁ d₂ hh
    have heq : (d₁ : L) * (zs : L) * (d₁ : L)⁻¹ =
        (d₂ : L) * (zs : L) * (d₂ : L)⁻¹ := by
      exact congrArg (fun x : Z₀ => (x.1.1 : L)) hh
    let r : L := (d₂ : L)⁻¹ * (d₁ : L)
    have hrconj : r * (zs : L) * r⁻¹ = (zs : L) := by
      dsimp [r]
      calc
        (d₂ : L)⁻¹ * (d₁ : L) * (zs : L) * ((d₂ : L)⁻¹ * (d₁ : L))⁻¹ =
            (d₂ : L)⁻¹ * ((d₁ : L) * (zs : L) * (d₁ : L)⁻¹) * (d₂ : L) := by group
        _ = (d₂ : L)⁻¹ * ((d₂ : L) * (zs : L) * (d₂ : L)⁻¹) * (d₂ : L) := by rw [heq]
        _ = (zs : L) := by group
    have hrc : r ∈ centralizer ({(zs : L)} : Set L) := by
      apply mem_centralizer_singleton_iff.mpr
      exact mul_inv_eq_iff_eq_mul.mp hrconj
    have hrS : r ∈ (S : Subgroup L) :=
      hcent (zs : L) zs.property hzne hrc
    have hrD : r ∈ D := D.mul_mem (D.inv_mem d₂.property) d₁.property
    have hrbot : r = 1 := by
      apply mem_bot.mp
      rw [← hdis]
      exact ⟨hrS, hrD⟩
    apply Subtype.ext
    dsimp [r] at hrbot
    exact (eq_of_inv_mul_eq_one hrbot).symm
  have hφcard : Nat.card D = Nat.card Z₀ := hDcard.trans hZcard.symm
  let _ := Fintype.ofFinite D
  let _ := Fintype.ofFinite Z₀
  have hφbij : Function.Bijective φ := by
    apply (Fintype.bijective_iff_injective_and_card φ).mpr
    exact ⟨hφinj, by simpa only [Nat.card_eq_fintype_card] using hφcard⟩
  obtain ⟨d, hd⟩ := hφbij.2 ⟨⟨ws, hws⟩, hwne⟩
  refine ⟨d, ?_, ?_⟩
  · rw [← hsup]
    exact mem_sup_right d.property
  · simpa [φ] using congrArg (fun x : Z₀ => (x.1.1 : L)) hd

/-- The Suzuki model supplies the three actual action calculations needed by
the rank-one reduction. -/
theorem suzuki_action_calculation
    (h : HypothesisE61 K T M V) (earlier : EarlierLocalFacts T)
    (hU : U ∈ obstructionFamily M V)
    (hL : ComponentIn (centralizer (U : Set G)) L)
    {m : ℕ} (hm : 1 ≤ m) (e : L ≃* SuzukiMatrixGroup m)
    (S : Sylow 2 L)
    (hS : (S : Subgroup L).map L.subtype =
      L ⊓ sylowCentralizer (T : Subgroup G) V)
    (hB : sylowBorel S = L ⊓ M) :
    ActionCalculation M V L (2 * m + 1) := by
  let A := (S : Subgroup L).map L.subtype
  let B := L ⊓ M
  have hplace : L ⊓ M = markedBorel L S := by
    simpa only [markedBorel, sylowBorel] using hB.symm
  have hfixer : ∀ a : MulAut L, (∀ s ∈ S, a s = s) →
      ∃ z ∈ (center S).map (S : Subgroup L).subtype,
        a = MulAut.conj z := by
    intro a ha
    exact suzuki_fixing_sylow_inner hm e S a ha
  have htrans := suzuki_center_transitive hm e S
  have hrange := componentAction_range_eq_inner_center h earlier hU hL S hS
    hplace hfixer htrans
  have hC : L ⊓ centralizer (V : Set G) = A := by
    apply le_antisymm
    · rintro c ⟨hcL, hcV⟩
      obtain ⟨⟨a, ha⟩, hane⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp
          (componentAction_range_ne_bot h earlier hU hL)
      obtain ⟨v, hv_eq⟩ := ha
      have ha' : a ∈ ((center S).map (S : Subgroup L).subtype).map MulAut.conj :=
        hrange ▸ ⟨v, hv_eq⟩
      obtain ⟨z, hz, haz⟩ := ha'
      have hzne : z ≠ 1 := by
        intro hz1
        have hconj : MulAut.conj z = 1 := by
          rw [hz1]
          exact map_one MulAut.conj
        apply hane
        apply Subtype.ext
        exact haz.symm.trans hconj
      have hac : componentAction h hU hL v (⟨c, hcL⟩ : L) = ⟨c, hcL⟩ := by
        apply Subtype.ext
        change (v : G) * c * (v : G)⁻¹ = c
        have hc := mem_centralizer_iff.mp hcV v v.property
        simp [hc]
      obtain ⟨zs, hzs, rfl⟩ := hz
      have hcz : (⟨c, hcL⟩ : L) ∈ centralizer ({(zs : L)} : Set L) := by
        apply mem_centralizer_singleton_iff.mpr
        apply Subtype.ext
        have hconj_c : MulAut.conj (zs : L) (⟨c, hcL⟩ : L) = ⟨c, hcL⟩ := by
          change MulAut.conj ((S : Subgroup L).subtype zs) (⟨c, hcL⟩ : L) =
            ⟨c, hcL⟩
          rw [haz, ← hv_eq]
          exact hac
        have hzc := congrArg Subtype.val hconj_c
        exact (mul_inv_eq_iff_eq_mul.mp hzc).symm
      have hcS : (⟨c, hcL⟩ : L) ∈ (S : Subgroup L) :=
        (suzukiSylow_borel_structure (Nat.succ_le_iff.mp hm) e S).2.1 (zs : L)
          zs.property hzne hcz
      exact mem_map_of_mem L.subtype hcS
    · change (S : Subgroup L).map L.subtype ≤ L ⊓ centralizer (V : Set G)
      rw [hS]
      exact inf_le_inf_left L (show sylowCentralizer (T : Subgroup G) V ≤
        centralizer (V : Set G) from inf_le_right)
  obtain ⟨hcard, hcent, D, ⟨eD⟩, hsup, hdis⟩ :=
    suzukiSylow_borel_structure (Nat.succ_le_iff.mp hm) e S
  have hDne : D ≠ ⊥ := by
    intro hD
    have hq : 2 < 2 ^ (2 * m + 1) := by
      calc
        2 < 8 := by decide
        _ = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (2 * m + 1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hDcard : Nat.card D = 2 ^ (2 * m + 1) - 1 := by
      rw [Nat.card_congr eD.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hc := hDcard
    rw [hD, Subgroup.card_bot] at hc
    omega
  have hfixed : V ⊓ centralizer ((L ⊓ M : Subgroup G) : Set G) =
      V ⊓ centralizer (L : Set G) := by
    apply le_antisymm
    · rintro v ⟨hvV, hvB⟩
      let v' : V := ⟨v, hvV⟩
      let ha : MulAut L := componentAction h hU hL v'
      obtain ⟨z, hz, haz⟩ := hfixer ha (by
        intro s hs
        exact componentAction_fixes_marked_sylow h hU hL S hS v' s hs)
      have hz1 : z = 1 := by
        by_contra hzne
        have hDS : D ≤ (S : Subgroup L) := by
          intro d hd
          have hdN : (d : L) ∈ normalizer (S : Set L) := by
            rw [← hsup]
            exact mem_sup_right hd
          have hdB : (d : G) ∈ L ⊓ M := by
            rw [← hB]
            exact mem_map_of_mem L.subtype hdN
          have had0 : componentAction h hU hL v' (d : L) = d := by
            apply Subtype.ext
            change (v' : G) * (d : G) * (v' : G)⁻¹ = (d : G)
            have hc := mem_centralizer_iff.mp hvB (d : G) hdB
            calc
              (v' : G) * (d : G) * (v' : G)⁻¹ =
                  (d : G) * (v' : G) * (v' : G)⁻¹ := by rw [hc.symm]
              _ = (d : G) := mul_inv_cancel_right _ _
          have had : ha (d : L) = d := by simpa [ha] using had0
          have hzd : (d : L) ∈ centralizer ({z} : Set L) := by
            apply mem_centralizer_singleton_iff.mpr
            apply Subtype.ext
            have had' := congrArg Subtype.val had
            rw [haz] at had'
            exact (mul_inv_eq_iff_eq_mul.mp had').symm
          exact hcent z (map_subtype_le (center S) hz) hzne hzd
        have hDbot : D ≤ ⊥ := fun d hd => by
          rw [← hdis]
          exact ⟨hDS hd, hd⟩
        exact hDne (le_bot_iff.mp hDbot)
      have haker : ha = 1 := by
        rw [haz, hz1]
        simp
      have hvker : v' ∈ (componentAction h hU hL).ker := by
        rw [MonoidHom.mem_ker]
        exact haker
      have hvCL : (v : G) ∈ centralizer (L : Set G) := by
        have := componentAction_ker h hU hL ▸ hvker
        exact this
      exact ⟨hvV, hvCL⟩
    · exact inf_le_inf_left V (centralizer_le inf_le_left)
  let model : Model L (2 * m + 1) := .suzuki m hm rfl ⟨e⟩
  have hd := intersection_decomposition h hU hL model S hS hB
  rw [hfixed] at hd
  let C := V ⊓ centralizer (L : Set G)
  let W := ⁅V, L ⊓ M⁆
  have hnorm : W ≤ normalizer (C : Set G) := by
    exact (commutator_eq_bot_iff_le_centralizer.mp hd.2.2).trans
      (Subgroup.centralizer_le_normalizer _)
  have hdisW : Disjoint C W :=
    disjoint_iff.mpr (inf_comm W C ▸ hd.2.1)
  have hcardV : Nat.card V = Nat.card C * Nat.card W := by
    calc
      Nat.card V = Nat.card (C ⊔ W : Subgroup G) := by
        rw [sup_comm]
        exact congrArg (fun A : Subgroup G => Nat.card A) hd.1.symm
      _ = _ := card_sup_eq_mul_of_normalizes_of_disjoint C W hnorm hdisW
  have hi := relIndex_mul_relIndex (⊥ : Subgroup G) C V bot_le inf_le_left
  simp only [relIndex_bot_left] at hi
  rw [hcardV] at hi
  have hrel : C.relIndex V = Nat.card W :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos hi
  have hcenterL : center L = ⊥ := by
    let hmodel : BenderSuzuki.IsSimpleBenderGroup (SuzukiMatrixGroup m) :=
      .isSuzuki ⟨m, by omega, ⟨MulEquiv.refl _⟩⟩
    apply (center L).eq_bot_iff_forall.mpr
    intro x hx
    apply e.injective
    rw [map_one]
    have hx' : e x ∈ center (SuzukiMatrixGroup m) :=
      (centerCongr e ⟨x, hx⟩).property
    rw [BenderSuzuki.ZD.bender_center_eq_bot hmodel] at hx'
    exact hx'
  have hinner : Function.Injective (MulAut.conj : L →* MulAut L) :=
    MulAut.conj_injective_of_center_eq_bot hcenterL
  have hrangeCard : Nat.card (componentAction h hU hL).range =
      2 ^ (2 * m + 1) := by
    rw [hrange, card_map_of_injective hinner,
      card_map_of_injective (S : Subgroup L).subtype_injective, hcard]
  have hidx : C.relIndex V = Nat.card (componentAction h hU hL).range := by
    rw [← index_ker, componentAction_ker]
    exact inf_relIndex_left V (centralizer (L : Set G))
  have hdisp : Nat.card (⁅V, L ⊓ M⁆ : Subgroup G) = 2 ^ (2 * m + 1) := by
    change Nat.card W = _
    calc
      Nat.card W = C.relIndex V := hrel.symm
      _ = Nat.card (componentAction h hU hL).range := hidx
      _ = _ := hrangeCard
  refine ⟨hfixed, hdisp, ?_⟩
  let X := D.map L.subtype
  have hX : X ≤ L ⊓ M := by
    rw [← hB]
    have hdN : (D : Subgroup L) ≤ normalizer (S : Set L) := by
      rw [← hsup]
      exact le_sup_right
    exact fun x hx => by
      obtain ⟨d, hd, rfl⟩ := hx
      have hdN' : (d : L) ∈ normalizer (S : Set L) := hdN hd
      exact mem_map_of_mem L.subtype hdN'
  have hgen : A ⊔ X = L ⊓ M := by
    change (S : Subgroup L).map L.subtype ⊔ D.map L.subtype = _
    rw [← Subgroup.map_sup, hsup]
    exact hB
  have hBN : L ⊓ M ≤ normalizer (V : Set G) :=
    component_intersection_normalizes h hU hL.1
  have hXN : X ≤ normalizer (A : Set G) := by
    rw [← hC]
    apply (le_inf ((hX.trans inf_le_left).trans L.le_normalizer)
      ((hX.trans hBN).trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  have hdisAX : Disjoint A X := by
    change Disjoint ((S : Subgroup L).map L.subtype) (D.map L.subtype)
    apply Subgroup.disjoint_map L.subtype_injective
    apply disjoint_iff.mpr
    rw [hdis]
  have hcardAX : Nat.card A * Nat.card X = Nat.card (L ⊓ M : Subgroup G) := by
    rw [← hgen]
    exact (card_sup_eq_mul_of_normalizes_of_disjoint A X hXN hdisAX).symm
  let B' := L ⊓ M
  let eL := (subgroupOfEquivOfLe hBN).symm
  let f : B' →* inducedAutomizer V B' :=
    (V.normalizerMonoidHom.rangeRestrict.subgroupMap
      (B'.subgroupOf (normalizer (V : Set G)))).comp eL.toMonoidHom
  have hf : Function.Surjective f :=
    (MonoidHom.subgroupMap_surjective _ _).comp eL.surjective
  have hker : f.ker.map B'.subtype = L ⊓ centralizer (V : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.property.1, ?_⟩
      change (y : G) ∈ centralizer (V : Set G)
      have heq : V.normalizerMonoidHom ⟨(y : G), hBN y.property⟩ = 1 :=
        congrArg (fun z => z.val.val) hy
      simpa only [Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] using
        (show (⟨(y : G), hBN y.property⟩ : normalizer (V : Set G)) ∈
          V.normalizerMonoidHom.ker from heq)
    · intro hx
      let y : B' := ⟨x, hx.1, h.centralizer_le hx.2⟩
      refine ⟨y, ?_, rfl⟩
      change f y = 1
      apply Subtype.ext
      apply Subtype.ext
      change V.normalizerMonoidHom ⟨x, hBN y.property⟩ = 1
      change (⟨x, hBN y.property⟩ : normalizer (V : Set G)) ∈
        V.normalizerMonoidHom.ker
      rw [Subgroup.normalizerMonoidHom_ker]
      exact hx.2
  have hkerA : f.ker.map B'.subtype = A := hker.trans hC
  let X₀ := X.subgroupOf B'
  have hmapX : X₀.map B'.subtype = X := by
    rw [subgroupOf_map_subtype, inf_eq_left.mpr hX]
  have hdis0 : Disjoint f.ker X₀ := by
    apply disjoint_iff.mpr
    have hAXbot : A ⊓ X = ⊥ := disjoint_iff.mp hdisAX
    have hmapzero : (f.ker ⊓ X₀).map B'.subtype = ⊥ := by
      rw [Subgroup.map_inf _ _ B'.subtype B'.subtype_injective, hkerA, hmapX,
        hAXbot]
    apply le_bot_iff.mp
    intro x hx
    have hxmap := mem_map_of_mem B'.subtype hx
    rw [hmapzero] at hxmap
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hxmap
  have hcardker : Nat.card f.ker = Nat.card A := by
    rw [← hkerA, card_map_of_injective B'.subtype_injective]
  have hcardX0 : Nat.card X₀ = Nat.card X := by
    exact Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv
  have hcard0 : Nat.card f.ker * Nat.card X₀ = Nat.card B' := by
    rw [hcardker, hcardX0]
    exact hcardAX
  have hcomp : f.ker.IsComplement' X₀ :=
    isComplement'_of_card_mul_and_disjoint hcard0 hdis0
  have heX : X ≃* Multiplicative (ZMod (2 ^ (2 * m + 1) - 1)) := by
    exact (D.equivMapOfInjective L.subtype L.subtype_injective).symm.trans eD
  have heX0 : X₀ ≃* Multiplicative (ZMod (2 ^ (2 * m + 1) - 1)) :=
    by
      have he0 := X₀.equivMapOfInjective B'.subtype B'.subtype_injective
      rw [hmapX] at he0
      exact he0.trans heX
  have heq : B' ⧸ f.ker ≃* inducedAutomizer V B' :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  refine ⟨heq.symm.trans (hcomp.symm.QuotientMulEquiv.trans heX0)⟩

end CFSG.Quasithin.ChapterE.Section06.Components.LieSieve.RankOne
