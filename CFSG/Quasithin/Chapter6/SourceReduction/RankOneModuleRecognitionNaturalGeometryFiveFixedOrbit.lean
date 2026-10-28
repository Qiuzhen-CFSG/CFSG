module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalGeometryFiveSpanAction

/-!
# The cubic-fixed S5 parabolic and its natural-layer orbit

In the contained S5 branch, let B be the canonical Sylow overgroup in K.
The specified quotient identifies B/O2(K) with an actual point stabilizer
S4. Coprime fixed-point lifting covers that same stabilizer by C_B(c).
A representative of a quotient Sylow element lies in the original T,
because O2(K) lies in T. The proved natural-plane calculation therefore
makes these representatives centralize the whole natural layer.

The conjugation kernel contains the fixed extension kernel and descends
to S4. A Sylow two-subgroup normally generates S4: its normal quotient
has odd order, so the transpositions have trivial image. Thus C_B(c)
centralizes the natural layer. It is the exact pointwise stabilizer inside
C_K(c), and its index is five. The final application keeps the same original
W/Z_S action and all its earlier marked data.

This identifies the actual orbit stabilizer without manufacturing an
ambient elementary lift from the quotient action. S5 escape, the mixed
amalgam contradiction, initial 6.1.4–5, omega escape and unconditional
6.1.27 remain with qt-d-1222-rankone-recognition-natural.

Source: Aschbacher–Smith 6.1.19, printed p.675 (`refs/quasithin.pdf`),
the canonical S5 parabolic in the original invariant cover.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveOrbit
local notation "S5" => Equiv.Perm (Fin 5)
private theorem card_stabilizer (i : Fin 5) :
    Nat.card (MulAction.stabilizer S5 i) = 24 := by
  have hi : (MulAction.stabilizer S5 i).index = 5 := by
    rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ]
    simp
  have hh := (MulAction.stabilizer S5 i).card_mul_index
  rw [hi, Nat.card_perm, show Nat.card (Fin 5) = 5 from by simp] at hh
  norm_num [Nat.factorial] at hh ⊢
  omega

private def point_equiv (i : Fin 5) :
    MulAction.stabilizer S5 i ≃* Equiv.Perm (Fin 4) := by
  classical
  let X := {x : Fin 5 // x ≠ i}
  let f : MulAction.stabilizer S5 i →* Equiv.Perm X := {
    toFun g := g.val.subtypePerm (fun x => by
      have hg : g.val i = i := g.property
      simpa only [hg] using g.val.injective.ne_iff (x := x) (y := i))
    map_one' := by ext x; rfl
    map_mul' := by intros; ext x; rfl }
  have hfi : Function.Injective f := by
    intro g h he
    apply Subtype.ext
    apply Equiv.ext
    intro x
    by_cases hx : x = i
    · subst x; exact g.property.trans h.property.symm
    · exact congrArg Subtype.val (DFunLike.congr_fun he ⟨x,hx⟩)
  have hX : Fintype.card X = 4 := by
    simp [X,Fintype.card_subtype_compl]
  have hc : Nat.card (MulAction.stabilizer S5 i) = Nat.card (Equiv.Perm X) := by
    rw [card_stabilizer,Nat.card_eq_fintype_card,Fintype.card_perm,hX]
    rfl
  let e := MulEquiv.ofBijective f ((Nat.bijective_iff_injective_and_card f).mpr ⟨hfi,hc⟩)
  let b : X ≃ Fin 4 := Fintype.equivFinOfCardEq hX
  exact e.trans (Equiv.permCongrHom b)


private theorem symmetric_odd_quotient {X : Type*} [Group X] [Finite X]
    (f : Equiv.Perm (Fin 4) →* X) (ho : Odd (Nat.card X)) : ∀ g, f g=1 := by
  intro g
  induction g using Equiv.Perm.swap_induction_on with
  | one => exact f.map_one
  | swap_mul g i j hij ih =>
    rw [map_mul,ih,mul_one]
    apply orderOf_eq_one_iff.mp
    apply Nat.eq_one_of_dvd_coprimes (show Nat.Coprime 2 (Nat.card X) from ho.coprime_two_left)
    · apply orderOf_dvd_of_pow_eq_one
      rw [←map_pow]
      simp [pow_two]
    · exact orderOf_dvd_natCard _

private theorem point_normal_sylow_top (i : Fin 5)
    (P : Sylow 2 (MulAction.stabilizer S5 i))
    (J : Subgroup (MulAction.stabilizer S5 i)) [J.Normal]
    (hPJ : (P : Subgroup _) ≤ J) : J=⊤ := by
  have ho : Odd J.index := Nat.not_even_iff_odd.mp (by
    intro he
    exact P.not_dvd_index ((even_iff_two_dvd.mp he).trans (index_dvd_of_le hPJ)))
  have hh := symmetric_odd_quotient
    ((QuotientGroup.mk' J).comp (point_equiv i).symm.toMonoidHom) ho
  apply top_unique
  intro x _
  exact (QuotientGroup.eq_one_iff x).mp (by simpa using hh ((point_equiv i) x))

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalFiveOrbit

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G}

/-- The cubic-fixed part of the contained canonical parabolic fixes the
whole natural layer and has index five in the cover's cubic centralizer. -/
theorem natural_five_contained_fixed_parabolic
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K B : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hBK : B < K) (hSB : (T : Subgroup G) ⊓ K ≤ B) (hBM : B ≤ M)
    (hmax : ∀ C : Subgroup G, (T : Subgroup G) ⊓ K ≤ C → C < K → C ≤ B)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5))
    {c : G} (hcL : c ∈ L) (hcN : c ∈ Escape.H (T : Subgroup G) L R)
    (hc3 : orderOf c=3) :
    B ⊓ centralizer (zpowers c : Set G) ≤ centralizer (layer L R : Set G) ∧
      (B ⊓ centralizer (zpowers c : Set G) : Subgroup G).relIndex
        (K ⊓ centralizer (zpowers c : Set G)) = 5 := by
  let V := layer L R
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 K))
  have hq : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = pCore 2 K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective,QuotientGroup.ker_mk']
  have hTK := h.sylow_normalizes_ZS.trans hNK
  obtain ⟨S,hS⟩ := NormalSylowQuotientAction.intersection_sylow T K hTK
  have hQS : q.ker ≤ (S : Subgroup K) := hqk ▸ pCore_isPGroup.le_sylow_of_normal S
  let B' := B.subgroupOf K
  have hSB' : (S : Subgroup K) ≤ B' := by
    rw [hS]
    exact fun k hk => hSB ⟨hk,k.property⟩
  have hB' : IsCoatom B' := by
    refine ⟨?_,?_⟩
    · intro he
      apply hBK.ne
      have hh := congrArg (map K.subtype) he
      simpa only [B',map_subgroupOf_eq_of_le hBK.le,←MonoidHom.range_eq_map,range_subtype] using hh
    · intro D hBD
      by_contra hn
      have hDK : D.map K.subtype < K := lt_of_le_of_ne (map_subtype_le _) (by
        intro he
        apply hn
        apply map_injective K.subtype_injective
        simpa only [←MonoidHom.range_eq_map,range_subtype] using he)
      have hSD : (T : Subgroup G) ⊓ K ≤ D.map K.subtype := by
        have hh := map_mono (hSB'.trans hBD.le) (f := K.subtype)
        rwa [hS,subgroupOf_map_subtype] at hh
      have hm := hmax _ hSD hDK
      apply hBD.not_ge
      intro k hk
      exact hm (mem_map_of_mem K.subtype hk)
  obtain ⟨i,hi⟩ := Theory.SpecificGroups.SymmetricFive.SylowOvergroup.quotient_image_eq_point_stabilizer
    q hq S B' hSB' hB' (hQS.trans hSB')
  let Y := MulAction.stabilizer (Equiv.Perm (Fin 5)) i
  have hpre : Y.comap q = B' := by
    dsimp only [Y]
    rw [←hi,comap_map_eq_self (hQS.trans hSB')]
  let C := K ⊓ centralizer (zpowers c : Set G)
  let D := B ⊓ centralizer (zpowers c : Set G)
  let f : D →* Y := (q.comp (inclusion (show D ≤ K from inf_le_left.trans hBK.le))).codRestrict Y
    (by
      intro d
      change q ⟨d,hBK.le d.property.1⟩ ∈ MulAction.stabilizer (Equiv.Perm (Fin 5)) i
      rw [←hi]
      exact mem_map_of_mem q (show (⟨d,hBK.le d.property.1⟩ : K) ∈ B' from d.property.1))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨d,hd⟩ := natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3 y.val
    have hdB : (d : G) ∈ B := by
      have hh : (inclusion (show C ≤ K from inf_le_left) d) ∈ Y.comap q := by
        change q (inclusion inf_le_left d) ∈ Y
        rw [show q (inclusion inf_le_left d)=y.val from hd]
        exact y.property
      change (inclusion (show C ≤ K from inf_le_left) d) ∈ B'
      rwa [hpre] at hh
    exact ⟨⟨d,hdB,d.property.2⟩,Subtype.ext hd⟩
  have hDV : D ≤ normalizer (V : Set G) :=
    (le_inf (inf_le_left.trans hBM) ((inf_le_left.trans hBK.le).trans hKI)).trans
      (hE.localCentralizer_le_normalizer h.ZS_ne_bot inf_le_left)
  let a : D →* MulAut V := V.normalizerMonoidHom.comp (inclusion hDV)
  have hker : f.ker ≤ a.ker := by
    intro d hd
    have hqone : q ⟨d,hBK.le d.property.1⟩=1 := congrArg Subtype.val hd
    have hdS : (⟨d,hBK.le d.property.1⟩ : K) ∈ (S : Subgroup K) := hQS hqone
    have hdT : (d : G) ∈ (T : Subgroup G) := by
      rw [hS] at hdS
      exact hdS
    have hcV := natural_four_cubic_fixed_centralizes_layer h hnat hcL hc3 hdT
      (hKI (hBK.le d.property.1)) (show Commute (d : G) c from
        (d.property.2 c (mem_zpowers c)).symm)
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (d : G)*(v : G)*(d : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (hcV v v.property).symm
  let b := f.liftOfSurjective hf ⟨a,hker⟩
  have hb (d : D) : b (f d)=a d := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ d
  have hSY : (S.mapSurjective hq : Subgroup (Equiv.Perm (Fin 5))) ≤ Y :=
    by
      change (S : Subgroup K).map q ≤ MulAction.stabilizer (Equiv.Perm (Fin 5)) i
      rw [←hi]
      exact map_mono hSB'
  let SY := (S.mapSurjective hq).subtype hSY
  have hSYk : (SY : Subgroup Y) ≤ b.ker := by
    intro y hy
    obtain ⟨d,hd⟩ := hf y
    have hdq : q ⟨d,hBK.le d.property.1⟩ = y.val := congrArg Subtype.val hd
    obtain ⟨s,hs,he⟩ := hy
    have hdiff : (⟨d,hBK.le d.property.1⟩ : K)*s⁻¹ ∈ q.ker := by
      change q (_ * _) = 1
      rw [map_mul,map_inv,hdq,he]
      exact mul_inv_cancel _
    have hdS : (⟨d,hBK.le d.property.1⟩ : K) ∈ (S : Subgroup K) := by
      simpa using (S : Subgroup K).mul_mem (hQS hdiff) hs
    have hcV := natural_four_cubic_fixed_centralizes_layer h hnat hcL hc3
      (by rw [hS] at hdS; exact hdS)
      (hKI (hBK.le d.property.1)) (show Commute (d : G) c from
        (d.property.2 c (mem_zpowers c)).symm)
    change b y=1
    rw [←hd,hb]
    apply MulEquiv.ext
    intro v
    apply Subtype.ext
    change (d : G)*(v : G)*(d : G)⁻¹ = v
    exact mul_inv_eq_iff_eq_mul.mpr (hcV v v.property).symm
  have hbk := NaturalFiveOrbit.point_normal_sylow_top i SY b.ker hSYk
  refine ⟨?_,?_⟩
  · intro d hd
    have hd1 : a ⟨d,hd⟩=1 := (hb ⟨d,hd⟩).symm.trans
      (show f ⟨d,hd⟩ ∈ b.ker from hbk ▸ mem_top _)
    intro v hv
    have hh := congrArg (fun k : MulAut V => (k ⟨v,hv⟩ : G)) hd1
    change d*v*d⁻¹=v at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm

  · let fC := q.comp (inclusion (show C ≤ K from inf_le_left))
    have hfC : Function.Surjective fC :=
      natural_five_cubic_fixed_cover h hnat K hKI hNK e hcL hcN hc3
    have hDC : D.subgroupOf C = Y.comap fC := by
      ext x
      change ((x : G) ∈ B ∧ (x : G) ∈ centralizer (zpowers c : Set G)) ↔
        q (inclusion inf_le_left x) ∈ Y
      have hh : q (inclusion inf_le_left x) ∈ Y ↔ (x : G) ∈ B := by
        change inclusion inf_le_left x ∈ Y.comap q ↔ _
        rw [hpre]
        rfl
      rw [hh]
      exact ⟨And.left,fun hx => ⟨hx,x.property.2⟩⟩
    change (D.subgroupOf C).index=5
    rw [hDC,index_comap_of_surjective _ hfC]
    change (MulAction.stabilizer (Equiv.Perm (Fin 5)) i).index=5
    rw [MulAction.index_stabilizer,MulAction.orbit_eq_univ]
    simp

/-- The contained parabolic is exactly the pointwise layer stabilizer
inside the original cubic centralizer, and that stabilizer has index five. -/
@[expose] def NaturalFiveFixedOrbitData (T : Sylow 2 G) (L R K M : Subgroup G) : Prop :=
  ∀ c : G, c ∈ L → c ∈ Escape.H (T : Subgroup G) L R → orderOf c=3 →
    (K ⊓ centralizer (zpowers c : Set G)) ⊓ centralizer (layer L R : Set G) =
      (M ⊓ K) ⊓ centralizer (zpowers c : Set G) ∧
    ((M ⊓ K) ⊓ centralizer (zpowers c : Set G) : Subgroup G).relIndex
      (K ⊓ centralizer (zpowers c : Set G)) = 5

/-- Apply the fixed-parabolic calculation to the literal M-intersection. -/
theorem natural_five_contained_fixed_orbit
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (K B : Subgroup G) (hKI : K ≤ Escape.I (T : Subgroup G) L R)
    (hNK : Escape.H (T : Subgroup G) L R ≤ normalizer (K : Set G))
    (hKM : ¬ K ≤ M) (hBK : B < K) (hSB : (T : Subgroup G) ⊓ K ≤ B)
    (hBM : B ≤ M)
    (hmax : ∀ C : Subgroup G, (T : Subgroup G) ⊓ K ≤ C → C < K → C ≤ B)
    (e : (K ⧸ pCore 2 K) ≃* Equiv.Perm (Fin 5)) :
    NaturalFiveFixedOrbitData T L R K M := by
  have hBeq := (natural_five_contained_overgroup h K B
    (hKI.trans (Subgroup.centralizer_le_normalizer _))
    (h.sylow_normalizes_ZS.trans hNK) hKM hBK hBM hmax).1
  intro c hcL hcN hc3
  obtain ⟨hfix,hindex⟩ := natural_five_contained_fixed_parabolic h hnat hE K B hKI hNK
    hBK hSB hBM hmax e hcL hcN hc3
  rw [hBeq] at hfix hindex
  refine ⟨le_antisymm ?_ ?_,hindex⟩
  · intro x hx
    exact ⟨⟨hE.normalizer_le (Subgroup.centralizer_le_normalizer _ hx.2),hx.1.1⟩,hx.1.2⟩
  · intro x hx
    exact ⟨⟨hx.1.2,hx.2⟩,hfix hx⟩

/-- For the same invariant cover, either the chosen parabolic escapes,
or its cubic-fixed part has the exact pointwise stabilizer and index five. -/
theorem natural_five_amalgam_or_fixed_orbit
    {X : Type*} [Group X]
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R 2)
    (hnat : IsNaturalModule L (layer L R) 2)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (P : Subgroup G) (σ : Escape.I (T : Subgroup G) L R →* MulAut X)
    (hPI : P ≤ Escape.I (T : Subgroup G) L R)
    (h5 : Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5)))
    (hcover : NaturalInvariantCoverData T P (Escape.I (T : Subgroup G) L R)
      (Escape.H (T : Subgroup G) L R) σ hPI)
    (hescape : NaturalEscapingCoverData T P (Escape.H (T : Subgroup G) L R) M)
    (hfive : NaturalFiveCubicParabolicData T L R P (Escape.H (T : Subgroup G) L R)) :
    NaturalEscapingAmalgamData T L R P (Escape.H (T : Subgroup G) L R) M ∨
      NaturalFiveFixedOrbitData T L R (P ⊔ (Escape.H (T : Subgroup G) L R).pCoreIn 2) M := by
  obtain ⟨B,hBK,hSB,_,hTB,⟨c,hcL,hcTL,hcN,hc3,_,hcB⟩,eB,hmax,_,_⟩ := hfive h5
  obtain ⟨hKI,hNK,_,_,⟨eK⟩,_⟩ := hcover
  by_cases hBM : B ≤ M
  · exact Or.inr (natural_five_contained_fixed_orbit h hnat hE _ B hKI hNK hescape.2.1
      hBK hSB hBM hmax (eK.trans h5.some))
  · have hBI := hBK.le.trans hKI
    have hF := natural_cubic_parabolic_hypothesisF11 h hnat B hBI hBM
      (le_sup_left.trans hTB) eB.some hcL hcTL hc3 hcB
    exact Or.inl ⟨B,hBK.le,hBI,hBM,eB,hF,
      natural_cubic_amalgam_right_solvable hF eB.some,hF.generatedLocallyRankOneTriple⟩

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M R : Subgroup G} {n : ℕ}
variable (d : NaturalEscapeGraph.OddConfiguration T L M R)
include d
/-- The same original W/Z_S witness retains its faithful span action and
the exact cubic-fixed pointwise layer stabilizer of index five. -/
theorem exists_ambient_amalgam_or_five_fixed_orbit
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M R n)
    (hnat : IsNaturalModule L (layer L R) n)
    (hE : ChapterE.Section06.HypothesisE61 KnownSimple.IsKnownSimple T M (layer L R))
    (hs : letI := h.layer_elementary; ChapterE.globalS (layer L R) = n)
    (hNS : Subgroup.normalizer (((T : Subgroup G) ⊓
      centralizer (ZS (T : Subgroup G) L R : Set G) : Subgroup G) : Set G) ≤ M)
    (hab : Escape.U (T : Subgroup G) L R ≤
      centralizer (Escape.U (T : Subgroup G) L R : Set G)) :
    n = 2 ∧ ∃ z a : G,
      z ∈ ZS (T : Subgroup G) L R ∧ orderOf z = 2 ∧
      let I := Escape.I (T : Subgroup G) L R
      let N := Escape.H (T : Subgroup G) L R
      let Z := ZS (T : Subgroup G) L R
      let W := Escape.U (T : Subgroup G) L R ⊓
        conjugateSpanBy Z (centralizer ({z} : Set G))
      let E := (layer L R).map (MulAut.conj a).toMonoidHom
      let P := conjugateSpanBy E I
      E ≤ I ∧ Z ≤ W ∧
      ∃ (hPI : P ≤ I) (hPN : P ≤ N) (_hIN : I ≤ N)
        (hIW : I ≤ Subgroup.normalizer (W : Set G))
        (hZ : (Z.subgroupOf W).Normal),
      let := hZ
      ∃ σ : I →* MulAut (W ⧸ Z.subgroupOf W),
        (∀ i : I, ∀ w : W,
          σ i (QuotientGroup.mk' (Z.subgroupOf W) w) =
            QuotientGroup.mk' (Z.subgroupOf W)
              ⟨(i : G) * (w : G) * (i : G)⁻¹,
                (mem_normalizer_iff.mp (hIW i.property) w).mp w.property⟩) ∧
      ∃ hX : IsElementaryAbelian 2 (W ⧸ Z.subgroupOf W),
        let := hX
        IsElementaryAbelian 2 ((E.subgroupOf I).map σ) ∧
        1 < Nat.card ((E.subgroupOf I).map σ) ∧
        Nat.card ((E.subgroupOf I).map σ) ≤ 4 ∧
        let g := σ.comp (inclusion hPI)
        ∃ (φ : (P ⧸ pCore 2 P) →* g.range)
          (j : (P ⧸ pCore 2 P) →* (N ⧸ pCore 2 N)),
          Function.Bijective φ ∧ φ.ker ≤ center (P ⧸ pCore 2 P) ∧
          Function.Injective j ∧ j.range.IsSubnormal ∧
          (∀ p, φ (QuotientGroup.mk' (pCore 2 P) p) = g.rangeRestrict p) ∧
          (∀ p, j (QuotientGroup.mk' (pCore 2 P) p) =
            QuotientGroup.mk' (pCore 2 N) (inclusion hPN p)) ∧
          pCore 2 g.range = ⊥ ∧ g.ker = pCore 2 P ∧
            (Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* BinaryLinear.OuterCyclic.LinearGroup 3) ∨
              Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 5))) ∧
            ((pResidual 2 P).map P.subtype = (primeToResidual 3 I).map I.subtype) ∧
            (N ≤ Subgroup.normalizer ((pResidual 2 P).map P.subtype : Set G)) ∧
            NaturalInvariantCoverData T P I N σ hPI ∧
            NaturalEscapingCoverData T P N M ∧
            NaturalFiveCubicParabolicData T L R P N ∧
            NaturalThreeInvariantParabolicData T L R P N M ∧
            (NaturalEscapingAmalgamData T L R P N M ∨
              (NaturalFiveContainedParabolicData T P N M ∧
                NaturalFiveElementaryRestriction P N ∧
                NaturalFiveCubicFixedData T L R P N ∧
                NaturalFiveSpanActionData T L R (P ⊔ N.pCoreIn 2) ∧
                NaturalFiveFixedOrbitData T L R (P ⊔ N.pCoreIn 2) M ∧
                ∃ c t : G, c ∈ L ∧ c ∈ N ∧ orderOf c=3 ∧
                  t ∈ N.pCoreIn 2 ∧ orderOf t=2 ∧ c*t*c⁻¹=t ∧ t ∉ Z ∧ t ∈ centralizer (layer L R : Set G) ∧
                  t ∈ centralizer (conjugateSpanBy (layer L R)
                    ((P ⊔ N.pCoreIn 2) ⊓ centralizer (zpowers c : Set G)) : Set G))) := by
  obtain ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
      φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,ham⟩ :=
    d.exists_ambient_amalgam_or_five_span_action h hnat hE hs hNS hab
  let := hZ
  let := hX
  refine ⟨hn,z,a,hz,ho,hEI,hZW,hPI,hPN,hIN,hIW,hZ,σ,hσ,hX,hEA,hpos,hupper,
    φ,j,hφ,hφc,hj,hjn,hφe,hje,hred,hk,hmodels,hcanonical,hnormal,hcover,hescape,hfive,hthree,?_⟩
  rcases ham with ham | ⟨hd,hno,hfixed,hspan,hobs⟩
  · exact Or.inl ham
  · rcases natural_five_amalgam_or_fixed_orbit (hn ▸ h) (hn ▸ hnat) hE
      _ σ hPI hd.1 hcover hescape hfive with ham | horbit
    · exact Or.inl ham
    · exact Or.inr ⟨hd,hno,hfixed,hspan,horbit,hobs⟩
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.NaturalEscapeGraph.OddConfiguration
