module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveAbelian
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.SmallIndexSource
public import Theory.Representation.BinaryFiveOrbitBounds
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.IndexFiveLower

/-!
# The original quintic closure and its order

For an outside subgroup of Sylow index five, the original quotient is
D₁₀ or Sz(2). The local closure U=⟨Vᴴ⟩ is elementary abelian. Its actual
image modulo the central point has a Sylow-fixed spanning orbit of length
five and faithful H/O₂(H) action. The orbit gives degree at most five;
the order-five element gives degree at least four. Restoring the literal
point of order two makes |U| equal to32 or64.

These are source inputs to the remaining asymmetric amalgam recognition;
no Ree or Tits recognition premise is used. Source: Aschbacher--Smith
14.2.6, 14.2.20(1) and 14.3.5, printed pp.982,988 and991.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
open SourcePreliminaries Chapter15.Section03 Chapter15.Section03.InitialSource ChapterA.Section05To06 Chapter12.Section08
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem tilde_seed_orbit {T : Sylow 2 G} {V : Subgroup G}
    [IsElementaryAbelian 2 V] (F : InvariantFlag T V 2) (H : Subgroup G)
    (hHF : H ≤ F.H) (hTH : (T : Subgroup G) ≤ H)
    (hVN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hV : Nat.card V = 4) [IsElementaryAbelian 2 (F.tilde (F.UH H))] :
    ∃ w : F.tilde (F.UH H), w ≠ 1 ∧
      (∀ s : T.subtype hTH,
        F.localTildeAction H hHF s w = w) ∧
      Submodule.span (ZMod 2) (Set.range (fun h : H =>
        Representation.elementaryRepresentation (p := 2)
          (F.localTildeAction H hHF) h (Additive.ofMul w))) = ⊤ := by
  let U := F.UH H
  let hUF := F.UH_le_H H hHF
  let c := F.tildeMap U hUF
  let i : V →* U := inclusion (le_conjugateSpanBy V H)
  let f := c.comp i
  have hk : f.ker = (F.Vi 1).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    change F.tildeProjection _ = 1 ↔ _
    exact QuotientGroup.eq_one_iff _
  have hkc : Nat.card f.ker = 2 := by
    rw [hk, Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv]
    exact F.card 1 (by decide)
  have hfc : Nat.card f.range = 2 := by
    have hh := f.ker.card_mul_index
    rw [index_ker,hkc,hV] at hh
    omega
  obtain ⟨w,hw,hu⟩ := (Nat.card_eq_two_iff' (1 : f.range)).mp hfc
  have hw' : (w : F.tilde U) ≠ 1 := by
    intro he
    exact hw (Subtype.ext he)
  have hs (v : V) : f v = 1 ∨ f v = w.val := by
    by_cases hv : f v = 1
    · exact Or.inl hv
    · exact Or.inr (congrArg Subtype.val (hu ⟨f v,⟨v,rfl⟩⟩
        (fun he => hv (congrArg Subtype.val he))))
  refine ⟨w.val,hw',?_,?_⟩
  · intro s
    have hN := hVN s.property
    have hm : F.localTildeAction H hHF s w.val ∈ f.range := by
      obtain ⟨v,hv⟩ := w.property
      have hx : (s : H).val*v.val*(s : H).val⁻¹ ∈ V :=
        (mem_normalizer_iff.mp hN v.val).mp v.property
      refine ⟨⟨_,hx⟩,?_⟩
      rw [←hv]
      change c (i _) = F.localTildeAction H hHF s (c (i v))
      exact (F.tildeAction_apply_map H U hHF hUF
        (le_normalizer_conjugateSpanBy V H) s (i v)).symm
    have hmne : F.localTildeAction H hHF s w.val ≠ 1 := by
      intro he
      exact hw' ((F.localTildeAction H hHF s).map_eq_one_iff.mp he)
    exact congrArg Subtype.val (hu ⟨_,hm⟩ (fun he => hmne (congrArg Subtype.val he)))
  · apply Representation.conjugateSpan_binary_orbit_span V H U
      (le_conjugateSpanBy V H) rfl c (F.tildeMap_surjective U hUF)
      (F.localTildeAction H hHF) ?_ w.val hs
    intro h x hx
    exact (F.tildeAction_apply_map H U hHF hUF
      (le_normalizer_conjugateSpanBy V H) h x).symm

omit [Finite G] in
private theorem tilde_card_mul_two {T : Sylow 2 G} {V : Subgroup G}
    [IsElementaryAbelian 2 V] (F : InvariantFlag T V 2)
    (H : Subgroup G) (hHF : H ≤ F.H) :
    Nat.card (F.tilde (F.UH H)) * 2 = Nat.card (F.UH H) := by
  let U := F.UH H
  let c := F.tildeMap U (F.UH_le_H H hHF)
  have hk : c.ker = (F.Vi 1).subgroupOf U := by
    ext v
    rw [MonoidHom.mem_ker, Subtype.ext_iff]
    exact QuotientGroup.eq_one_iff _
  have hkc : Nat.card c.ker = 2 := by
    rw [hk]
    exact (Nat.card_congr (subgroupOfEquivOfLe
      (show F.Vi 1 ≤ U from (F.le_seed 1).trans (le_conjugateSpanBy V H))).toEquiv).trans
      (F.card 1 (by decide))
  have hh := c.ker.index_mul_card
  rw [index_ker,hkc] at hh
  have hr : c.range = ⊤ := MonoidHom.range_eq_top.mpr (F.tildeMap_surjective U _)
  simpa only [hr,card_top] using hh

/-- Index five gives the two original quotient models, without a classification premise. -/
theorem source_index_five_models
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hi : (T : Subgroup G).relIndex H = 5) :
    Nonempty ((H ⧸ pCore 2 H) ≃* DihedralGroup 5) ∨
      Nonempty ((H ⧸ pCore 2 H) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 0) := by
  let S := T.subtype hH.1.2
  have hN : normalizer (T : Set G) ≤ M :=
    (source_lemma_14_2_2_7 hG T hempty hM hu hmany hcard e).trans inf_le_left
  have hproper : pCore 2 H < (S : Subgroup H) := by
    apply lt_of_le_of_ne (pCore_isPGroup.le_sylow_of_normal S)
    intro he
    have hn : ((T : Subgroup G).subgroupOf H).Normal := by
      change (S : Subgroup H).Normal
      rw [←he]
      infer_instance
    exact hH.2 (((normal_subgroupOf_iff_le_normalizer hH.1.2).mp hn).trans hN)
  exact sylow_index_five_core_quotient S hi hproper

/-- The literal original quintic closure is elementary of order 32 or 64.
Its order is obtained before any Ree or Tits amalgam recognition. -/
theorem source_index_five_closure_structure
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (hi : (T : Subgroup G).relIndex H = 5) :
    let U := conjugateSpanBy (localModule T M) H
    IsElementaryAbelian 2 U ∧ (Nat.card U = 32 ∨ Nat.card U = 64) := by
  have hm := source_index_five_models hG T hempty hM hu hmany hcard e H hH hi
  let hab := source_index_five_closure_abelian hG T hempty hM hu hmany hcard e H hH hm
  let hv := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hM.1.1.1,hM.1.2⟩
  refine ⟨conjugateSpanBy_elementary_of_commutative _ _,?_⟩
  obtain ⟨he,F,hp,_,_,hloc⟩ := source_lemma_14_2_6 hG T hempty hM hu hmany hcard e
  let := he
  obtain ⟨hHF,h,_,_,_,hk⟩ := hloc H hH
  let : IsElementaryAbelian 2 (F.tilde (F.UH H)) := h.tilde_U_elementary
  have hV : Nat.card (rankTwoSeed T M) = 4 := by
    rw [rankTwoSeed_eq_localModule]
    exact hcard
  obtain ⟨w,_,hfix,hspan⟩ := tilde_seed_orbit F H hHF hH.1.2 h.T_normalizes_V hV
  let ρ := Representation.elementaryRepresentation (p := 2) (F.localTildeAction H hHF)
  have hhi : (T.subtype hH.1.2).index = 5 := hi
  have hupp := BinaryPentagon.finrank_le_five_of_index_five_orbit ρ
    (T.subtype hH.1.2) hhi (Additive.ofMul w)
    (fun s => congrArg Additive.ofMul (hfix s)) hspan
  have hlow := index_five_tilde_finrank_ge_four F H hHF hk hm
  have hd : Module.finrank (ZMod 2) (Additive (F.tilde (F.UH H))) = 4 ∨
      Module.finrank (ZMod 2) (Additive (F.tilde (F.UH H))) = 5 := by omega
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := Additive (F.tilde (F.UH H)))
  rw [Nat.card_congr (Additive.toMul : Additive (F.tilde (F.UH H)) ≃ F.tilde (F.UH H))] at hc
  have hc' : Nat.card (F.tilde (F.UH H)) = 16 ∨ Nat.card (F.tilde (F.UH H)) = 32 := by
    rcases hd with hd | hd
    · left
      simpa only [hd,Nat.card_zmod,show 2^4=16 from rfl] using hc
    · right
      simpa only [hd,Nat.card_zmod,show 2^5=32 from rfl] using hc
  have hmul := tilde_card_mul_two F H hHF
  change Nat.card (F.tilde (F.UH H)) * 2 = Nat.card (conjugateSpanBy (rankTwoSeed T M) H) at hmul
  have hmul' := hmul.trans (congrArg
    (fun V : Subgroup G => Nat.card (conjugateSpanBy V H)) (rankTwoSeed_eq_localModule T M))
  rcases hc' with hc' | hc' <;> rw [hc'] at hmul' <;> omega

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam
