module
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable.WeightFourReturning
public import Theory.Representation.BinaryPermutation.SixCoreEightFixedFamily
public import CFSG.Quasithin.Chapter12.Section02.RecognitionSource.LocalConfigurationPrefix

/-!
# Zeroth weak closure in the weight-four branch

A noncentral conjugate A=Vʸ contained in M has an order-eight permutation
image and a proper opposite-normalizer hyperplane U. The point-radical
image has fixed codimension at least three, contradicting the two indices
at most two along U≤V. The other image contains two transpositions. Each
cyclic preimage has corank two in A, so the original rank bound places
its centralizer in Mʸ. Both transpositions must therefore fix the same
hyperplane U, contradicting their distinctness.

Every conjugate in T consequently centralizes V. Applying the original
chosen-module Sylow-kernel uniqueness proves N_G(W₀(T,V))≤M. Unique escape
and normalizer fusion retain their earlier-source producers; no universal
nonsolvability assertion is reconstructed from a single point.

Source: Aschbacher–Smith 13.4.16, weak-closure claim, printed p.913,
refs/quasithin.pdf. Product reciprocity and the coset graph remain separate
steps after this claim.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
namespace CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
open Chapter12.Section02 BinaryConjugationCoordinates
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Every conjugate of the original core contained in M centralizes V in
the weight-four branch. -/
theorem weight_four_contained_conjugate_commutes
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hweight : m.weight z = 4)
    (y : G) (hy : V.conjBy y ≤ normalizer (L : Set G))
    : ⁅V,V.conjBy y⁆ = ⊥ := by
  by_contra hmove
  obtain ⟨hnot,himage,hUi,hCU,hfamily,_⟩ := weight_four_returning_hyperplane
    h structural D m z hz1 hzT hzout hunique hfusion hweight y hy hmove
  let A := V.conjBy y
  let U := V ⊓ (normalizer (L : Set G)).conjBy y
  let := D.elementary
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  have hn := normalizer_component_le_module h structural D m
  obtain ⟨q,hq,_,_⟩ := exists_core_normalizer_permutation D m hn
  let f := q.comp (inclusion hy)
  have hf (a : A) (v : V) :
      (m.coordinate (V.normalizerMonoidHom ⟨a.val,(hy.trans hn) a.property⟩ v)).toAdd =
        BinaryPermutation.coreRepresentation (Fin 6) (f a) (m.coordinate v).toAdd :=
    hq (inclusion hy a) v
  let : IsElementaryAbelian 2 f.range :=
    IsElementaryAbelian.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hcard := model_card_range A V (hy.trans hn)
    (BinaryPermutation.coreRepresentation (Fin 6)) BinaryPermutation.SixCoreNormalizer.action_injective
    f m.coordinate hf
  rw [inf_relIndex_left] at hcard
  have he : Nat.card f.range = 8 := hcard.trans himage
  have hCVAU : V ⊓ centralizer (A : Set G) ≤ U := by
    apply inf_le_inf_left
    exact hfamily A le_rfl (by change Nat.log 2 (A.relIndex A) ≤ 2; simp)
  have hcEq : centralizer (A : Set G) ⊓ U = V ⊓ centralizer (A : Set G) :=
    le_antisymm (le_inf (inf_le_right.trans inf_le_left) inf_le_left)
      (le_inf inf_le_right hCVAU)
  change (centralizer (A : Set G)).relIndex U ≤ 2 at hCU
  have hcindex : (centralizer (A : Set G)).relIndex V ≤ 4 := by
    have hh := relIndex_inf_mul_relIndex (centralizer (A : Set G)) U V
    rw [inf_of_le_left (show U ≤ V from inf_le_left),hcEq,hUi] at hh
    rw [inf_relIndex_left] at hh
    omega
  rcases BinaryPermutation.SixCoreWeightFour.eight_fixed_alternative f.range he.ge with hd | ⟨s,hs,t,ht,hss,htt,hst⟩
  · rw [model_fixed_index A V (hy.trans hn) (BinaryPermutation.coreRepresentation (Fin 6))
      f m.coordinate hf] at hcindex
    have hlo := Nat.pow_le_pow_right (by decide : 0 < 2) hd
    omega
  have hswap (t : Equiv.Perm (Fin 6)) (ht : t ∈ f.range) (hs : t.IsSwap) :
      ∀ v : V, BinaryPermutation.coreRepresentation (Fin 6) t (m.coordinate v).toAdd =
        (m.coordinate v).toAdd ↔ v.val ∈ U := by
    let B₀ := (zpowers t).comap f
    let B := B₀.map A.subtype
    have hBA : B ≤ A := map_subtype_le _
    have htcard : Nat.card (zpowers t) = 2 := by rw [Nat.card_zpowers,hs.orderOf]
    have htR : zpowers t ≤ f.range := zpowers_le.mpr ht
    have hti : (zpowers t).relIndex f.range = 4 := by
      have hh : Nat.card (zpowers t) * (zpowers t).relIndex f.range = Nat.card f.range := by
        rw [←Nat.card_congr (subgroupOfEquivOfLe htR).toEquiv]
        exact ((zpowers t).subgroupOf f.range).card_mul_index
      rw [htcard,he] at hh
      omega
    have hBi : B.relIndex A = 4 := by
      have heA : A = (⊤ : Subgroup A).map A.subtype := by
        rw [←MonoidHom.range_eq_map,range_subtype]
      change (B₀.map A.subtype).relIndex A = 4
      conv_lhs => arg 2; rw [heA]
      rw [relIndex_map_map_of_injective _ _ A.subtype_injective,relIndex_top_right]
      exact (index_comap _ _).trans hti
    have hBc : ChapterE.subgroupCorank A B = 2 := by rw [ChapterE.subgroupCorank,hBi]; decide
    have hBC : centralizer (B : Set G) ≤ (normalizer (L : Set G)).conjBy y := by
      exact hfamily B hBA hBc.le
    let j : B →* A := inclusion hBA
    let fB := f.comp j
    have hfB (b : B) (v : V) :
        (m.coordinate (V.normalizerMonoidHom ⟨b.val,(hBA.trans (hy.trans hn)) b.property⟩ v)).toAdd =
          BinaryPermutation.coreRepresentation (Fin 6) (fB b) (m.coordinate v).toAdd := hf (j b) v
    have hBR : fB.range = zpowers t := by
      apply le_antisymm
      · rintro _ ⟨b,rfl⟩
        obtain ⟨a,ha,he⟩ := b.property
        have hj : j b = a := Subtype.ext he.symm
        change f (j b) ∈ zpowers t
        rw [hj]
        exact ha
      · intro a ha
        obtain ⟨b,hb⟩ := htR ha
        refine ⟨⟨b.val,⟨b,?_,rfl⟩⟩,hb⟩
        change f b ∈ zpowers t
        rwa [hb]
    have hsmall : (centralizer (B : Set G)).relIndex V ≤ 2 := by
      rw [model_fixed_index B V (hBA.trans (hy.trans hn))
        (BinaryPermutation.coreRepresentation (Fin 6)) fB m.coordinate hfB,hBR]
      exact Nat.pow_le_pow_right (by decide : 0 < 2)
        (BinaryPermutation.SixCoreWeightFour.swap_fixedCodim_le_one t hs)
    have hCU' : V ⊓ centralizer (B : Set G) ≤ U := inf_le_inf_left V hBC
    have hUC : U ≤ centralizer (B : Set G) := by
      have hh := relIndex_mul_relIndex (V ⊓ centralizer (B : Set G)) U V hCU' inf_le_left
      rw [hUi,inf_relIndex_left] at hh
      have hpos : (V ⊓ centralizer (B : Set G)).relIndex U ≠ 0 := index_ne_zero_of_finite
      exact (relIndex_eq_one.mp (show (V ⊓ centralizer (B : Set G)).relIndex U = 1 by omega)).trans inf_le_right
    intro v
    have hfix : BinaryPermutation.coreRepresentation (Fin 6) t (m.coordinate v).toAdd =
        (m.coordinate v).toAdd ↔ v.val ∈ centralizer (B : Set G) := by
      rw [←mem_fixedSpace_zpowers_iff,←hBR]
      constructor
      · intro hv b hb
        let b' : B := ⟨b,hb⟩
        have hh := hfB b' v
        have hv' : BinaryPermutation.coreRepresentation (Fin 6) (fB b') (m.coordinate v).toAdd =
            (m.coordinate v).toAdd := hv ⟨fB b',⟨b',rfl⟩⟩
        rw [hv'] at hh
        have hc := congrArg Subtype.val (m.coordinate.injective (Multiplicative.toAdd.injective hh))
        exact mul_inv_eq_iff_eq_mul.mp hc
      · intro hv a
        obtain ⟨b,hb⟩ := a.property
        change BinaryPermutation.coreRepresentation (Fin 6) a.val (m.coordinate v).toAdd = _
        rw [←hb,←hfB b v]
        apply congrArg (fun w : V => (m.coordinate w).toAdd)
        apply Subtype.ext
        exact mul_inv_eq_iff_eq_mul.mpr (hv b.val b.property)
    exact hfix.trans ⟨fun hv => hCU' ⟨v.property,hv⟩,fun hv => hUC hv⟩
  apply hst
  apply BinaryPermutation.SixCoreWeightFour.swap_eq_of_fixed_le s t hss htt
  intro v hv
  let w := m.coordinate.symm (Multiplicative.ofAdd v)
  have hw : (m.coordinate w).toAdd = v := by simp [w]
  have hsfix : BinaryPermutation.coreRepresentation (Fin 6) s (m.coordinate w).toAdd =
      (m.coordinate w).toAdd := by rwa [hw]
  have htfix := (hswap t ht htt w).mpr ((hswap s hs hss w).mp hsfix)
  rwa [hw] at htfix

/-- The literal zeroth weak closure centralizes V and has full normalizer in M. -/
theorem weight_four_weakClosure_control
    (h : Hypothesis1223 KnownSimple.IsKnownSimple T L)
    (structural : Structural1222.{u} KnownSimple.IsKnownSimple)
    (D : ChosenModule T L V) (m : CoreMarking D)
    (z : V) (hz1 : z ≠ 1)
    (hzT : z.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G))
    (hzout : ¬ centralizer ({z.val} : Set G) ≤ normalizer (L : Set G))
    (hunique : ∀ w : V, w ≠ 1 → w.val ∈ Stellmacher.omegaOneCenterAmbient (T : Subgroup G) →
      ¬ centralizer ({w.val} : Set G) ≤ normalizer (L : Set G) → w = z)
    (hfusion : ∀ v : V, v ≠ 1 → ∀ w ∈ V, IsConj v.val w →
      ∃ n ∈ normalizer (V : Set G), MulAut.conj n v.val = w)
    (hweight : m.weight z = 4)
    : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G) ∧
      0 < ChapterE.globalW V (T : Subgroup G) ∧
      normalizer (ChapterE.indexedWeakClosure V (T : Subgroup G) 0 : Set G) ≤
        normalizer (L : Set G) := by
  let := D.elementary
  have hW : ChapterE.indexedWeakClosure V (T : Subgroup G) 0 ≤ centralizer (V : Set G) := by
    rw [ChapterE.weakClosure_eq_sSup_gamma]
    apply sSup_le
    intro A hA
    obtain ⟨g,rfl,hg⟩ := (ChapterE.mem_gamma_zero_iff V (T : Subgroup G) A).mp hA
    exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
      (weight_four_contained_conjugate_commutes h structural D m z hz1 hzT hzout
        hunique hfusion hweight g (hg.trans D.sylow_normalizes_component)))
  have hw : 0 < ChapterE.globalW V (T : Subgroup G) := by
    apply bot_lt_iff_ne_bot.mpr
    intro he
    exact ChapterE.globalW_attained (n := 0) he
      (le_inf (ChapterE.indexedWeakClosure_le _ _ _) hW)
  refine ⟨hW,hw,?_⟩
  exact ChapterE.SourceContainment.normalizer_weakClosure_zero_le
    ⟨D.ne_bot,D.le_sylow,((structural G T L h).2.2 V D).1⟩ hw
    (RecognitionSource.chosen_kernel_unique h D structural)

end CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Nonsolvable
