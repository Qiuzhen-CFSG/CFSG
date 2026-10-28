module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.OriginalRadical
public import CFSG.Quasithin.ChapterB.Section03.Offenders.SixCorePlane
public import Theory.SpecificGroups.SymmetricSix.Parabolics.TwoCores.Syntheme
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.PCoreProduct

/-!
# The actual cubic normalizer in the three-pair branch

The original MS2(a) witness is uniquely determined in this branch. Its
image lies in the normalizer of the three pair swaps, the syntheme
stabilizer of order 48. Odd index and its two-core of order eight force
that image to have order 48: the only proper odd-index alternative has
order sixteen and would be its own two-core. Pullback identifies the
original witness with the full radical normalizer and fixes its index
at fifteen. Restriction uses the actual original and replacement quotient
maps, so the same witness restricts to the replacement radical normalizer.

On that normalizer we construct the action on the three marked pairs.
Its kernel is literally the replacement radical restricted to the
normalizer, giving the S₃ quotient. A power of a preimage of the pair
rotation removes its two-part while preserving that rotation, producing
an actual element of order three. The beyond-four consumer constructs
these facts without an image, quotient or lift premise, and the final
consumer places that same element in the original MS2(a) witness.

These are local inputs for the Section 5 three-pair argument, not the
remaining distance contradiction. Both moved covers, the original
nonsylow radical, and the characteristic replacement are unchanged.

Source: Aschbacher--Smith C.1.31 (MS2)(a), printed p.135;
Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), Section 5, pp.912--927, and the characteristic reduction in
Section 7, pp.932--933. The S₃ model is the existing actual syntheme action.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open Theory.SpecificGroups.SymmetricSix
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
namespace CubeRadical
local notation "S" => Equiv.Perm (Fin 6)
private abbrev flip : S := dWords 7

private theorem cube_normalizer : normalizer (D 6 : Set S) = synthemeStabilizer := by
  apply le_antisymm
  · intro g hg
    have ht : flip ∈ D 6 := (mem_disjointTranspositions_iff (3 : Fin 4) _).mpr ⟨7,rfl⟩
    obtain ⟨i,hi⟩ := (mem_disjointTranspositions_iff (3 : Fin 4) _).mp
      ((mem_normalizer_iff.mp hg flip).mp ht)
    have hs : (g*flip*g⁻¹).support.card = 6 := by
      rw [Equiv.Perm.card_support_conj]
      decide
    rw [←hi] at hs
    have cert : ∀ i : Fin 8, (dWords i).support.card=6 → dWords i=flip := by decide +kernel
    have he : g*flip=flip*g := mul_inv_eq_iff_eq_mul.mp (hi.symm.trans (cert i hs))
    have h1 : g 1=flip (g 0) := congrArg (fun q : S => q 0) he
    have h3 : g 3=flip (g 2) := congrArg (fun q : S => q 2) he
    have h5 : g 5=flip (g 4) := congrArg (fun q : S => q 4) he
    change baseSyntheme.image (fun t => t.image g)=baseSyntheme
    have hc : ∀ i j k : Fin 6, i ≠ j → i ≠ flip j → i ≠ k → i ≠ flip k →
        j ≠ k → j ≠ flip k →
        ({pair i (flip i),pair j (flip j),pair k (flip k)} : Finset (Finset (Fin 6))) = baseSyntheme := by
      decide +kernel
    have hh := hc (g 0) (g 2) (g 4) (g.injective.ne (by decide))
      (h3 ▸ g.injective.ne (by decide : (0:Fin 6)≠3))
      (g.injective.ne (by decide)) (h5 ▸ g.injective.ne (by decide : (0:Fin 6)≠5))
      (g.injective.ne (by decide)) (h5 ▸ g.injective.ne (by decide : (2:Fin 6)≠5))
    simpa only [baseSyntheme,pair,Finset.image_insert,Finset.image_singleton,h1,h3,h5] using hh
  · rw [← CFSG.Quasithin.ChapterB.Offenders.SixCorePlane.cube_eq]
    exact BinaryFlags.H2_normalizes_D


private theorem cube_witness_image {A : Type*} [Group A] [Finite A]
    (q : A →* S) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (H T : Subgroup A) (hker : q.ker ≤ T) (hodd : Odd H.index)
    (hcore : H.pCoreIn 2 = T) (u : S)
    (himage : T.map q = (D 6).map (MulAut.conj u).toMonoidHom) :
    H.map q = synthemeStabilizer.map (MulAut.conj u).toMonoidHom := by
  let N := normalizer (T.map q : Set S)
  have hN : N = synthemeStabilizer.map (MulAut.conj u).toMonoidHom := by
    rw [show N = normalizer (T.map q : Set S) from rfl,himage,
      ←map_normalizer_eq_of_bijective (D 6) (MulAut.conj u).bijective,cube_normalizer]
  have hNc : Nat.card N=48 := by
    rw [hN,card_map_of_injective (MulAut.conj u).injective,synthemeStabilizer_order]
  have hTH : T ≤ H := hcore ▸ pCoreIn_le 2 H
  have hHN : H.map q ≤ N := by
    apply (map_mono ?_).trans (le_normalizer_map q)
    rw [←hcore]
    exact H.le_normalizer.trans (normalizer_le_normalizer_characteristic_image H (pCore 2 H))
  have hTc : Nat.card (T.map q)=8 := by
    rw [himage,card_map_of_injective (MulAut.conj u).injective]
    exact card_disjointTranspositions 3
  have hHC : (H.map q).pCoreIn 2=T.map q := by
    rw [←map_pCoreIn_of_ker_isPGroup q hk H,hcore]
  have hHo : Odd (H.map q).index := (H.index_map_eq hq (hker.trans hTH)).symm ▸ hodd
  have hrelOdd := Odd.of_dvd_nat hHo (relIndex_dvd_index_of_le hHN)
  have hprod := relIndex_mul_relIndex (⊥ : Subgroup S) (H.map q) N bot_le hHN
  rw [relIndex_bot_left,relIndex_bot_left,hNc] at hprod
  have hHc : 8 ≤ Nat.card (H.map q) := hTc ▸ card_le_of_le (map_mono hTH)
  have hbound : (H.map q).relIndex N ≤ 6 := by
    have hh := Nat.mul_le_mul_right ((H.map q).relIndex N) hHc
    omega
  have hrel : (H.map q).relIndex N=1 := by
    obtain ⟨k,hkodd⟩ := hrelOdd
    have hs : (H.map q).relIndex N=1 ∨ (H.map q).relIndex N=3 ∨
      (H.map q).relIndex N=5 := by omega
    rcases hs with hs | hs | hs
    · exact hs
    · have h16 : Nat.card (H.map q)=16 := by rw [hs] at hprod; omega
      have hp : IsPGroup 2 (H.map q) := IsPGroup.of_card (n := 4) h16
      have hc := pCoreIn_eq_self_of_isPGroup 2 (H.map q) hp
      have hh := congrArg (fun U : Subgroup S => Nat.card U) (hHC.symm.trans hc)
      rw [hTc,h16] at hh
      omega
    · rw [hs] at hprod
      omega
  exact (le_antisymm hHN (relIndex_eq_one.mp hrel)).trans hN

private theorem cube_witness_eq_normalizer {A : Type*} [Group A] [Finite A]
    (q : A →* S) (hq : Function.Surjective q) (hk : IsPGroup 2 q.ker)
    (H T : Subgroup A) (hker : q.ker ≤ T) (hodd : Odd H.index)
    (hcore : H.pCoreIn 2 = T) (u : S)
    (himage : T.map q = (D 6).map (MulAut.conj u).toMonoidHom) :
    H = normalizer (T : Set A) ∧ H.index = 15 := by
  have hH := cube_witness_image q hq hk H T hker hodd hcore u himage
  have hn : (normalizer (T.map q : Set S)).comap q = normalizer (T : Set A) := by
    rw [comap_normalizer_eq_of_surjective _ hq,comap_map_eq,sup_eq_left.mpr hker]
  have hN : normalizer (T.map q : Set S) =
      synthemeStabilizer.map (MulAut.conj u).toMonoidHom := by
    rw [himage,←map_normalizer_eq_of_bijective (D 6) (MulAut.conj u).bijective,
      cube_normalizer]
  have hTH : T ≤ H := hcore ▸ pCoreIn_le 2 H
  constructor
  · rw [←hn,hN,←hH,comap_map_eq,sup_eq_left.mpr (hker.trans hTH)]
  · rw [←H.index_map_eq hq (hker.trans hTH),hH,
      index_map_of_bijective (MulAut.conj u).bijective,synthemeStabilizer_index]

private theorem cube_witness_action {A : Type*} [Group A] [Finite A]
    (q : A →* S) (hk : IsPGroup 2 q.ker)
    (H : Subgroup A) (u : S)
    (himage : H.map q = synthemeStabilizer.map (MulAut.conj u).toMonoidHom) :
    ∃ f : H →* Equiv.Perm (Fin 3), Function.Surjective f ∧
      f.ker = pCore 2 H ∧ ∀ (g : H) (i : Fin 3),
        (SynthemeCalculation.block i).image ((MulAut.conj u⁻¹) (q g)) =
          SynthemeCalculation.block (f g i) := by
  let q₀ := (MulAut.conj u⁻¹).toMonoidHom.comp q
  have h₀ : H.map q₀ = synthemeStabilizer := by
    rw [show q₀ = (MulAut.conj u⁻¹).toMonoidHom.comp q from rfl,←map_map,himage,map_map]
    have he : (MulAut.conj u⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        MonoidHom.id S := by
      ext x
      simp [MulAut.conj_apply,mul_assoc]
    rw [he,map_id]
  let k : H →* synthemeStabilizer :=
    (q₀.comp H.subtype).codRestrict synthemeStabilizer
      (fun g => h₀ ▸ mem_map_of_mem q₀ g.property)
  have hkSurj : Function.Surjective k := by
    rintro ⟨g,hg⟩
    have hg' : g ∈ H.map q₀ := h₀.symm ▸ hg
    obtain ⟨x,hx,rfl⟩ := hg'
    exact ⟨⟨x,hx⟩,rfl⟩
  have hkKer : k.ker = q.ker.comap H.subtype := by
    ext g
    change (⟨(MulAut.conj u⁻¹) (q g),_⟩ : synthemeStabilizer) = 1 ↔ q g = 1
    rw [Subtype.ext_iff]
    exact (MulAut.conj u⁻¹).map_eq_one_iff
  have hkGroup : IsPGroup 2 k.ker := by
    rw [hkKer]
    exact hk.comap_of_injective H.subtype H.subtype_injective
  let f := synthemeQuotientHom.comp k
  refine ⟨f,synthemeQuotientHom_surjective.comp hkSurj,?_,?_⟩
  · rw [show f = synthemeQuotientHom.comp k from rfl,←MonoidHom.comap_ker,
      synthemeQuotientHom_ker,k.comap_pCore_of_ker_isPGroup hkSurj hkGroup]
  · intro g i
    exact synthemeQuotientHom_blocks (k g) i

private theorem cubic_lift {A : Type*} [Group A]
    (q : A →* S) (hk : IsPGroup 2 q.ker) (N : Subgroup A)
    (r : S) (hr : r^3=1) (hne : r≠1) (hmem : r ∈ N.map q) :
    ∃ x ∈ N, orderOf x=3 ∧ q x=r := by
  obtain ⟨x,hx,hxr⟩ := hmem
  have hxker : x^3 ∈ q.ker := by
    rw [MonoidHom.mem_ker,map_pow,hxr,hr]
  obtain ⟨n,hn⟩ := hk ⟨x^3,hxker⟩
  have hn' : (x^3)^(2^n)=1 := congrArg Subtype.val hn
  have hp : ∀ n : ℕ, r^(4^n)=r := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ,pow_mul,ih,show (4:ℕ)=3+1 from rfl,pow_succ,hr,one_mul]
  let y := x^(4^n)
  have hyq : q y=r := by rw [map_pow,hxr,hp]
  have hy : y^3=1 := by
    calc
      y^3=((x^3)^(2^n))^(2^n) := by
        simp only [y,←pow_mul,show (4:ℕ)^n=2^n*2^n by rw [show (4:ℕ)=2*2 from rfl,mul_pow]]
        congr 1
        ac_rfl
      _ = 1 := by rw [hn',one_pow]
  refine ⟨y,N.pow_mem hx _,orderOf_eq_prime hy ?_,hyq⟩
  intro he
  exact hne (hyq.symm.trans (he ▸ map_one q))

end CubeRadical

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}
local notation "M" => (L ⊔ R : Subgroup G)
local notation "T" => R.subgroupOf (L ⊔ R)
local notation "S" => Equiv.Perm (Fin 6)

/-- Every original MS2(a) witness in the three-pair branch is the full
radical normalizer, has index fifteen, and restricts to the literal
replacement radical normalizer. -/
theorem nonsylow_cube_original_witness_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T)
    (u : S) (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom)
    (H : Subgroup M) (hodd : Odd H.index) (hcore : H.pCoreIn 2 = T) :
    H = normalizer (T : Set M) ∧ H.index = 15 ∧
      H.subgroupOf d.overgroup = normalizer (d.radical : Set d.overgroup) := by
  let q := OriginalRadical.ambientProjection h e hz hn
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hq := OriginalRadical.ambientProjection_surjective h e hz hn s
  have hk : IsPGroup 2 q.ker := by
    rw [show q = OriginalRadical.ambientProjection h e hz hn from rfl,
      OriginalRadical.ambientProjection_kernel]
    exact pCore_isPGroup
  have hker : q.ker ≤ T := by
    rw [show q = OriginalRadical.ambientProjection h e hz hn from rfl,
      OriginalRadical.ambientProjection_kernel]
    exact h.relative_radical.twoCore_le
  have hi := OriginalRadical.nonsylow_radical_image (e := e) (hz := hz) (hn := hn) hb hns
  have he := CubeRadical.cube_witness_eq_normalizer q hq hk H T hker hodd hcore u (hi.trans himage)
  have hs : Function.Surjective (SourceReduction.projection h e hz hn d) := by
    simpa only [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] using s.surjective
  have hpre : H = (normalizer (d.radical.map (SourceReduction.projection h e hz hn d) : Set S)).comap q := by
    rw [←hi,comap_normalizer_eq_of_surjective _ hq,comap_map_eq,sup_eq_left.mpr hker]
    exact he.1
  refine ⟨he.1,he.2,?_⟩
  change H.comap d.overgroup.subtype = _
  rw [hpre,comap_comap,show q = OriginalRadical.ambientProjection h e hz hn from rfl,
    OriginalRadical.ambientProjection_restriction,
    comap_normalizer_eq_of_surjective _ hs,comap_map_eq,
    SourceReduction.projection_kernel,sup_eq_left.mpr (replacement_core_le_radical h d)]

/-- The actual normalizer acts on the three marked pairs with the literal
replacement radical as kernel. Its two-core and ambient index are exact. -/
theorem nonsylow_cube_normalizer_action_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T)
    (u : S) (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    let N := normalizer (d.radical : Set d.overgroup)
    N.pCoreIn 2 = d.radical ∧ N.index = 15 ∧
      ∃ f : N →* Equiv.Perm (Fin 3), Function.Surjective f ∧
        f.ker = d.radical.subgroupOf N ∧ ∀ (g : N) (i : Fin 3),
          (SynthemeCalculation.block i).image
            ((MulAut.conj u⁻¹) (SourceReduction.projection h e hz hn d g)) =
              SynthemeCalculation.block (f g i) := by
  let q := SourceReduction.projection h e hz hn d
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hq : Function.Surjective q := by
    simpa only [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] using s.surjective
  have hk : IsPGroup 2 q.ker := by
    rw [show q = SourceReduction.projection h e hz hn d from rfl,SourceReduction.projection_kernel]
    exact pCore_isPGroup
  have hker : q.ker ≤ d.radical := by
    rw [show q = SourceReduction.projection h e hz hn d from rfl,SourceReduction.projection_kernel]
    exact replacement_core_le_radical h d
  obtain ⟨H,_,hodd,hcore⟩ := OriginalRadical.nonsylow_odd_index_radical
    (e := e) (hz := hz) (hn := hn) hb hns
  have he := CubeRadical.cube_witness_eq_normalizer q hq hk H d.radical hker hodd hcore u himage
  have hi := CubeRadical.cube_witness_image q hq hk H d.radical hker hodd hcore u himage
  have ha := CubeRadical.cube_witness_action q hk H u hi
  rw [he.1] at hcore ha
  have hpc : pCore 2 (normalizer (d.radical : Set d.overgroup)) =
      d.radical.subgroupOf (normalizer (d.radical : Set d.overgroup)) := by
    apply map_injective (normalizer (d.radical : Set d.overgroup)).subtype_injective
    rw [map_subgroupOf_eq_of_le d.radical.le_normalizer]
    exact hcore
  obtain ⟨f,hf,hfk,hblocks⟩ := ha
  exact ⟨hcore,he.1 ▸ he.2,f,hf,hfk.trans hpc,hblocks⟩


/-- The quotient is by the actual radical inside its normalizer. -/
theorem nonsylow_cube_normalizer_quotient_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T)
    (u : S) (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    Nonempty ((normalizer (d.radical : Set d.overgroup)) ⧸
      d.radical.subgroupOf (normalizer (d.radical : Set d.overgroup)) ≃*
        Equiv.Perm (Fin 3)) := by
  obtain ⟨_,_,f,hf,hker,_⟩ := nonsylow_cube_normalizer_action_knownSimple hb hns u himage
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective f hf)⟩

/-- Lift the marked pair rotation to an element of order three in the
actual radical normalizer, retaining the canonical six-letter projection. -/
theorem nonsylow_cube_cubic_knownSimple
    (hb : 2 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T)
    (u : S) (himage : d.radical.map (SourceReduction.projection h e hz hn d) =
      (D 6).map (MulAut.conj u).toMonoidHom) :
    ∃ x : d.overgroup, x ∈ normalizer (d.radical : Set d.overgroup) ∧
      orderOf x=3 ∧ SourceReduction.projection h e hz hn d x =
        (MulAut.conj u) BinaryFlags.pairRotation := by
  let q := SourceReduction.projection h e hz hn d
  let s := fullSymmetricAction_knownSimple h e hz hn d hb
  have hq : Function.Surjective q := by
    simpa only [SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] using s.surjective
  have hk : IsPGroup 2 q.ker := by
    rw [show q = SourceReduction.projection h e hz hn d from rfl,SourceReduction.projection_kernel]
    exact pCore_isPGroup
  have hker : q.ker ≤ d.radical := by
    rw [show q = SourceReduction.projection h e hz hn d from rfl,SourceReduction.projection_kernel]
    exact replacement_core_le_radical h d
  obtain ⟨hc,hi,_⟩ := nonsylow_cube_normalizer_action_knownSimple hb hns u himage
  have hN := CubeRadical.cube_witness_image q hq hk
    (normalizer (d.radical : Set d.overgroup)) d.radical hker (hi ▸ by decide) hc u himage
  apply CubeRadical.cubic_lift q hk _ ((MulAut.conj u) BinaryFlags.pairRotation)
  · rw [←map_pow,show BinaryFlags.pairRotation^3=1 by decide +kernel,map_one]
  · exact (MulAut.conj u).map_ne_one_iff.mpr (by decide +kernel)
  · rw [hN]
    exact mem_map_of_mem _ BinaryFlags.pairRotation_mem_H2

/-- Beyond distance four the nonsylow source hypotheses supply the whole
local cubic configuration; no model or quotient premise is supplied. -/
theorem nonsylow_four_lt_cubic_configuration_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T) :
    ∃ u : S,
      d.radical.map (SourceReduction.projection h e hz hn d) =
        (D 6).map (MulAut.conj u).toMonoidHom ∧
      (normalizer (d.radical : Set d.overgroup)).pCoreIn 2=d.radical ∧
      (normalizer (d.radical : Set d.overgroup)).index=15 ∧
      Nonempty ((normalizer (d.radical : Set d.overgroup)) ⧸
        d.radical.subgroupOf (normalizer (d.radical : Set d.overgroup)) ≃*
          Equiv.Perm (Fin 3)) ∧
      ∃ x : d.overgroup, x ∈ normalizer (d.radical : Set d.overgroup) ∧
        orderOf x=3 ∧ SourceReduction.projection h e hz hn d x =
          (MulAut.conj u) BinaryFlags.pairRotation := by
  obtain ⟨u,hu⟩ := nonsylow_four_lt_radical_image_cube_knownSimple
    (e := e) (hz := hz) (hn := hn) hb hns
  have hb2 : 2 < replacementDistance h d := by omega
  obtain ⟨hc,hi,_⟩ := nonsylow_cube_normalizer_action_knownSimple hb2 hns u hu
  exact ⟨u,hu,hc,hi,nonsylow_cube_normalizer_quotient_knownSimple hb2 hns u hu,nonsylow_cube_cubic_knownSimple hb2 hns u hu⟩

/-- The constructed cubic belongs to the restriction of the original
MS2(a) witness, with that witness's actual index and ambient projection. -/
theorem nonsylow_four_lt_original_cubic_knownSimple
    (hb : 4 < replacementDistance h d)
    (hns : ¬ ∃ P : Sylow 2 M, (P : Subgroup M) = T)
    (H : Subgroup M) (hodd : Odd H.index) (hcore : H.pCoreIn 2 = T) :
    H = normalizer (T : Set M) ∧ H.index = 15 ∧
      H.subgroupOf d.overgroup = normalizer (d.radical : Set d.overgroup) ∧
      ∃ u : S,
        d.radical.map (SourceReduction.projection h e hz hn d) =
          (D 6).map (MulAut.conj u).toMonoidHom ∧
        ∃ x : d.overgroup, (x : M) ∈ H ∧ orderOf x = 3 ∧
          OriginalRadical.ambientProjection h e hz hn (x : M) =
            (MulAut.conj u) BinaryFlags.pairRotation := by
  obtain ⟨u,hu,_,_,_,x,hx,horder,himage⟩ :=
    nonsylow_four_lt_cubic_configuration_knownSimple (e := e) (hz := hz) (hn := hn) hb hns
  obtain ⟨hH,hindex,hrestrict⟩ := nonsylow_cube_original_witness_knownSimple
    (by omega) hns u hu H hodd hcore
  refine ⟨hH,hindex,hrestrict,u,hu,x,?_,horder,?_⟩
  · change x ∈ H.subgroupOf d.overgroup
    rwa [hrestrict]
  · have he := congrArg (fun f : d.overgroup →* S => f x)
      (OriginalRadical.ambientProjection_restriction h e hz hn d)
    exact he.trans himage

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
