module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight.EvenRankTwoBasic
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.RankTwoPerfect
public import CFSG.Quasithin.ChapterA.Section02.Statements.Models
public import Theory.AtlasPort.LinearGroups.G2.PerfectSubgroups
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.AtlasPort.LinearGroups.G2.DerivedEvenOrder
public import Theory.SpecificGroups.Triality.InvolutionFixedRank
public import Theory.SpecificGroups.ReeF4.ConverseParabolics.TwoLocalOrders
public import Theory.SpecificGroups.Tits.FiniteSimple

/-!
# Even rank-two exclusions for local A₈ sections with nontrivial core

The original local component is perfect and has three-rank two. Linear,
symplectic and G₂ full-Sylow overgroups then generate the entire ambient
group, contradicting the nontrivial intrinsic core in a simple group.
In triality, the normalizer of that core embeds in a genuine root parabolic,
whose commutator has three-rank at most one. In Ree, the same normalizer has
order prime to fifteen. The four small rows are excluded by actual orders.

The nontrivial-core premise is explicit: it must survive any preceding
quotient transport before this source specialization is applied.
Source: Aschbacher–Smith A.3.12 and 15.3.32(3), pp.47–48 and 1132.
-/

public section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem map_join_eq_top (S : Sylow 2 G) (B : Subgroup G)
    {H : Type*} [Group H] (e : G ≃* H)
    (h : (B ⊔ (S : Subgroup G)).map e.toMonoidHom = ⊤) :
    B ⊔ (S : Subgroup G) = ⊤ := by
  apply map_injective (f := e.toMonoidHom) e.injective
  rw [h,map_top_of_surjective _ e.surjective]

theorem not_linear_of_core_ne_bot [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    {n : ℕ} (hn : 1 ≤ n) (hm : ClassicalGroup.IsPSL G 3 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  by_cases hn1 : n = 1
  · have hd := ambient_card_dvd hA
    rw [Nat.card_congr e.toEquiv,Matrix.PSL3.LinearThree.card_projective,hF,hn1] at hd
    norm_num at hd
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let := local_perfect hB
  apply join_ne_top_of_core_ne_bot hB hA hcore
  apply map_join_eq_top S B e
  apply Matrix.PSL3.LinearThree.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    F (p := 3) (by decide) (by rw [threeRank hA]) (by omega : 1 < n) hF
    (S.mapSurjective e.surjective) _ (map_mono le_sup_right)
    (e.toMonoidHom.comp B.subtype) (e.injective.comp B.subtype_injective)
  rintro _ ⟨b,rfl⟩
  exact mem_map_of_mem _ (mem_sup_left b.property)

theorem not_symplectic_of_core_ne_bot [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassicalGroup.IsPSp G 2 (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
  let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
  let := local_perfect hB
  have hq : 2 < Nat.card F := by
    rw [hF]
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
    norm_num at this
    omega
  apply join_ne_top_of_core_ne_bot hB hA hcore
  apply map_join_eq_top S B a
  apply Theory.SpecificGroups.SymplecticFour.perfect_odd_rank_two_sylow_overgroup_eq_top
    (p := 3) (by decide) (by rw [threeRank hA]) hq
    (S.mapSurjective a.surjective) _ (map_mono le_sup_right)
    (a.toMonoidHom.comp B.subtype) (a.injective.comp B.subtype_injective)
  rintro _ ⟨b,rfl⟩
  exact mem_map_of_mem _ (mem_sup_left b.property)

theorem not_g2_of_core_ne_bot [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    {n : ℕ} (hn : 2 ≤ n) (hm : ClassificationModels.IsG2At G (2 ^ n)) : False := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hF)
  let := local_perfect hB
  have hq : 2 < Nat.card F := by
    rw [hF]
    have := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
    norm_num at this
    omega
  apply join_ne_top_of_core_ne_bot hB hA hcore
  apply map_join_eq_top S B e
  apply Atlas.G2.PerfectSubgroups.perfect_odd_rank_two_sylow_overgroup_eq_top
    (p := 3) (by decide) (by rw [threeRank hA]) hq
    (S.mapSurjective e.surjective) _ (map_mono le_sup_right)
    (e.toMonoidHom.comp B.subtype) (e.injective.comp B.subtype_injective)
  rintro _ ⟨b,rfl⟩
  exact mem_map_of_mem _ (mem_sup_left b.property)

omit [Finite G] in
private theorem embedded_core {H : Type*} [Group H] (e : G ≃* H)
    (B : Subgroup G) (hcore : pCore 2 B ≠ ⊥) :
    ∃ R : Subgroup H, R ≠ ⊥ ∧ IsPGroup 2 R ∧ B.map e.toMonoidHom ≤ normalizer (R : Set H) := by
  let R := (pCore 2 B).map B.subtype
  have hR : R ≠ ⊥ := by
    intro h
    exact hcore ((map_eq_bot_iff_of_injective (pCore 2 B) B.subtype_injective).mp h)
  refine ⟨R.map e.toMonoidHom, ?_, (pCore_isPGroup.map B.subtype).map e.toMonoidHom, ?_⟩
  · intro h
    exact hR ((map_eq_bot_iff_of_injective R (f := e.toMonoidHom) e.injective).mp h)
  · exact (map_mono (B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))).trans
      (le_normalizer_map e.toMonoidHom)

theorem not_triality_of_core_ne_bot
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    {n : ℕ} (hn : 1 ≤ n) (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) G) : False := by
  let hn' : 0 < n := by omega
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n hn').mp hm
  obtain ⟨R,hR,hp,hBR⟩ := embedded_core e B hcore
  obtain ⟨g,a,hg⟩ := Triality.Standard.TwoLocalCover.normalizer_cover n hn' R hR hp
  let P := Triality.Standard.Parabolics.parabolic (Triality.Standard.binaryParameters n hn') a
  let j := (MulAut.conj g).toMonoidHom.comp (e.toMonoidHom.comp B.subtype)
  have him : ∀ b, j b ∈ P := by
    intro b
    exact hg (mem_map_of_mem _ (hBR (mem_map_of_mem _ b.property)))
  let f : B →* P := j.codRestrict P him
  have hf : Function.Injective f := fun x y h =>
    B.subtype_injective (e.injective ((MulAut.conj g).injective (congrArg Subtype.val h)))
  let := local_perfect hB
  let : Group.IsPerfect f.range := Group.IsPerfect.range f
  have hd : f.range ≤ commutator P := by
    rw [← commutator_eq_self (H := f.range)]
    exact commutator_mono le_top le_top
  let k := f.codRestrict (commutator P) (fun x => hd ⟨x,rfl⟩)
  have hk : Function.Injective k := fun x y h => hf (congrArg Subtype.val h)
  have hb := (Theory.GroupTheory.primeRank_le_of_injective 3 k hk).trans
    (Triality.Standard.InvolutionFixedRank.derived_parabolic_threeRank_le_one
      (Triality.Standard.binaryParameters n hn') rfl a)
  rw [threeRank hA] at hb
  omega

omit [Finite G] in
theorem not_ree_of_core_ne_bot {B : Subgroup G}
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    {m : ℕ} (hm : 1 ≤ m) (e : G ≃* ReeF4.Model m) : False := by
  obtain ⟨R,hR,hp,hBR⟩ := embedded_core e B hcore
  apply ReeF4.ConverseParabolics.normalizer_fifteen_free hm R hR hp
  have hd := card_dvd_of_le hBR
  rw [card_map_of_injective e.injective] at hd
  exact (show 15 ∣ 20160 by decide).trans ((quotient_card_dvd hA).trans hd)

/-- The eight actual Theorem C rank-two rows, retaining the intrinsic core
condition needed for the two-local triality and Ree arguments. -/
theorem not_rankTwo_of_core_ne_bot [IsSimpleGroup G]
    (S : Sylow 2 G) {B : Subgroup G} (hB : B ∈ localCComponents S)
    (hA : ClassicalGroup.IsPSL (B ⧸ pCore 2 B) 4 2) (hcore : pCore 2 B ≠ ⊥)
    {n : ℕ} (hm : ChapterA.Section02.IsTheoremCRankTwoModel G n) : False := by
  cases hm with
  | linear hn hm => exact not_linear_of_core_ne_bot S hB hA hcore hn hm
  | symplectic hn hm => exact not_symplectic_of_core_ne_bot S hB hA hcore hn hm
  | g2 hn hm => exact not_g2_of_core_ne_bot S hB hA hcore hn hm
  | triality hn hm => exact not_triality_of_core_ne_bot S hB hA hcore hn hm
  | ree_f4 m hm _ he => exact not_ree_of_core_ne_bot hA hcore hm he.some
  | symplectic_derived _ he =>
    have hd := ambient_card_dvd hA
    rw [Nat.card_congr (he.some.trans
      Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
      nat_card_alternatingGroup] at hd
    norm_num at hd
  | g2_derived _ he =>
    have hd := ambient_card_dvd hA
    rw [Nat.card_congr he.some.toEquiv,
      Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
    norm_num at hd
  | tits _ he =>
    have hd := ambient_card_dvd hA
    rw [Nat.card_congr he.some.toEquiv,Tits.parrottGroup_card] at hd
    norm_num at hd

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.AlternatingEight
