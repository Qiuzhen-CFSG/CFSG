module

public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six.Containing
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Bender
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.RankTwo
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.SixLocalFF.BinaryLinear
public import Theory.SpecificGroups.SymplecticFour.EvenProjective
public import Theory.SpecificGroups.SymplecticFour.Binary.ProjectiveDerived
public import Theory.SpecificGroups.Triality.InvolutionFixedRank
public import Theory.SpecificGroups.ReeF4.Model.LocalBlock
public import Theory.SpecificGroups.Tits.TwoLocalFifteenFree
public import Theory.Alternating.PrimeRank
public import Theory.Quasithin.CoprimeRank
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.ExceptionalParabolics.FirstParabolic.Order

/-!
# Ordinary containing models for the order-32 A₆ section

The genuine Bender, prime and quadratic PSL₂ embedding theorems, together
with the characteristic-two local placement theorems, exclude the rank-one,
rank-two and binary linear containing families. Triality is excluded by the
three-rank of its parabolic commutator; Ree and Tits by their fifteen-free
two-local normalizers. Actual orders exclude the small alternating and
sporadic groups and the nonclassical triple covers.

The output retains precisely odd prime-field ternary groups and five large
sporadic carriers. It is an unconditional reduction of the original local
configuration, not their remaining embedding classification.
Source: Aschbacher–Smith A.3.6, A.3.12 and 8.2.13, pp.43–48,722–723.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
open Chapter1.Section02.LocalModels ClassificationModels
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The explicit ordinary carriers not yet excluded by this sieve. -/
@[expose] def RemainingModel (H : Type*) [Group H] : Prop :=
  (∃ (p : ℕ) (unitary : Bool), p.Prime ∧ Odd p ∧
    (IsPSLSign H unitary 3 p ∨ IsSLSign H unitary 3 p)) ∨
  (∃ name : SporadicName,
    (name = .m24 ∨ name = .j4 ∨ name = .hs ∨ name = .he ∨ name = .ru) ∧
    Nonempty (H ≃* name.Carrier))

private theorem core_ne_bot {B : Type*} [Group B]
    (h : Nat.card (pCore 2 B) = 32) : pCore 2 B ≠ ⊥ := by
  intro he
  rw [he, card_bot] at h
  omega

omit [Finite G] in
private theorem local_perfect {T B : Subgroup G} (hB : B ∈ localCComponents T) :
    Group.IsPerfect B := by
  let := hB.perfect
  let e := subgroupOfEquivOfLe (show B ≤ B ⊔ T from le_sup_left)
  exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

private theorem threeRank {B : Type*} [Group B] [Finite B]
    (h : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    primeRank 3 B = 2 := by
  obtain ⟨e⟩ := h
  rw [← primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 B) pCore_isPGroup,
    primeRank_congr 3 e,
    GLS3.Chapter5.PRank.alternating_primeRank_of_odd_prime 6 3 (by decide) (by decide)]

private theorem not_of_equiv {H : Type*} [Group H] [Finite H]
    (a : G ≃* H)
    (hH : ∀ (S : Sylow 2 H) (B : Subgroup H), B ∈ localCComponents S →
      B ≠ ⊤ → Nat.card (pCore 2 B) = 32 →
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) → False)
    (S : Sylow 2 G) (B : Subgroup G) (hB : B ∈ localCComponents S)
    (hproper : B ≠ ⊤) (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) : False := by
  let : Group.IsSolvable a.toMonoidHom.ker := by
    rw [(MonoidHom.ker_eq_bot_iff _).mpr a.injective]
    infer_instance
  let d := B.equivMapOfInjective a.toMonoidHom a.injective
  let dq := QuotientGroup.congr _ _ d (pCore_map_iso 2 d)
  apply hH (S.mapSurjective (f := a.toMonoidHom) a.surjective)
    (B.map a.toMonoidHom)
    (Chapter1.Section02.localCComponents_map_of_solvable_ker hB a.toMonoidHom)
  · intro he
    apply hproper
    apply map_injective (f := a.toMonoidHom) a.injective
    rw [he, map_top_of_surjective _ a.surjective]
  · rw [← pCore_map_iso 2 d, card_map_of_injective d.injective, hcore]
  · obtain ⟨e⟩ := hA6
    exact ⟨dq.symm.trans e⟩

omit [Finite G] in
private theorem embedded_core {H : Type*} [Group H] (e : G ≃* H)
    (B : Subgroup G) (hcore : pCore 2 B ≠ ⊥) :
    ∃ R : Subgroup H, R ≠ ⊥ ∧ IsPGroup 2 R ∧
      B.map e.toMonoidHom ≤ normalizer (R : Set H) := by
  let R := (pCore 2 B).map B.subtype
  have hR : R ≠ ⊥ := fun h => hcore
    ((map_eq_bot_iff_of_injective (pCore 2 B) B.subtype_injective).mp h)
  refine ⟨R.map e.toMonoidHom, ?_, (pCore_isPGroup.map B.subtype).map e.toMonoidHom, ?_⟩
  · exact fun h => hR ((map_eq_bot_iff_of_injective R (f := e.toMonoidHom) e.injective).mp h)
  · exact (map_mono (B.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image B (pCore 2 B)))).trans
      (le_normalizer_map e.toMonoidHom)

private theorem not_triality (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)))
    {n : ℕ} (hn : 1 ≤ n) (hm : Triality.Standard.IsTrialityGroupAt (2 ^ n) G) : False := by
  let hn' : 0 < n := by omega
  obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff G n hn').mp hm
  obtain ⟨R,hR,hp,hBR⟩ := embedded_core e B (core_ne_bot hcore)
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
  rw [threeRank hA6] at hb
  omega

private theorem not_fifteen_free {H : Type*} [Group H] [Finite H] (e : G ≃* H)
    (hH : ∀ R : Subgroup H, R ≠ ⊥ → IsPGroup 2 R →
      ¬ 15 ∣ Nat.card (normalizer (R : Set H)))
    (B : Subgroup G) (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) : False := by
  obtain ⟨R,hR,hp,hBR⟩ := embedded_core e B (core_ne_bot hcore)
  apply hH R hR hp
  have hd := card_dvd_of_le hBR
  rw [card_map_of_injective e.injective, card_of_shape hcore hA6] at hd
  exact (by decide : 15 ∣ 11520).trans hd

/-- All actual characteristic-two rank-two containing carriers are excluded. -/
theorem not_rankTwo (S : Sylow 2 G) (B : Subgroup G)
    (hB : B ∈ localCComponents S) (hproper : B ≠ ⊤)
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)))
    (hm : RankTwoTheoremC G) : False := by
  have hd : 11520 ∣ Nat.card G := by
    rw [← card_of_shape hcore hA6]
    exact B.card_subgroup_dvd_card
  cases hm with
  | linear n hn hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      apply not_of_equiv e ?_ S B hB hproper hcore hA6
      intro S B hB hp _ ha
      exact SixLocalFF.not_linear_three_all hF S B hB hp ha.some
  | symplectic n hn hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card hF
      let a := e.trans (Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv (F := F)).symm
      apply not_of_equiv a ?_ S B hB hproper hcore hA6
      intro S B hB hp _ ha
      exact SixLocalFF.not_symplectic hF (by omega) S B hB hp ha.some
  | g2 n hn hm =>
      obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
      let : Fintype F := Fintype.ofFinite F
      let : CharP F 2 := charP_of_card_eq_prime_pow
        (by simpa only [Nat.card_eq_fintype_card] using hF)
      have hq : 2 < Nat.card F := by
        rw [hF]
        have hh := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hn
        norm_num at hh
        omega
      apply not_of_equiv e ?_ S B hB hproper hcore hA6
      intro S B hB hp _ ha
      exact SixLocalFF.not_g2 hq S B hB hp ha.some
  | triality n hn hm => exact not_triality S B hB hcore hA6 hn hm
  | ree m hm he =>
      obtain ⟨d, ⟨e⟩⟩ := he
      exact not_fifteen_free (e.trans d.modelEquiv)
        (ReeF4.ConverseParabolics.normalizer_fifteen_free hm) B hcore hA6
  | symplectic_derived he =>
      rw [Nat.card_congr (he.some.trans
        Theory.SpecificGroups.SymplecticFour.Binary.projectiveDerivedEquivAlternatingSix).toEquiv,
        nat_card_alternatingGroup] at hd
      norm_num at hd
  | g2_derived he =>
      rw [Nat.card_congr he.some.toEquiv,
        Atlas.G2.DerivedEvenOrder.card_derived_binary (by simp)] at hd
      norm_num at hd
  | tits he => exact not_fifteen_free he.some Tits.normalizer_fifteen_free B hcore hA6

omit [Finite G] in
private theorem sporadic_remaining {name : SporadicName}
    (hne : name ≠ .j3) (he : Nonempty (G ≃* name.Carrier))
    (hd : 11520 ∣ Nat.card G) : RemainingModel G := by
  right
  refine ⟨name, ?_, he⟩
  obtain ⟨e⟩ := he
  cases name with
  | m11 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 11520 ∣ Nat.card Sporadic.Mathieu.M11 at hd
      rw [Sporadic.Mathieu.m11_order] at hd
      norm_num at hd
  | m12 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 11520 ∣ Nat.card Sporadic.Mathieu.M12 at hd
      rw [Sporadic.Mathieu.m12_order] at hd
      norm_num at hd
  | m22 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 11520 ∣ Nat.card Sporadic.Mathieu.M22 at hd
      rw [Sporadic.Mathieu.m22_order] at hd
      norm_num at hd
  | m23 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 11520 ∣ Nat.card Sporadic.Mathieu.M23 at hd
      rw [Sporadic.Mathieu.m23_order] at hd
      norm_num at hd
  | j2 =>
      rw [Nat.card_congr e.toEquiv] at hd
      change 11520 ∣ Nat.card Sporadic.LeechRelated.J2.Carrier at hd
      rw [Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hd
      norm_num at hd
  | j3 => exact (hne rfl).elim
  | m24 => exact Or.inl rfl
  | j4 => exact Or.inr (Or.inl rfl)
  | hs => exact Or.inr (Or.inr (Or.inl rfl))
  | he => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  | ru => exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

/-- The simple-carrier sieve uses the original ambient local component and
Sylow; only odd ternary and five large sporadic containing models remain. -/
theorem simple_models_remaining
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)))
    (hm : TheoremCModel K) : RemainingModel K := by
  have hd : 11520 ∣ Nat.card K := by
    rw [← card_of_shape hcore hA6]
    exact card_dvd_of_le hBK.le
  obtain ⟨S, _, hl, _, hp, hc, ha⟩ := source_sylow_restriction T hB hK hBK hTB hcore hA6
  cases hm with
  | alternating n hn he =>
      obtain ⟨e⟩ := he
      have hn5 := hn.1
      have hn8 := hn.2
      interval_cases n <;>
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup] at hd <;> norm_num at hd
  | linear_odd p k hp ho hk hs he =>
      exfalso
      rcases hk with rfl | rfl
      · exact not_a312_embedding hBK hcore hA6
          (embedding_of_primePSL2 T hB hK hBK.le hp ho (by simpa using he))
      · exact not_a312_embedding hBK hcore hA6
          (embedding_of_quadraticPSL2 T hB hK hBK.le hp ho he)
  | three_odd p hp ho unitary he => exact Or.inl ⟨p,unitary,hp,ho,Or.inl he⟩
  | rank_one he => exact (hBK.ne (eq_of_bender_containing_component T hB hK hBK.le he)).elim
  | rank_two he => exact (not_rankTwo S (B.subgroupOf K) hl hp hc ha he).elim
  | binary_linear d hd he =>
      exact (SixLocalFF.BinaryLinear.not_section_binary_linear S (B.subgroupOf K) hl ha.some hd he).elim
  | sporadic name hne he => exact sporadic_remaining hne he hd
  | janko_one he =>
      rw [Nat.card_congr he.some.toEquiv, Janko1.card_model] at hd
      norm_num at hd

private theorem card_threeCover {H : Type*} [Group H] {J : Type} [Group J]
    (h : IsThreeCover H J) : Nat.card H = Nat.card J * 3 := by
  obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := h
  rw [card_eq_card_quotient_mul_card_subgroup (center H),
    Nat.card_congr eq.toEquiv, Nat.card_congr ez.toEquiv]
  simp

/-- The triple-cover carriers give only the special odd ternary part of
the same residual list. The actual classical covering groups are retained. -/
theorem cover_models_remaining
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)))
    (hm : ThreeCoverModel K) : RemainingModel K := by
  have hd : 11520 ∣ Nat.card K := by
    rw [← card_of_shape hcore hA6]
    exact card_dvd_of_le hBK.le
  obtain ⟨S, _, hl, _, hp, hc, ha⟩ := source_sylow_restriction T hB hK hBK hTB hcore hA6
  cases hm with
  | classical unitary q hq hm =>
      rcases hq with ⟨n,hn,rfl,_⟩ | ⟨hq,ho⟩
      · exfalso
        cases unitary with
        | false =>
            obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hm
            let : Fintype F := Fintype.ofFinite F
            let : CharP F 2 := charP_of_card_eq_prime_pow
              (by simpa only [Nat.card_eq_fintype_card] using hF)
            apply not_of_equiv e ?_ S (B.subgroupOf K) hl hp hc ha
            intro S B hB hp _ ha
            exact SixLocalFF.not_special_linear_three hF S B hB hp ha.some
        | true =>
            exact hBK.ne (eq_of_binary_su3_containing_component T hB hK hBK.le (by omega) hm)
      · exact Or.inl ⟨q,unitary,hq,ho,Or.inr hm⟩
  | alternating_six he =>
      rw [card_threeCover he, nat_card_alternatingGroup] at hd
      norm_num at hd
  | alternating_seven he =>
      rw [card_threeCover he, nat_card_alternatingGroup] at hd
      norm_num at hd
  | mathieu he =>
      rw [card_threeCover he, Sporadic.Mathieu.m22_order] at hd
      norm_num at hd

/-- The actual core-free SQTK source configuration has one of the explicit
remaining ordinary models, without an A.3.12 or local-classification callback. -/
theorem ordinary_models_remaining
    (hG : IsSQTK KnownSimple.IsKnownSimple G) (hO : pCore 2 G = ⊥)
    (T : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents T) (hK : K.IsCComponent) (hBK : B < K)
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hcore : Nat.card (pCore 2 B) = 32)
    (hA6 : Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6))) :
    RemainingModel K := by
  obtain ⟨_, hm | hm⟩ := containing_models_knownSimple hG hO T hB hK hBK hcore hA6
  · exact simple_models_remaining T hB hK hBK hTB hcore hA6 hm.2
  · exact cover_models_remaining T hB hK hBK hTB hcore hA6 hm.2

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.Order32Six
