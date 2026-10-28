module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleRecognitionNaturalContainedConjugateFieldGeometryQuotient
public import Theory.GroupTheory.PrimePowerCosetReplacement
public import Theory.GroupTheory.TINormalizerControl

/-!
# Arranging the involutory field witness

The original field witness may have order greater than two. Its odd-power
two-primary part preserves both the actual module action and the marked
quotient action. Choose a Sylow subgroup of N_M(U) above that actor and B;
the TI property puts this subgroup in N_G(B), where it extends to an
ambient Sylow. Its intersection with N_G(U) is the chosen local Sylow.

This proves the initial Sylow arrangement in source 6.1.14, printed
pp.670–671. Promotion to the full normalizer remains a separate step.
-/

public section

open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces
universe u
variable {G : Type u} [Group G] {L B : Subgroup G}
  {F : Type} [Field F]

private noncomputable def quotientActorHom
    (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F) :
    normalizer (L : Set G) →* MulAut (Matrix.SpecialLinearGroup (Fin 2) F) where
  toFun := quotientActor e
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨q, rfl⟩ := e.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    rw [quotientActor_mk]
    simp
  map_mul' t s := by
    apply MulEquiv.ext
    intro x
    obtain ⟨q, rfl⟩ := e.surjective x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 L) q
    change quotientActor e (t * s) _ = quotientActor e t (quotientActor e s _)
    rw [quotientActor_mk, quotientActor_mk, quotientActor_mk, map_mul]
    rfl

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition.ConjugateFixedSpaces

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open ConjugateFixedSpaces Representation.SL2NaturalOffenders.FixedField
universe u
variable {G : Type u} [Group G] [Finite G] {L M B U : Subgroup G} {n : ℕ}

/-- The field witness can be chosen to have two-power order, with the same
fixed subgroup and the same literal quotient action. -/
theorem field_fixedSpace_two_primary_witness
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) :
    ∃ t : normalizer (L : Set G),
      (t : G) ∈ M ∧ (t : G) ∈ normalizer (B : Set G) ∧
      (∃ k : ℕ, (t : G) ^ (2 ^ k) = 1) ∧
      U = B ⊓ centralizer ({(t : G)} : Set G) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 2 ^ n ∧
        ∃ (e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F)
          (σ : F ≃+* F), σ ≠ 1 ∧ σ ^ 2 = 1 ∧
          ∀ l : L,
            e (QuotientGroup.mk' (pCore 2 L) (L.normalizerMonoidHom t l)) =
              Theory.PSL2.sl2FieldAut σ (e (QuotientGroup.mk' (pCore 2 L) l)) := by
  obtain ⟨F, _, _, _, _, e, f, hf⟩ := hnatural
  let : Algebra (ZMod 2) F := ZMod.algebra F 2
  obtain ⟨t, htM, htB, hU, K, _, _, _, hK, a, σ, hσ, hσsq, hσact⟩ := hfield
  obtain ⟨hasq, _⟩ := field_quotientActor e a t σ hσ hσsq hσact
  have hi : Function.Involutive (vectorActor f ⟨t, htB⟩) := by
    apply intertwiner_involutive_of_fixed (quotientActor e t) _
      (vectorActor_intertwines e f hf t htB) hasq
    obtain ⟨u, hune⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hUne
    have hu := u.property
    let v : B := ⟨u, (hU.le hu).1⟩
    refine ⟨(f v).toAdd, ?_, ?_⟩
    · intro hz
      have hv : v = 1 := f.injective (by simpa using congrArg Multiplicative.ofAdd hz)
      exact hune (Subtype.ext (congrArg (fun b : B => (b : G)) hv))
    · apply (vectorActor_fixed_iff f ⟨t, htB⟩ _).mpr
      simpa [v] using (hU.le hu).2
  have hBsq : B.normalizerMonoidHom ⟨t, htB⟩ ^ 2 = 1 := by
    apply MulEquiv.ext
    intro b
    have hh := hi (f b).toAdd
    apply Subtype.ext
    have hh' := congrArg (fun v => (f.symm (Multiplicative.ofAdd v) : G)) hh
    rw [vectorActor_coe, vectorActor_coe] at hh'
    change (t : G) * ((t : G) * (b : G) * (t : G)⁻¹) * (t : G)⁻¹ = b
    simpa only [ofAdd_toAdd, f.symm_apply_apply] using hh'
  obtain ⟨k, m, hm, ho⟩ := exists_primary_power 2 Nat.prime_two t
  have heq : quotientActor a (t ^ m) = quotientActor a t := by
    change quotientActorHom a (t ^ m) = quotientActorHom a t
    rw [map_pow]
    change quotientActor a t ^ m = quotientActor a t
    obtain ⟨j, hj⟩ := hm.odd_of_left
    rw [hj, pow_add, pow_one, pow_mul,
      (field_quotientActor a a t σ hσ hσsq hσact).1, one_pow, one_mul]
  have hBeq : B.normalizerMonoidHom ⟨(t ^ m : normalizer (L : Set G)),
        (normalizer (B : Set G)).pow_mem htB m⟩ = B.normalizerMonoidHom ⟨t, htB⟩ := by
    change B.normalizerMonoidHom ((⟨t, htB⟩ : normalizer (B : Set G)) ^ m) = _
    rw [map_pow]
    obtain ⟨j, hj⟩ := hm.odd_of_left
    rw [hj, pow_add, pow_one, pow_mul, hBsq, one_pow, one_mul]
  refine ⟨t ^ m, M.pow_mem htM m, (normalizer (B : Set G)).pow_mem htB m,
    ⟨k, ?_⟩, ?_, K, inferInstance, inferInstance, inferInstance, hK,
      a, σ, hσ, hσsq, ?_⟩
  · have hp : (t ^ m) ^ (2 ^ k) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    exact congrArg (fun s : normalizer (L : Set G) => (s : G)) hp
  · rw [hU]
    apply Subgroup.ext
    intro b
    change (b ∈ B ∧ b ∈ centralizer ({(t : G)} : Set G)) ↔
      (b ∈ B ∧ b ∈ centralizer ({(↑(t ^ m) : G)} : Set G))
    constructor <;> rintro ⟨hb, hc⟩ <;> refine ⟨hb, ?_⟩
    all_goals
      have hh := congrArg (fun z : MulAut B => (z ⟨b, hb⟩ : G)) hBeq
      change (t : G) ^ m * b * ((t : G) ^ m)⁻¹ = (t : G) * b * (t : G)⁻¹ at hh
      rw [mem_centralizer_singleton_iff] at hc ⊢
    · exact (mul_inv_eq_iff_eq_mul.mp (hh.trans (by rw [← hc, mul_inv_cancel_right]))).symm
    · change b * (t : G) ^ m = (t : G) ^ m * b at hc
      exact (mul_inv_eq_iff_eq_mul.mp (hh.symm.trans (by rw [← hc, mul_inv_cancel_right]))).symm
  · intro l
    rw [← quotientActor_mk, heq, quotientActor_mk]
    exact hσact l
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition

namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
universe u
variable {G : Type u} [Group G] [Finite G]

/-- A subgroup containing an ambient Sylow contains an ambient Sylow above
every one of its two-subgroups. -/
private theorem exists_sylow_between (T : Sylow 2 G) (H Q : Subgroup G)
    (hTH : (T : Subgroup G) ≤ H) (hQH : Q ≤ H) (hQ : IsPGroup 2 Q) :
    ∃ P : Sylow 2 G, Q ≤ P ∧ (P : Subgroup G) ≤ H := by
  obtain ⟨S, hS⟩ := (hQ.comap_subtype (K := H)).exists_le_sylow
  let Q' := (S : Subgroup H).map H.subtype
  have hp : IsPGroup 2 Q' := S.isPGroup'.map H.subtype
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have hc : Nat.card Q' = Nat.card (T : Subgroup G) := by
    rw [card_map_of_injective H.subtype_injective]
    exact (Nat.card_congr (S.equiv (T.subtype hTH)).toEquiv).trans
      (Nat.card_congr (subgroupOfEquivOfLe hTH).toEquiv)
  have he : Q' = (P : Subgroup G) := Subgroup.eq_of_le_of_card_ge hP (by
    rw [hc]
    exact le_of_eq (Nat.card_congr (P.equiv T).toEquiv))
  refine ⟨P, ?_, ?_⟩
  · rw [← he]
    have hh := map_mono (f := H.subtype) hS
    change (Q.subgroupOf H).map H.subtype ≤ Q' at hh
    simpa only [subgroupOf_map_subtype, inf_of_le_left hQH] using hh
  · rw [← he]
    exact map_subtype_le _


/-- A two-element witness is placed in an ambient Sylow which normalizes B
and whose U-normalizer is already Sylow in N_M(U). -/
theorem field_fixedSpace_sylow_arrangement
    (T : Sylow 2 G) (L M B U : Subgroup G) (n : ℕ)
    [IsElementaryAbelian 2 B]
    (hTB : (T : Subgroup G) ≤ normalizer (B : Set G))
    (hBM : normalizer (B : Set G) ≤ M)
    (hML : M ≤ normalizer (L : Set G))
    (hTI : ∀ g ∈ M, B ⊓ B.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      B.map (MulAut.conj g).toMonoidHom = B)
    (hnatural : IsNaturalModule L B n)
    (hfield : IsInvolutoryFieldFixedSpace L M B U n) (hUne : U ≠ ⊥) :
    ∃ P : Sylow 2 G,
      (P : Subgroup G) ≤ M ∧ B ≤ P ∧
      (P : Subgroup G) ≤ normalizer (L : Set G) ∧
      (P : Subgroup G) ≤ normalizer (B : Set G) ∧
      IsInvolutoryFieldFixedSpace L (P : Subgroup G) B U n ∧
      ∃ R : Sylow 2 (M ⊓ normalizer (U : Set G) : Subgroup G),
        (R : Subgroup (M ⊓ normalizer (U : Set G) : Subgroup G)).map
          (M ⊓ normalizer (U : Set G)).subtype =
            (P : Subgroup G) ⊓ normalizer (U : Set G) := by
  obtain ⟨t, htM, htB, ⟨k, htp⟩, hU, F, _, _, _, hF, e, σ, hσ, hs, he⟩ :=
    field_fixedSpace_two_primary_witness hnatural hfield hUne
  have hUB : U ≤ B := hU.le.trans inf_le_left
  have hBC : B ≤ centralizer (U : Set G) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hUB)
  have htU : (t : G) ∈ centralizer (U : Set G) := by
    intro u hu
    exact mem_centralizer_singleton_iff.mp ((hU.le hu).2)
  let H := M ⊓ normalizer (U : Set G)
  have hBH : B ≤ H := le_inf (B.le_normalizer.trans hBM)
    (hBC.trans (Subgroup.centralizer_le_normalizer _))
  have htH : (t : G) ∈ H := ⟨htM, Subgroup.centralizer_le_normalizer _ htU⟩
  have hp : IsPGroup 2 (zpowers (t : G)) := IsPGroup.of_card_dvd_pow (by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one htp)
  let Q := B ⊔ zpowers (t : G)
  have hQ : IsPGroup 2 Q :=
    (IsElementaryAbelian.isPGroup (p := 2) (G := B)).to_sup_of_normal_left' hp
      (zpowers_le.mpr htB)
  have hQH : Q ≤ H := sup_le hBH (zpowers_le.mpr htH)
  obtain ⟨R, hQR⟩ := (hQ.comap_subtype (K := H)).exists_le_sylow
  let R' := (R : Subgroup H).map H.subtype
  have hQR' : Q ≤ R' := by
    have hh := map_mono (f := H.subtype) hQR
    change (Q.subgroupOf H).map H.subtype ≤ R' at hh
    simpa only [subgroupOf_map_subtype, inf_of_le_left hQH] using hh
  have hHN : H ≤ normalizer (B : Set G) :=
    inf_normalizer_le_of_trivial_intersections hTI hUne hUB
  obtain ⟨P, hRP, hPN⟩ := exists_sylow_between T (normalizer (B : Set G)) R' hTB
    ((map_subtype_le _).trans hHN) (R.isPGroup'.map H.subtype)
  have hPM := hPN.trans hBM
  refine ⟨P, hPM, (le_sup_left.trans hQR').trans hRP, hPM.trans hML, hPN,
    ⟨t, hRP (hQR' (mem_sup_right (mem_zpowers _))), htB, hU,
      F, inferInstance, inferInstance, inferInstance, hF, e, σ, hσ, hs, he⟩, R, ?_⟩
  have hle : R' ≤ (P : Subgroup G) ⊓ normalizer (U : Set G) :=
    le_inf hRP ((map_subtype_le _).trans inf_le_right)
  have hPH : (P : Subgroup G) ⊓ normalizer (U : Set G) ≤ H :=
    inf_le_inf_right _ hPM
  have hpP := (P.isPGroup'.to_le
    (show (P : Subgroup G) ⊓ normalizer (U : Set G) ≤ P from inf_le_left)).comap_subtype (K := H)
  have hrle : (R : Subgroup H) ≤
      ((P : Subgroup G) ⊓ normalizer (U : Set G)).subgroupOf H := by
    intro r hr
    exact hle (mem_map_of_mem H.subtype hr)
  have hmax := R.is_maximal' hpP hrle
  have hh := congrArg (map H.subtype) hmax
  change (((P : Subgroup G) ⊓ normalizer (U : Set G)).subgroupOf H).map H.subtype = R' at hh
  simpa only [subgroupOf_map_subtype, inf_of_le_left hPH] using hh.symm
end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
