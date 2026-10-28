module
public import Theory.SpecificGroups.SmallRankTwoPointMotion.CentralCover
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.SymmetricThreeTwoCoreStructure

/-!
# Point stabilizers in cubic sign extensions of S₆

The two S₆ parabolics have odd central involutions in their common Sylow
subgroup. For a cubic sign extension, two generating solvable local groups
of Sylow index three map injectively onto these parabolics. The central
involutions then show that a point stabilizer avoiding both local groups
also avoids both parabolics downstairs. Its image is Sylow, and trivial
intersection with the cubic kernel gives the same result upstairs.

A normal subgroup of prime order meeting a point stabilizer nontrivially
fixes its full conjugate span. This supplies the trivial-intersection premise
on a faithful full-span quotient, without treating the sign kernel as central.
Consumer: Aschbacher--Smith 13.2.12, printed p.882.
-/

public section

open Subgroup Theory.GroupTheory
namespace Theory.SpecificGroups.SmallRankTwoPointMotion.CubicSymmetric
open SymmetricSix
local instance : Fintype S6 := fintypePerm

set_option maxRecDepth 100000 in
private theorem duad_central_swap :
    ∀ a : S6, a ∈ duadStabilizer →
      a * Equiv.swap 0 1 = Equiv.swap 0 1 * a := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem syntheme_central_swap :
    ∀ a : S6, a ∈ synthemeStabilizer →
      a * (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5) =
        (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5) * a := by
  decide +kernel

/-- A proper strict Sylow overgroup in S₆ has an odd central involution
in the original Sylow subgroup. -/
theorem odd_central_involution (S : Sylow 2 S6) (A : Subgroup S6)
    (hSA : (S : Subgroup S6) < A) (hA : A ≠ ⊤) :
    ∃ z ∈ (S : Subgroup S6), Equiv.Perm.sign z = -1 ∧ z ^ 2 = 1 ∧
      ∀ a ∈ A, a * z = z * a := by
  obtain ⟨g,hg,hcover⟩ := coatoms_over_sylow S
  let e := MulAut.conj g
  obtain ⟨P,hP,hAP⟩ := (eq_top_or_exists_le_coatom A).resolve_left hA
  have hp := (hcover P).mp ⟨hP,hSA.le.trans hAP⟩
  have base (Q : Subgroup S6) (z : S6) (hz : z ∈ SymmetricSix.borel)
      (hs : Equiv.Perm.sign z = -1) (h2 : z ^ 2 = 1)
      (hc : ∀ a ∈ Q, a*z=z*a) (hPQ : P = Q.map e.toMonoidHom) :
      ∃ z ∈ (S : Subgroup S6), Equiv.Perm.sign z = -1 ∧ z ^ 2 = 1 ∧
        ∀ a ∈ A, a*z=z*a := by
    refine ⟨e z, hg ▸ mem_map_of_mem e.toMonoidHom hz, ?_, ?_, ?_⟩
    · simp only [e,MulAut.conj_apply,map_mul,map_inv,hs]
      simp [mul_comm]
    · rw [←map_pow,h2,map_one]
    · intro a ha
      obtain ⟨b,hb,rfl⟩ := hPQ ▸ hAP ha
      change e b * e z = e z * e b
      simpa only [map_mul] using congrArg e (hc b hb)
  rcases hp with hp | hp
  · exact base duadStabilizer (Equiv.swap 0 1) (by decide +kernel)
      (Equiv.Perm.sign_swap (by decide)) (by decide +kernel) duad_central_swap hp
  · exact base synthemeStabilizer
      (Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) syntheme_central_swap hp
end Theory.SpecificGroups.SmallRankTwoPointMotion.CubicSymmetric

namespace Theory.SpecificGroups.SmallRankTwoPointMotion.CubicSymmetric
variable {D : Type*} [Group D] [Finite D]

/-- Prime normal kernels meet a full-span point stabilizer trivially. -/
theorem centralizer_seed_image_inf_cubic_eq_bot
    {J : Type*} [Group J] (x : J) (f : J →* D) (hf : Function.Surjective f)
    (hk : f.ker = centralizer (conjugateSpanBy (zpowers x) ⊤ : Set J))
    (K : Subgroup D) [K.Normal] (hK : Nat.card K = 3) :
    (centralizer ({x} : Set J)).map f ⊓ K = ⊥ := by
  let C := centralizer ({x} : Set J)
  let N := C.map f ⊓ K
  have hd : Nat.card N ∣ 3 := hK ▸ card_dvd_of_le (show N ≤ K from inf_le_right)
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with hn | hn
  · exact N.eq_bot_iff_card.mpr hn
  have he : N = K := eq_of_le_of_card_ge inf_le_right (by omega)
  have hker : f.ker ≤ C := by
    rw [hk]
    exact centralizer_le (Set.singleton_subset_iff.mpr
      (le_conjugateSpanBy _ _ (mem_zpowers x)))
  have hnC : K.comap f ≤ C := by
    have hh := comap_mono (f := f) (show K ≤ C.map f from he ▸ inf_le_left)
    rwa [comap_map_eq_self hker] at hh
  have hspan : K.comap f ≤ centralizer (conjugateSpanBy (zpowers x) ⊤ : Set J) := by
    apply le_centralizer_conjugateSpanBy_of_normalizes _ _ _ le_normalizer_of_normal
    simpa only [zpowers_eq_closure,centralizer_closure] using hnC
  rw [←hk] at hspan
  have hh := map_mono (f := f) hspan
  rw [map_comap_eq_self_of_surjective hf,map_ker_self] at hh
  exact le_bot_iff.mp (inf_le_right.trans hh)

omit [Finite D] in
private theorem injective_on_of_inf_ker_eq_bot {Q : Type*} [Group Q]
    (q : D →* Q) (A : Subgroup D) (h : A ⊓ q.ker = ⊥) :
    Function.Injective (q.comp A.subtype) := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  apply bot_unique
  intro a ha
  exact Subtype.ext (mem_bot.mp (h ▸ (show (a:D) ∈ A ⊓ q.ker from ⟨a.property,ha⟩)))

/-- Both local index-three groups lift faithfully through a cubic sign kernel;
central odd involutions then lift point-stabilizer containment. -/
theorem cubic_symmetric_point_stabilizer
    (q : D →* Equiv.Perm (Fin 6)) (hq : Function.Surjective q)
    (hk : Nat.card q.ker = 3)
    (hinv : ∀ g : D, Equiv.Perm.sign (q g) = -1 →
      ∀ z ∈ q.ker, g*z*g⁻¹ = z⁻¹)
    (S : Sylow 2 D) (A B C : Subgroup D)
    (hSA : (S : Subgroup D) ≤ A) (hSB : (S : Subgroup D) ≤ B)
    (hgen : A ⊔ B = ⊤) (ha : Group.IsSolvable A) (hb : Group.IsSolvable B)
    (ea : (A ⧸ pCore 2 A) ≃* Equiv.Perm (Fin 3))
    (eb : (B ⧸ pCore 2 B) ≃* Equiv.Perm (Fin 3))
    (hSC : (S : Subgroup D) ≤ C) (hAC : ¬ A ≤ C) (hBC : ¬ B ≤ C)
    (hfaith : C ⊓ q.ker = ⊥) : C = (S : Subgroup D) := by
  let R := S.mapSurjective hq
  have hproper (P : Subgroup D) (hP : Group.IsSolvable P) : P.map q ≠ ⊤ := by
    let := hP
    intro ht
    have hs : Group.IsSolvable (Equiv.Perm (Fin 6)) := Group.isSolvable_of_surjective
      (f := q.comp P.subtype) (MonoidHom.range_eq_top.mp (by
        rwa [MonoidHom.range_comp,range_subtype]))
    let := hs
    let : Group.IsPerfect (alternatingGroup (Fin 6)) :=
      ⟨commutator_alternatingGroup_eq_top (by simp)⟩
    exact Group.IsPerfect.not_isSolvable (alternatingGroup (Fin 6)) inferInstance
  have hstrict (P Q : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
      (hSQ : (S : Subgroup D) ≤ Q) (hPQ : P ⊔ Q = ⊤)
      (hQ : Group.IsSolvable Q) : (R : Subgroup _) < P.map q := by
    apply lt_of_le_of_ne (map_mono hSP)
    intro he
    apply hproper Q hQ
    have hh : P.map q ≤ Q.map q := he ▸ map_mono hSQ
    rw [←sup_of_le_right hh,←Subgroup.map_sup,hPQ,map_top_of_surjective _ hq]
  have hRa := hstrict A B hSA hSB hgen hb
  have hRb := hstrict B A hSB hSA (sup_comm B A ▸ hgen) ha
  have hSi := injective_comp_subtype_of_coprime_ker q
    (by rw [hk]; decide : Nat.Coprime 2 (Nat.card q.ker)) (S : Subgroup D) S.isPGroup'
  have hSmap : Nat.card S = Nat.card R := Nat.card_congr
    (MulEquiv.ofBijective (q.subgroupMap (S : Subgroup D))
      ⟨fun _ _ h => hSi (congrArg Subtype.val h), q.subgroupMap_surjective _⟩).toEquiv
  have local_inj (P : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
      (eP : (P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3))
      (hRP : (R : Subgroup _) < P.map q) (hP : Group.IsSolvable P) :
      Function.Injective (q.comp P.subtype) := by
    have hi : (S : Subgroup D).relIndex P = 3 :=
      SymmetricThreeTwoCore.sylow_index_three eP (S.subtype hSP)
    have hi' := SymmetricSix.symmetric_sylow_parabolic_index R (P.map q) hRP (hproper P hP)
    have hcard : Nat.card P = Nat.card (P.map q) := by
      have h₁ := ((S : Subgroup D).subgroupOf P).index_mul_card
      have h₂ := ((R : Subgroup _).subgroupOf (P.map q)).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hSP).toEquiv] at h₁
      rw [Nat.card_congr (subgroupOfEquivOfLe hRP.le).toEquiv] at h₂
      change (S : Subgroup D).relIndex P * Nat.card (S : Subgroup D) = _ at h₁
      change (R : Subgroup (Equiv.Perm (Fin 6))).relIndex (P.map q) * Nat.card (R : Subgroup (Equiv.Perm (Fin 6))) = _ at h₂
      rw [hi,hSmap] at h₁
      rw [hi'] at h₂
      exact h₁.symm.trans h₂
    have hi := ((Nat.bijective_iff_surjective_and_card (q.subgroupMap P)).mpr
      ⟨q.subgroupMap_surjective P,hcard⟩).1
    intro x y h
    apply hi
    exact Subtype.ext h
  have hai := local_inj A hSA ea hRa ha
  have hbi := local_inj B hSB eb hRb hb
  have hci := injective_on_of_inf_ker_eq_bot q C hfaith
  have descent (P : Subgroup D) (hSP : (S : Subgroup D) ≤ P)
      (hPi : Function.Injective (q.comp P.subtype))
      (hRP : (R : Subgroup _) < P.map q) (hP : Group.IsSolvable P)
      (hPC : P.map q ≤ C.map q) : P ≤ C := by
    obtain ⟨w,hw,hwodd,_,hwcent⟩ := odd_central_involution R (P.map q) hRP (hproper P hP)
    obtain ⟨t,ht,rfl⟩ := hw
    have htP := hSP ht
    have htC := hSC ht
    have commP (a : D) (ha : a ∈ P) : a*t=t*a := by
      exact congrArg Subtype.val (hPi (show (q.comp P.subtype) (⟨a,ha⟩ * ⟨t,htP⟩) =
          (q.comp P.subtype) (⟨t,htP⟩ * ⟨a,ha⟩) from by
        change q (a*t) = q (t*a)
        simpa only [map_mul] using hwcent (q a) (mem_map_of_mem q ha)))
    intro a ha
    obtain ⟨c,hc,he⟩ := hPC (mem_map_of_mem q ha)
    have commC : c*t=t*c := by
      have hh := hwcent (q a) (mem_map_of_mem q ha)
      rw [←he] at hh
      exact congrArg Subtype.val (hci (show (q.comp C.subtype) (⟨c,hc⟩ * ⟨t,htC⟩) =
          (q.comp C.subtype) (⟨t,htC⟩ * ⟨c,hc⟩) from by
        change q (c*t) = q (t*c)
        simpa only [map_mul] using hh))
    have hk' : a*c⁻¹ ∈ q.ker := by
      change q (a*c⁻¹)=1
      rw [map_mul,map_inv,he,mul_inv_cancel]
    have hcomm : t * (a*c⁻¹) * t⁻¹ = a*c⁻¹ := by
      calc
        t * (a*c⁻¹) * t⁻¹ = (t*a*t⁻¹) * (t*c*t⁻¹)⁻¹ := by group
        _ = a*c⁻¹ := by rw [mul_inv_eq_iff_eq_mul.mpr (commP a ha).symm,
          mul_inv_eq_iff_eq_mul.mpr commC.symm]
    have hin := hinv t hwodd (a*c⁻¹) hk'
    have htwo : (a*c⁻¹)^2=1 := by
      rw [hcomm] at hin
      calc
        (a*c⁻¹)^2 = (a*c⁻¹) * (a*c⁻¹)⁻¹ := by simpa only [pow_two] using congrArg (fun z : D => (a*c⁻¹)*z) hin
        _ = 1 := mul_inv_cancel _
    have hthree : (a*c⁻¹)^3=1 := by
      have hh := pow_card_eq_one' (x := (⟨a*c⁻¹,hk'⟩ : q.ker))
      rw [hk] at hh
      exact congrArg Subtype.val hh
    have heq : a*c⁻¹=1 := by
      have hh : (a*c⁻¹)^3 = a*c⁻¹ := by rw [pow_succ,htwo,one_mul]
      exact hh.symm.trans hthree
    rwa [mul_inv_eq_one.mp heq]
  have hCimage := sylow_overgroup_eq_of_avoids_generators
    (Or.inr (Or.inr ⟨MulEquiv.refl _⟩)) R (A.map q) (B.map q) (C.map q)
    (map_mono hSA) (map_mono hSB)
    (by rw [←Subgroup.map_sup,hgen,map_top_of_surjective _ hq])
    (hproper A ha) (hproper B hb) (map_mono hSC)
    (fun h => hAC (descent A hSA hai hRa ha h))
    (fun h => hBC (descent B hSB hbi hRb hb h))
  apply le_antisymm ?_ hSC
  intro c hc
  obtain ⟨s,hs,he⟩ := hCimage.le (mem_map_of_mem q hc)
  have heq : (⟨s,hSC hs⟩ : C) = ⟨c,hc⟩ := hci he
  have hsc : s = c := congrArg Subtype.val heq
  rwa [←hsc]
end Theory.SpecificGroups.SmallRankTwoPointMotion.CubicSymmetric
