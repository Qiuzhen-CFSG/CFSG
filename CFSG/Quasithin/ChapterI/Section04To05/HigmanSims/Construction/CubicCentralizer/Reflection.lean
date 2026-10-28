module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.LocalOrder
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.NormalizerSixteenPointStabilizer
public import Theory.GroupAction.PrimeOrderConjugation
import all CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.CubicCentralizer.FixedCore

/-!
# An actual reflection in the original cubic centralizer

The point stabilizer of the constructed pure sixteen has index ten in the
original involution centralizer. A cubic therefore normalizes a conjugate
of that sixteen. The cubic norm of its known reflection is still an
involution, centralizes the cubic, and inverts the original central cyclic
four. All conjugation transports retain the original ambient point core.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.HigmanSims
variable {G : Type*} [Group G] [Finite G] {z : G} {V : Subgroup G}

omit [Finite G] in
private theorem norm_reflection (A : Subgroup G) [IsElementaryAbelian 2 A]
    (s c a : G) (hsA : s ∈ normalizer (A : Set G)) (hs3 : s ^ 3 = 1)
    (hcs : Commute c s) (ha : a ∈ A) (hac : a * c * a⁻¹ = c⁻¹) :
    ∃ b ∈ A, b ^ 2 = 1 ∧ Commute b s ∧ b * c * b⁻¹ = c⁻¹ := by
  let α : MulAut A := A.normalizerMonoidHom ⟨s, hsA⟩
  let aA : A := ⟨a, ha⟩
  let b : A := aA * α aA * α (α aA)
  have hα3 : α (α (α aA)) = aA := by
    apply Subtype.ext
    change s * (s * (s * a * s⁻¹) * s⁻¹) * s⁻¹ = a
    calc
      _ = s ^ 3 * a * (s ^ 3)⁻¹ := by simp only [pow_succ, pow_zero]; group
      _ = a := by rw [hs3]; simp
  have hfix : α b = b := by
    dsimp only [b]
    rw [map_mul, map_mul, hα3]
    ac_rfl
  have hinvert (x : G) (hx : x * c * x⁻¹ = c⁻¹) :
      (s * x * s⁻¹) * c * (s * x * s⁻¹)⁻¹ = c⁻¹ := by
    have hsc : s * c * s⁻¹ = c := by rw [hcs.eq.symm, mul_inv_cancel_right]
    have hh := congrArg (MulAut.conj s) hx
    simp only [map_mul, map_inv] at hh
    change (s * x * s⁻¹) * (s * c * s⁻¹) * (s * x * s⁻¹)⁻¹ =
      (s * c * s⁻¹)⁻¹ at hh
    rwa [hsc] at hh
  have h1 : (α aA : G) * c * (α aA : G)⁻¹ = c⁻¹ := hinvert a hac
  have h2 : (α (α aA) : G) * c * (α (α aA) : G)⁻¹ = c⁻¹ :=
    hinvert (α aA) h1
  have h1i : (α aA : G) * c⁻¹ * (α aA : G)⁻¹ = c := by
    have hh := congrArg Inv.inv h1
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using hh
  refine ⟨b, b.property, ?_, ?_, ?_⟩
  · exact elemPow_eq_one_of_isElementaryAbelian (A := A) (b : G) b.property
  · have hh := congrArg Subtype.val hfix
    change s * (b : G) * s⁻¹ = b at hh
    exact (mul_inv_eq_iff_eq_mul.mp hh).symm
  · change (a * (α aA : G) * (α (α aA) : G)) * c *
      (a * (α aA : G) * (α (α aA) : G))⁻¹ = c⁻¹
    calc
      _ = a * ((α aA : G) * ((α (α aA) : G) * c * (α (α aA) : G)⁻¹) *
          (α aA : G)⁻¹) * a⁻¹ := by group
      _ = c⁻¹ := by rw [h2, h1i, hac]

omit [Finite G] in
private theorem center_transport (u : G) (e : G ≃* G) (c : G)
    (hc : c ∈ (center ((involutionCentralizer u).pCoreIn 2)).map
      ((involutionCentralizer u).pCoreIn 2).subtype)
    (hQ : ((involutionCentralizer u).pCoreIn 2).map e.toMonoidHom =
      (involutionCentralizer (e u)).pCoreIn 2) :
    e c ∈ (center ((involutionCentralizer (e u)).pCoreIn 2)).map
      ((involutionCentralizer (e u)).pCoreIn 2).subtype := by
  obtain ⟨cQ, hcQ, rfl⟩ := hc
  have hec : e (cQ : G) ∈ (involutionCentralizer (e u)).pCoreIn 2 :=
    hQ ▸ mem_map_of_mem e.toMonoidHom cQ.property
  refine ⟨⟨e cQ, hec⟩, mem_center_iff.mpr ?_, rfl⟩
  intro q
  have hq : (q : G) ∈ ((involutionCentralizer u).pCoreIn 2).map e.toMonoidHom :=
    hQ.symm ▸ q.property
  obtain ⟨q0, hq0, heq⟩ := hq
  apply Subtype.ext
  change (q : G) * e cQ = e cQ * (q : G)
  change e q0 = (q : G) at heq
  rw [← heq, ← map_mul, ← map_mul]
  exact congrArg e (congrArg Subtype.val (mem_center_iff.mp hcQ ⟨q0, hq0⟩))

/-- Every specified cubic in the original point centralizer commutes with
an actual involution which inverts the original central cyclic four. -/
theorem TypeAt.cubic_point_centralizer_reflection (h : TypeAt z V) (t : G)
    (ht : t ∈ involutionCentralizer z) (ht3 : orderOf t = 3) :
    ∃ c b : G, orderOf c = 4 ∧ c ^ 2 = z ∧
      c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
        ((involutionCentralizer z).pCoreIn 2).subtype ∧
      Commute c t ∧ orderOf b = 2 ∧ b ∈ involutionCentralizer z ∧
      Commute b t ∧ b * c * b⁻¹ = c⁻¹ ∧
      b ∉ (involutionCentralizer z).pCoreIn 2 := by
  obtain ⟨u, c, a, E, huV, hu1, huT, _, _, _, hc4, hc2, hcZ,
    _, _, _, hac, _, hAe, hA16, _, _, _, _, _, hCA, _, _, _, _, hpure, _, hpoints, _⟩ :=
    h.exists_all_point_core_eights
  let A := E.val ⊔ zpowers a
  let := hAe
  have huA : u ∈ A := (show E.val ≤ A from le_sup_left) E.property.2.1
  have haA : a ∈ A := (show zpowers a ≤ A from le_sup_right) (mem_zpowers a)
  have hz1 : z ≠ 1 := by intro he; have hh := h.involution; simp [he] at hh
  obtain ⟨m, hm⟩ := h.seed_transitive (⟨u, huV⟩ : V) ⟨z, h.involution_mem_seed⟩
    (fun he => hu1 (congrArg Subtype.val he)) (fun he => hz1 (congrArg Subtype.val he))
  have hmu : (m : G) * u * (m : G)⁻¹ = z := congrArg Subtype.val hm
  let t0 := (MulAut.conj (m : G)).symm t
  have ht0 : t0 ∈ involutionCentralizer u := by
    apply mem_centralizer_singleton_iff.mpr
    apply (MulAut.conj (m : G)).injective
    simp only [map_mul]
    rw [show (MulAut.conj (m : G)) t0 = t from (MulAut.conj (m : G)).apply_symm_apply t]
    change t * ((m : G) * u * (m : G)⁻¹) = ((m : G) * u * (m : G)⁻¹) * t
    rw [hmu]
    exact mem_centralizer_singleton_iff.mp ht
  have ht03 : orderOf t0 = 3 := ((MulAut.conj (m : G)).symm.orderOf_eq t).trans ht3
  let H := involutionCentralizer u
  let N := (normalizer (A : Set G)).subgroupOf H
  have hN : Nat.card N = 768 := by
    rw [← card_subtype H N, subgroupOf_map_subtype]
    exact h.sixteen_normalizer_point_card A hA16 hCA hpure hpoints u huA hu1
  have hi : N.index = 10 := by
    have hh := N.card_mul_index
    rw [hN, show Nat.card H = 7680 from huT.centralizer_card] at hh
    omega
  obtain ⟨g, hg⟩ := Theory.GroupAction.exists_conjugate_mem_of_prime_order N
    (x := (⟨t0, ht0⟩ : H)) (by decide : Nat.Prime 3)
    ((orderOf_coe _).symm.trans ht03) (by rw [hi]; decide)
  let s : G := (g : G)⁻¹ * t0 * (g : G)
  have hsA : s ∈ normalizer (A : Set G) := hg
  have hsH : s ∈ H := H.mul_mem (H.mul_mem (H.inv_mem g.property) ht0) g.property
  have hs3 : orderOf s = 3 := by
    simpa only [s, MulAut.conj_apply, inv_inv] using
      ((MulAut.conj (g : G)⁻¹).orderOf_eq t0).trans ht03
  have hcs : Commute c s := cubic_central_four huT s c hsH hs3 hc4 hcZ
  obtain ⟨b, hbA, hb2, hbs, hbc⟩ := norm_reflection A s c a hsA
    (hs3 ▸ pow_orderOf_eq_one s) hcs haA hac
  let e := MulAut.conj ((m : G) * (g : G))
  have heu : e u = z := by
    have hgu : (g : G) * u * (g : G)⁻¹ = u := by
      rw [mem_centralizer_singleton_iff.mp g.property, mul_inv_cancel_right]
    change ((m : G) * (g : G)) * u * ((m : G) * (g : G))⁻¹ = z
    calc
      _ = (m : G) * ((g : G) * u * (g : G)⁻¹) * (m : G)⁻¹ := by group
      _ = z := by rw [hgu, hmu]
  have hes : e s = t := by
    change ((m : G) * (g : G)) * ((g : G)⁻¹ *
      ((m : G)⁻¹ * t * (m : G)) * (g : G)) * ((m : G) * (g : G))⁻¹ = t
    group
  have heZ : e c ∈ (center ((involutionCentralizer z).pCoreIn 2)).map
      ((involutionCentralizer z).pCoreIn 2).subtype := by
    have hh := center_transport u e c hcZ (pointCore_conjugate u ((m : G) * (g : G)))
    rwa [heu] at hh
  have hec4 : orderOf (e c) = 4 := (e.orderOf_eq c).trans hc4
  have hebc : e b * e c * (e b)⁻¹ = (e c)⁻¹ := by
    simpa only [map_mul, map_inv] using congrArg e hbc
  have hec2 : (e c) ^ 2 = z := by rw [← map_pow, hc2, heu]
  have hebH : e b ∈ involutionCentralizer z := by
    apply mem_centralizer_singleton_iff.mpr
    rw [← heu, ← map_mul, ← map_mul]
    exact congrArg e (congrArg Subtype.val
      (mul_comm' (⟨b, hbA⟩ : A) ⟨u, huA⟩))
  have hnc : ¬ Commute (e b) (e c) := by
    intro hh
    have he : e c = (e c)⁻¹ := by
      simpa only [hh.eq, mul_inv_cancel_right] using hebc
    have hc : (e c) ^ 2 = 1 := by
      calc
        (e c) ^ 2 = e c * (e c)⁻¹ := by rw [pow_two]; exact congrArg (e c * ·) he
        _ = 1 := mul_inv_cancel _
    have hd := orderOf_dvd_of_pow_eq_one hc
    rw [hec4] at hd
    norm_num at hd
  have heb2 : orderOf (e b) = 2 := orderOf_eq_prime (by rw [← map_pow, hb2, map_one])
    (fun he => hnc (he ▸ Commute.one_left _))
  refine ⟨e c, e b, hec4, hec2, heZ, ?_, heb2, hebH, ?_, hebc, ?_⟩
  · have hh : Commute (e c) (e s) := hcs.map e.toMonoidHom
    rwa [hes] at hh
  · have hh : Commute (e b) (e s) := hbs.map e.toMonoidHom
    rwa [hes] at hh
  · intro hbQ
    obtain ⟨cQ, hcQ, heq⟩ := heZ
    apply hnc
    rw [← heq]
    exact congrArg Subtype.val (mem_center_iff.mp hcQ ⟨e b, hbQ⟩)

end CFSG.Quasithin.HigmanSims
