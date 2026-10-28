module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.AdditionalFusion.Tables
public import Theory.GroupAction.FiveActionMinimalOrder

/-!
# The five-element argument on Held's second elementary subgroup

In the cross-fusion branch, the pi orbit under the actual normalizer of L₂
has one or five points. Its stabilizer has order 64, so a normalizer which
is not a two-group has order 320. An element of order five acts without
nonidentity fixed points on L₂. Counting its orbits in the mu fusion class
then forces mu to fuse with tau*lambda.

Source: D. Held, "A Characterization of some multiply transitive permutation
groups, I", Illinois J. Math. 13 (1969), Lemma 2.9, printed p.230.
-/

open Subgroup Equiv
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS.CrossBranch
open Coordinates

private def crossActor : Fin 4 → H := ![1, lam, mup, mup * lam]

private theorem crossActor_normalizes (i : Fin 4) :
    crossActor i ∈ normalizer (elementary 3 : Set H) := by
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := (mem_elementary 3 x).mp hx
    have ht : ∀ (j : Fin 4) (a : BaseCode), ∃ b : BaseCode,
        elementaryWord 3 b = crossActor j * elementaryWord 3 a * (crossActor j)⁻¹ := by
      decide +kernel
    exact (mem_elementary 3 _).mpr (ht i a)
  · rw [card_map_of_injective (MulAut.conj _).injective]

private theorem cross_conjugate : ∀ a : BaseCode, elementaryClass 3 a = 8 →
    ∃ i, crossActor i * (tau * lam * xi) * (crossActor i)⁻¹ = elementaryWord 3 a := by
  decide +kernel

private theorem pi_word : ∀ a : BaseCode, elementaryClass 3 a = 1 → elementaryWord 3 a = pi := by
  decide +kernel

private theorem selected_card : ∀ b : Bool,
    Fintype.card {a : BaseCode // elementaryClass 3 a = 1 ∨
      (elementaryClass 3 a = 8 ∧ b = true)} = if b then 5 else 1 := by
  decide +kernel

universe u
variable {G : Type u} [Group G] [Finite G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

private abbrev N := normalizer (ambientElementary D e 3 : Set G)
private noncomputable abbrev E := ambientElementary D e 3
private noncomputable def piPoint : E D e := ⟨D.z, z_mem_ambientElementary D e 3⟩

private noncomputable def wordEquiv : BaseCode ≃ E D e :=
  (Equiv.ofBijective _ (elementaryWord_bijective 3)).trans
    ((elementary 3).equivMapOfInjective (D.a10ModelEmbedding e)
      (D.a10ModelEmbedding_injective e)).toEquiv

private def inOrbit (x : G) : Prop := ∃ n : N D e, (n : G) * D.z * (n : G)⁻¹ = x

private theorem inOrbit_iff (x : E D e) :
    inOrbit D e (x : G) ↔ x ∈ MulAction.orbit (N D e) (piPoint D e) := by
  constructor
  · rintro ⟨n, hn⟩
    exact MulAction.mem_orbit_iff.mpr ⟨n, Subtype.ext hn⟩
  · intro hx
    obtain ⟨n, hn⟩ := MulAction.mem_orbit_iff.mp hx
    exact ⟨n, congrArg Subtype.val hn⟩

omit [Finite G] in
private theorem inOrbit_conj (g : N D e) (y : G) :
    inOrbit D e ((g : G) * y * (g : G)⁻¹) ↔ inOrbit D e y := by
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨g⁻¹ * n, ?_⟩
    change ((g : G)⁻¹ * (n : G)) * D.z * ((g : G)⁻¹ * (n : G))⁻¹ = y
    calc
      _ = (g : G)⁻¹ * ((n : G) * D.z * (n : G)⁻¹) * (g : G) := by group
      _ = y := by rw [hn]; group
  · rintro ⟨n, hn⟩
    refine ⟨g * n, ?_⟩
    change ((g : G) * (n : G)) * D.z * ((g : G) * (n : G))⁻¹ = _
    calc
      _ = (g : G) * ((n : G) * D.z * (n : G)⁻¹) * (g : G)⁻¹ := by group
      _ = _ := by rw [hn]

private theorem stabilizer_card :
    Nat.card (MulAction.stabilizer (N D e) (piPoint D e)) = 64 := by
  have hs : MulAction.stabilizer (N D e) (piPoint D e) =
      D.centralizer.subgroupOf (N D e) := by
    ext g
    rw [MulAction.mem_stabilizer_iff, Subtype.ext_iff]
    change (g : G) * D.z * (g : G)⁻¹ = D.z ↔ (g : G) ∈ D.centralizer
    rw [mul_inv_eq_iff_eq_mul, mem_centralizer_singleton_iff]
  rw [hs, ← inf_subgroupOf_right D.centralizer (N D e), Nat.card_congr (subgroupOfEquivOfLe (inf_le_right :
    D.centralizer ⊓ N D e ≤ N D e)).toEquiv]
  have hc := ambient_normalizer_intersection_card D e 3
  change Nat.card (normalizer (ambientElementary D e 3 : Set G) ⊓ D.centralizer : Subgroup G) = 64 at hc
  simpa only [inf_comm] using hc

private theorem normalizer_card : Nat.card (N D e) =
    64 * (MulAction.orbit (N D e) (piPoint D e)).ncard := by
  have h := (MulAction.stabilizer (N D e) (piPoint D e)).card_mul_index
  rw [stabilizer_card, MulAction.index_stabilizer] at h
  exact h.symm

variable
  (hmu : ¬ IsConj D.z (D.a10ModelEmbedding e mu))
  (htau : ¬ IsConj D.z (D.a10ModelEmbedding e tau))
  (hlam : ¬ IsConj D.z (D.a10ModelEmbedding e lam))
  (hpilam : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * lam)))
  (hxi : ¬ IsConj D.z (D.a10ModelEmbedding e xi))
  (hpiXi : ¬ IsConj D.z (D.a10ModelEmbedding e (pi * xi)))
  (hcross : IsConj D.z (D.a10ModelEmbedding e (tau * lam * xi)))

include hmu htau hlam hpilam hxi hpiXi hcross in
private theorem pi_fusion_iff (i : Fin 9) :
    IsConj D.z (D.a10ModelEmbedding e (localRepresentative i)) ↔ i = 1 ∨ i = 8 := by
  have hp := D.a10ModelEmbedding_central e
  fin_cases i
  · simp [localRepresentative, D.z_ne_one]
  · change IsConj D.z (D.a10ModelEmbedding e pi) ↔ _
    rw [hp]
    exact ⟨fun _ => Or.inl rfl, fun _ => IsConj.refl _⟩
  · simpa [localRepresentative] using hmu
  · simpa [localRepresentative] using htau
  · simpa [localRepresentative] using hlam
  · simpa [localRepresentative] using hpilam
  · simpa [localRepresentative] using hxi
  · simpa [localRepresentative] using hpiXi
  · simpa [localRepresentative] using hcross

include hmu htau hlam hpilam hxi hpiXi hcross in
private theorem orbit_words_iff (a : BaseCode) :
    inOrbit D e (D.a10ModelEmbedding e (elementaryWord 3 a)) ↔
      elementaryClass 3 a = 1 ∨ (elementaryClass 3 a = 8 ∧
        inOrbit D e (D.a10ModelEmbedding e (tau * lam * xi))) := by
  have hc := (D.a10ModelEmbedding e).map_isConj (elementaryWord_isConj 3 a)
  have hx (ha : elementaryClass 3 a = 8) :
      inOrbit D e (D.a10ModelEmbedding e (elementaryWord 3 a)) ↔
        inOrbit D e (D.a10ModelEmbedding e (tau * lam * xi)) := by
    obtain ⟨i, hi⟩ := cross_conjugate a ha
    let n : N D e := ⟨D.a10ModelEmbedding e (crossActor i),
      le_normalizer_map _ (mem_map_of_mem _ (crossActor_normalizes i))⟩
    rw [← hi]
    simpa only [map_mul, map_inv] using inOrbit_conj D e n
      (D.a10ModelEmbedding e (tau * lam * xi))
  constructor
  · intro h
    obtain ⟨n, hn⟩ := h
    have hf : IsConj D.z (D.a10ModelEmbedding e (localRepresentative (elementaryClass 3 a))) :=
      (isConj_iff.mpr ⟨(n : G), hn⟩).trans hc.symm
    rcases (pi_fusion_iff D e hmu htau hlam hpilam hxi hpiXi hcross _).mp hf with hp | hp
    · exact Or.inl hp
    · exact Or.inr ⟨hp, (hx hp).mp ⟨n, hn⟩⟩
  · rintro (ha | ⟨ha, hx'⟩)
    · rw [pi_word a ha]
      exact ⟨1, by simpa using (D.a10ModelEmbedding_central e).symm⟩
    · exact (hx ha).mpr hx'

include hmu htau hlam hpilam hxi hpiXi hcross in
private theorem pi_orbit_card :
    (MulAction.orbit (N D e) (piPoint D e)).ncard = 1 ∨
      (MulAction.orbit (N D e) (piPoint D e)).ncard = 5 := by
  classical
  let b := decide (inOrbit D e (D.a10ModelEmbedding e (tau * lam * xi)))
  have he : Nat.card {a : BaseCode // elementaryClass 3 a = 1 ∨
      (elementaryClass 3 a = 8 ∧ b = true)} =
      (MulAction.orbit (N D e) (piPoint D e)).ncard := by
    apply Nat.card_congr (Equiv.subtypeEquiv (wordEquiv D e) ?_)
    intro a
    rw [← inOrbit_iff]
    change _ ↔ inOrbit D e (D.a10ModelEmbedding e (elementaryWord 3 a))
    simpa only [b, decide_eq_true_eq] using
      (orbit_words_iff D e hmu htau hlam hpilam hxi hpiXi hcross a).symm
  rw [Nat.card_eq_fintype_card, selected_card] at he
  cases hb : b
  · exact Or.inl (by simpa [hb] using he.symm)
  · exact Or.inr (by simpa [hb] using he.symm)

include hmu htau hlam hpilam hxi hpiXi hcross in
/-- In the cross-fusion branch, a non-two normalizer of L₂ has order 320. -/
public theorem l2_normalizer_card
    (hN : ¬ IsPGroup 2 (normalizer (ambientElementary D e 3 : Set G))) :
    Nat.card (normalizer (ambientElementary D e 3 : Set G)) = 320 := by
  rcases pi_orbit_card D e hmu htau hlam hpilam hxi hpiXi hcross with h | h
  · have hc : Nat.card (N D e) = 2 ^ 6 := by rw [normalizer_card, h]; norm_num
    exact (hN (IsPGroup.of_card hc)).elim
  · rw [normalizer_card, h]

private def muSelected (b : Fin 3 → Bool) (a : BaseCode) : Prop :=
  elementaryClass 3 a = 2 ∨
    (elementaryClass 3 a = 5 ∧ b 0 = true) ∨
    (elementaryClass 3 a = 6 ∧ b 1 = true) ∨
    (elementaryClass 3 a = 7 ∧ b 2 = true)

private instance (b : Fin 3 → Bool) (a : BaseCode) : Decidable (muSelected b a) := by
  unfold muSelected
  infer_instance

private theorem muSelected_mod : ∀ b : Fin 3 → Bool,
    Fintype.card {a : BaseCode // muSelected b a} % 5 ≠ 0 := by decide +kernel

include hmu hcross in
private theorem mu_fused_card_not_dvd
    (hm : ¬ IsConj (D.a10ModelEmbedding e mu) (D.a10ModelEmbedding e (tau * lam))) :
    ¬ 5 ∣ Nat.card {x : E D e // IsConj (D.a10ModelEmbedding e mu) (x : G)} := by
  classical
  let f := D.a10ModelEmbedding e
  have hml : ¬ IsConj (f mu) (f lam) := by
    have ht : IsConj lam (tau * lam) := by
      have hh : taup * lam * taup⁻¹ = tau * lam := by decide +kernel
      exact isConj_iff.mpr ⟨taup, hh⟩
    exact fun h => hm (h.trans (f.map_isConj ht))
  have hm1 : ¬ IsConj (f mu) 1 := by
    intro h
    have hmu1 : mu ≠ 1 := by decide +kernel
    exact hmu1 ((D.a10ModelEmbedding_injective e)
      ((isConj_one_right.mp h.symm).trans (map_one f).symm))
  have hmp : ¬ IsConj (f mu) (f pi) := by
    rw [D.a10ModelEmbedding_central e]
    exact fun h => hmu h.symm
  have hmc : ¬ IsConj (f mu) (f (tau * lam * xi)) :=
    fun h => hmu (hcross.trans h.symm)
  let b : Fin 3 → Bool := ![decide (IsConj (f mu) (f (Coordinates.pi * lam))),
    decide (IsConj (f mu) (f xi)), decide (IsConj (f mu) (f (Coordinates.pi * xi)))]
  have hi (a : BaseCode) : IsConj (f mu) (f (elementaryWord 3 a)) ↔ muSelected b a := by
    have hc := f.map_isConj (elementaryWord_isConj 3 a)
    have he : IsConj (f mu) (f (elementaryWord 3 a)) ↔
        IsConj (f mu) (f (localRepresentative (elementaryClass 3 a))) :=
      ⟨fun h => h.trans hc.symm, fun h => h.trans hc⟩
    rw [he]
    have hnot : elementaryClass 3 a ≠ 3 := by
      have ht : ∀ a, elementaryClass 3 a ≠ 3 := by decide +kernel
      exact ht a
    unfold muSelected
    clear hc he
    have hself : IsConj (f mu) (f mu) := IsConj.refl _
    generalize elementaryClass 3 a = j at *
    fin_cases j <;> simp [localRepresentative, b] at * <;> assumption
  have he : Nat.card {a : BaseCode // muSelected b a} =
      Nat.card {x : E D e // IsConj (f mu) (x : G)} := by
    apply Nat.card_congr (Equiv.subtypeEquiv (wordEquiv D e) ?_)
    exact fun a => (hi a).symm
  rw [← he, Nat.card_eq_fintype_card, Nat.dvd_iff_mod_eq_zero]
  exact muSelected_mod b

include hmu htau hlam hpilam hxi hpiXi hcross in
/-- The order-five actor forces the first of the two printed fusion alternatives. -/
public theorem mu_isConj_tau_mul_lam_of_l2_not_two
    (hN : ¬ IsPGroup 2 (normalizer (ambientElementary D e 3 : Set G))) :
    IsConj (D.a10ModelEmbedding e mu) (D.a10ModelEmbedding e (tau * lam)) := by
  classical
  by_contra hm
  have hncard := l2_normalizer_card D e hmu htau hlam hpilam hxi hpiXi hcross hN
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hd : 5 ∣ Nat.card (N D e) := by rw [hncard]; decide
  obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' 5 hd
  let A := zpowers n
  have hA : Nat.card A = 5 := (Nat.card_zpowers n).trans hn
  have hnot : FixedPoints.subgroup A (E D e) ≠ ⊤ := by
    intro ht
    have hc : (n : G) ∈ centralizer (E D e : Set G) := by
      apply mem_centralizer_iff.mpr
      intro y hy
      have hfix : (⟨y, hy⟩ : E D e) ∈ FixedPoints.subgroup A (E D e) := ht ▸ mem_top _
      have hf := congrArg (fun x : E D e => (x : G)) (hfix ⟨n, mem_zpowers n⟩)
      change (n : G) * y * (n : G)⁻¹ = y at hf
      exact (mul_inv_eq_iff_eq_mul.mp hf).symm
    rw [ambientElementary_selfCentralizing D e 3] at hc
    have hd := (E D e).orderOf_dvd_natCard hc
    rw [ambientElementary_card, Subgroup.orderOf_coe, hn] at hd
    norm_num at hd
  have hfixed := Theory.GroupAction.fixed_eq_bot_of_five_action_card_sixteen
    hA (ambientElementary_card D e 3) hnot
  let X := {x : E D e // IsConj (D.a10ModelEmbedding e mu) (x : G)}
  let _ : MulAction A X := {
    smul a x := ⟨a • x.val, x.property.trans (isConj_iff.mpr ⟨((a : N D e) : G), rfl⟩)⟩
    one_smul x := by apply Subtype.ext; exact one_smul A x.val
    mul_smul a b x := by apply Subtype.ext; exact mul_smul a b x.val }
  have hempty : IsEmpty (MulAction.fixedPoints A X) := ⟨by
    rintro ⟨x, hx⟩
    have hxfix : x.val ∈ FixedPoints.subgroup A (E D e) := by
      intro a
      exact congrArg Subtype.val (hx a)
    have hx1 : x.val = 1 := by simpa only [hfixed, mem_bot] using hxfix
    have hmu1 : mu ≠ 1 := by decide +kernel
    have hh := x.property
    rw [hx1, Subgroup.coe_one] at hh
    exact hmu1 ((D.a10ModelEmbedding_injective e)
      ((isConj_one_right.mp hh.symm).trans (map_one (D.a10ModelEmbedding e)).symm))⟩
  let _ := hempty
  have hp : IsPGroup 5 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hmod := hp.card_modEq_card_fixedPoints X
  have hdiv : 5 ∣ Nat.card X := by
    have hzero : Nat.card (MulAction.fixedPoints A X) = 0 := (Nat.card_eq_zero).mpr (Or.inl hempty)
    rw [hzero] at hmod
    exact Nat.modEq_zero_iff_dvd.mp hmod
  exact mu_fused_card_not_dvd D e hmu hcross hm hdiv

include hmu htau hlam hpilam hxi hpiXi hcross in
/-- Held's five-element fusion alternative on the literal L₂ normalizer. -/
public theorem l2_five_fusion
    (hN : ¬ IsPGroup 2 (normalizer (ambientElementary D e 3 : Set G))) :
    IsConj (D.a10ModelEmbedding e mu) (D.a10ModelEmbedding e (tau * lam)) ∨
      IsConj (D.a10ModelEmbedding e xi) (D.a10ModelEmbedding e (tau * lam)) :=
  Or.inl (mu_isConj_tau_mul_lam_of_l2_not_two D e hmu htau hlam hpilam hxi hpiXi hcross hN)

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS.CrossBranch
