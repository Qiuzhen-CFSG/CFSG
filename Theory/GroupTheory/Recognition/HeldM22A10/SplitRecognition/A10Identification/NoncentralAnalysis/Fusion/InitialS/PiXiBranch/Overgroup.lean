module

public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Overgroup.Local
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.CentralizerStructure.Recognition.FaithfulExclusion.SourceActors.Section213Alpha.Overgroup.Tools
public import Theory.GroupTheory.Recognition.HeldM22A10.SplitRecognition.A10Identification.NoncentralAnalysis.Fusion.Bounds

/-!
# Held's initial pi--xi overgroup

In the first case of Held 2.9, pi is conjugate to pi*xi but not to xi or mu.
The centralizer of pi*xi therefore contains an order-64 enlargement of the
local order-32 subgroup B. Its center and unique nonidentity square force
this enlargement into N(<pi,mu,xi>) intersect C(pi*mu). Joining it with
C_H(mu), the three-element orbit of pi and the Sylow bound in C_G(pi*mu)
give an overgroup of order 192. This supplies the actual cubic actor in the
next module, without assuming the later xi--mu fusion theorem.

Source: D. Held, Illinois J. Math. 13 (1969), 224--240,
DOI 10.1215/ijm/1256053756, Lemma 2.9, printed pp.229--230.
-/

open Subgroup
namespace Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
open CentralizerStructure.FaithfulExclusion
universe u
variable {G : Type u} [Group G] (D : LocalData G)
  (e : D.centralizer ≃* CentralizerModels.a10Centralizer)

open Coordinates

private noncomputable def overgroupB : Subgroup G := overgroupModelB.map (D.a10ModelEmbedding e)
private noncomputable def overgroupP : Subgroup G :=
  (centralizer ({Coordinates.mu} : Set H)).map (D.a10ModelEmbedding e)

private theorem overgroupB_card : Nat.card (overgroupB D e) = 32 := by
  rw [overgroupB, card_map_of_injective (D.a10ModelEmbedding_injective e), overgroupModelB_card]

private theorem overgroupP_card : Nat.card (overgroupP D e) = 64 := by
  rw [overgroupP, card_map_of_injective (D.a10ModelEmbedding_injective e), centralizer_mu_card]

private theorem overgroupB_center :
    (overgroupB D e ⊓ centralizer (overgroupB D e : Set G) : Subgroup G) = section213Eight D e := by
  let f := D.a10ModelEmbedding e
  ext x
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    have hyc : y ∈ centralizer (overgroupModelB : Set H) := by
      intro z hz
      apply D.a10ModelEmbedding_injective e
      simpa only [map_mul] using hc (f z) (mem_map_of_mem f hz)
    obtain ⟨i, hi⟩ := (overgroupModelB_center y).mp ⟨hy, hyc⟩
    exact (mem_section213Eight_iff D e 0 _).mpr ⟨i, congrArg f hi⟩
  · intro hx
    obtain ⟨i, rfl⟩ := (mem_section213Eight_iff D e 0 x).mp hx
    have hi := (overgroupModelB_center (section213Word 0 i)).mpr ⟨i, rfl⟩
    refine ⟨mem_map_of_mem f hi.1, ?_⟩
    rintro z ⟨y, hy, rfl⟩
    simpa only [map_mul] using congrArg f (hi.2 y hy)

private theorem overgroupB_normalizer :
    normalizer (overgroupB D e : Set G) ≤
      normalizer (section213Eight D e : Set G) ⊓
      centralizer ({D.a10ModelEmbedding e corePi} : Set G) := by
  apply le_inf
  · rw [← overgroupB_center]
    exact overgroup_normalizer_center _
  · apply overgroup_normalizer_centralizes_square
    · intro h
      have he : corePi = (1 : H) := D.a10ModelEmbedding_injective e (h.trans (map_one _).symm)
      exact (by decide +kernel : corePi ≠ (1 : H)) he
    · rintro x ⟨y, hy, rfl⟩
      rcases overgroupModelB_square y hy with h | h
      · left; rw [← map_pow, h, map_one]
      · right; rw [← map_pow, h]
    · obtain ⟨x, hx, hs⟩ := overgroupModelB_square_witness
      exact ⟨_, mem_map_of_mem _ hx, by rw [← map_pow, hs]⟩

private theorem overgroupB_centralizes (d : Bit) :
    overgroupB D e ≤ centralizer ({D.a10ModelEmbedding e (normalizedXi d)} : Set G) := by
  rintro x ⟨y, hy, rfl⟩
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul] using congrArg (D.a10ModelEmbedding e)
    (mem_centralizer_singleton_iff.mp (overgroupModelB_centralizes d hy))

private theorem overgroupP_le : overgroupP D e ≤ D.centralizer := by
  rintro x ⟨y, hy, rfl⟩
  exact (e.symm y).property

private theorem overgroupP_normalizes [Finite G] :
    overgroupP D e ≤ normalizer (section213Eight D e : Set G) := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_normalizer_iff_map_conj_eq]
  apply eq_of_le_of_card_ge
  · rintro z ⟨w, hw, rfl⟩
    obtain ⟨i, rfl⟩ := (mem_section213Eight_iff D e 0 w).mp hw
    obtain ⟨j, hj⟩ := overgroupModelP_conjugates y hy i
    apply (mem_section213Eight_iff D e 0 _).mpr
    refine ⟨j, ?_⟩
    change D.a10ModelEmbedding e (section213Word 0 j) =
      D.a10ModelEmbedding e y * D.a10ModelEmbedding e (section213Word 0 i) *
        (D.a10ModelEmbedding e y)⁻¹
    simpa only [map_mul, map_inv] using congrArg (D.a10ModelEmbedding e) hj
  · rw [card_map_of_injective (MulAut.conj _).injective]

private theorem overgroupP_centralizes :
    overgroupP D e ≤ centralizer ({D.a10ModelEmbedding e corePi} : Set G) := by
  rintro x ⟨y, hy, rfl⟩
  have hh : y ∈ centralizer ({corePi} : Set H) := overgroupModelP_centralizer.symm ▸ hy
  apply mem_centralizer_singleton_iff.mpr
  simpa only [map_mul] using congrArg (D.a10ModelEmbedding e) (mem_centralizer_singleton_iff.mp hh)

private theorem overgroupP_intersection :
    D.centralizer ⊓ centralizer ({D.a10ModelEmbedding e corePi} : Set G) = overgroupP D e := by
  apply le_antisymm
  · rintro x ⟨hx, hc⟩
    have hx' : x ∈ (D.a10ModelEmbedding e).range := by rwa [D.a10ModelEmbedding_range e]
    obtain ⟨y, rfl⟩ := hx'
    refine mem_map.mpr ⟨y, ?_, rfl⟩
    rw [← overgroupModelP_centralizer, mem_centralizer_singleton_iff]
    apply D.a10ModelEmbedding_injective e
    simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc
  · exact le_inf (overgroupP_le D e) (overgroupP_centralizes D e)

private theorem overgroup_xi_intersection_card (d : Bit) :
    Nat.card (D.centralizer ⊓ centralizer ({D.a10ModelEmbedding e (normalizedXi d)} : Set G) : Subgroup G) = 96 := by
  have he : (D.centralizer ⊓ centralizer ({D.a10ModelEmbedding e (normalizedXi d)} : Set G) : Subgroup G) =
      (centralizer ({normalizedXi d} : Set H)).map (D.a10ModelEmbedding e) := by
    ext x
    constructor
    · rintro ⟨hx, hc⟩
      have hx' : x ∈ (D.a10ModelEmbedding e).range := by rwa [D.a10ModelEmbedding_range e]
      obtain ⟨y, rfl⟩ := hx'
      refine mem_map.mpr ⟨y, mem_centralizer_singleton_iff.mpr ?_, rfl⟩
      apply D.a10ModelEmbedding_injective e
      simpa only [map_mul] using mem_centralizer_singleton_iff.mp hc
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(e.symm y).property, mem_centralizer_singleton_iff.mpr ?_⟩
      simpa only [map_mul] using congrArg (D.a10ModelEmbedding e) (mem_centralizer_singleton_iff.mp hy)
  rw [he, card_map_of_injective (D.a10ModelEmbedding_injective e), overgroupModelXi_card]

variable [Finite G]

private theorem overgroup_exists_T
    (d : Bit) (hpiXi : IsConj D.z
      (D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d))) :
    ∃ T : Subgroup G, Nat.card T = 64 ∧
      T ≤ normalizer (section213Eight D e : Set G) ∧
      T ≤ centralizer ({D.a10ModelEmbedding e corePi} : Set G) ∧ ¬ T ≤ D.centralizer := by
  let X := centralizer ({D.a10ModelEmbedding e (normalizedXi (d + 1))} : Set G)
  have hchoice : normalizedXi (d + 1) = Coordinates.pi * normalizedXi d := by
    have h : ∀ d : Bit, normalizedXi (d + 1) = Coordinates.pi * normalizedXi d := by
      decide +kernel
    exact h d
  have hBX : overgroupB D e ≤ X := overgroupB_centralizes D e (d + 1)
  have hBcardX : Nat.card ((overgroupB D e).subgroupOf X) = 2 ^ 5 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hBX).toEquiv, overgroupB_card]
    norm_num
  have hd : 2 ^ 6 ∣ Nat.card X := by
    have hconj : IsConj D.z (D.a10ModelEmbedding e (normalizedXi (d + 1))) := by
      rwa [hchoice]
    rw [centralizer_card_of_isConj D hconj]
    norm_num
  obtain ⟨S, hScard, hBS⟩ := Sylow.exists_subgroup_card_pow_prime_le 2 hd
    ((overgroupB D e).subgroupOf X) hBcardX (show 5 ≤ 6 by decide)
  let T : Subgroup G := S.map X.subtype
  have hTX : T ≤ X := map_subtype_le _
  have hTcard : Nat.card T = 64 := by
    rw [show Nat.card T = Nat.card S from card_map_of_injective X.subtype_injective, hScard]
    norm_num
  have hBT : overgroupB D e ≤ T := by
    intro x hx
    exact mem_map.mpr ⟨⟨x, hBX hx⟩, hBS hx, rfl⟩
  have hBcard : Nat.card ((overgroupB D e).subgroupOf T) = 32 :=
    (Nat.card_congr (subgroupOfEquivOfLe hBT).toEquiv).trans (overgroupB_card D e)
  have hindex : ((overgroupB D e).subgroupOf T).index = 2 := by
    have hc := ((overgroupB D e).subgroupOf T).card_mul_index
    rw [hBcard, hTcard] at hc
    omega
  have hTN : T ≤ normalizer (overgroupB D e : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hBT).mp (normal_of_index_eq_two hindex)
  have hTN' := hTN.trans (overgroupB_normalizer D e)
  refine ⟨T, hTcard, hTN'.trans inf_le_left, hTN'.trans inf_le_right, ?_⟩
  intro hTH
  have hd := card_dvd_of_le (le_inf hTH hTX)
  rw [hTcard, overgroup_xi_intersection_card D e (d + 1)] at hd
  norm_num at hd

private theorem overgroup_card_bound (K : Subgroup G) (x y z : G) (hx : x ∈ K)
    (horb : ∀ g ∈ K, g * x * g⁻¹ = x ∨ g * x * g⁻¹ = y ∨ g * x * g⁻¹ = z) :
    Nat.card K ≤ 3 * Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  classical
  let xk : K := ⟨x, hx⟩
  let S : Finset G := {x, y, z}
  let O := MulAction.orbit (ConjAct K) xk
  have hO (w : O) : (w.val : G) ∈ S := by
    obtain ⟨g, hg⟩ := w.property
    have hh := horb (g.ofConjAct : G) g.ofConjAct.property
    have he : (g.ofConjAct : G) * x * (g.ofConjAct : G)⁻¹ = (w.val : G) :=
      congrArg Subtype.val hg
    simpa only [he, S, Finset.mem_insert, Finset.mem_singleton] using hh
  have hcardO : Nat.card O ≤ 3 := by
    have hle := Nat.card_le_card_of_injective
      (fun w : O => (⟨(w.val : G), hO w⟩ : S))
      (by
        intro a b h
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun t : S => (t : G)) h)
    exact hle.trans (by simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, S] using (Finset.card_le_three (a := x) (b := y) (c := z)))
  let ec : MulAction.stabilizer (ConjAct K) xk ≃
      (K ⊓ centralizer ({x} : Set G) : Subgroup G) :=
    { toFun := fun g => ⟨g.val.ofConjAct, g.val.ofConjAct.property, by
        apply mem_centralizer_singleton_iff.mpr
        have h := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp g.property)
        exact mul_inv_eq_iff_eq_mul.mp h⟩
      invFun := fun g => ⟨ConjAct.toConjAct ⟨g.val, g.property.1⟩, by
        apply MulAction.mem_stabilizer_iff.mpr
        apply Subtype.ext
        exact mul_inv_eq_of_eq_mul (mem_centralizer_singleton_iff.mp g.property.2)⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hc := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (ConjAct K) xk)
  rw [Nat.card_prod, Nat.card_congr ec] at hc
  change Nat.card O * Nat.card (K ⊓ centralizer ({x} : Set G) : Subgroup G) = Nat.card K at hc
  rw [← hc]
  exact Nat.mul_le_mul_right _ hcardO

variable {D e}

omit [Finite G] in
private theorem overgroup_conj_isConj (g x : G) : IsConj x (g⁻¹ * x * g) :=
  isConj_iff.mpr ⟨g⁻¹, by simp only [inv_inv]⟩

private theorem overgroup_pi_conjugate_choices (d : Bit)
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (hxi : ¬ IsConj D.z (D.a10ModelEmbedding e (normalizedXi d)))
    (g : G) (hn : g ∈ normalizer (section213Eight D e : Set G))
    (hm : g⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g ≠ D.a10ModelEmbedding e Coordinates.pi) :
    g⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g = D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d) ∨
    g⁻¹ * D.a10ModelEmbedding e Coordinates.pi * g = D.a10ModelEmbedding e (corePi * normalizedXi d) := by
  let f := D.a10ModelEmbedding e
  have hnot : ¬ IsConj (f Coordinates.pi) (f Coordinates.mu) := by
    simpa only [f, Coordinates.pi, Coordinates.mu, LocalData.a10NoncentralInvolution, D.a10ModelEmbedding_central e] using hfusion
  have hpi : f Coordinates.pi ∈ section213Eight D e := by
    rw [mem_section213Eight_iff D e 0]
    exact ⟨(1, 0, 0), by simp [section213Word, f]⟩
  have hmem : g⁻¹ * f Coordinates.pi * g ∈ section213Eight D e := by
    simpa only [inv_inv] using
      (mem_normalizer_iff.mp ((normalizer _).inv_mem hn) (f Coordinates.pi)).mp hpi
  obtain ⟨i, hi⟩ := (mem_section213Eight_iff D e d _).mp hmem
  have hc : IsConj (f Coordinates.pi) (f (section213Word d i)) := by
    rw [hi]
    exact overgroup_conj_isConj g (f Coordinates.pi)
  have hcases : ∀ d i, section213Word d i = 1 ∨ section213Word d i = Coordinates.pi ∨
      section213Word d i = Coordinates.mu ∨ section213Word d i = corePi ∨
      section213Word d i = normalizedXi d ∨ section213Word d i = Coordinates.mu * normalizedXi d ∨
      section213Word d i = Coordinates.pi * normalizedXi d ∨
      section213Word d i = corePi * normalizedXi d := by decide +kernel
  have hp : IsConj (f corePi) (f Coordinates.mu) := by
    apply f.map_isConj
    apply isConj_iff.mpr
    exact ⟨taup, by decide +kernel⟩
  have hx : IsConj (f (Coordinates.mu * normalizedXi d)) (f (normalizedXi d)) := by
    apply f.map_isConj
    apply isConj_iff.mpr
    refine ⟨tau, ?_⟩
    have hl : ∀ d, tau * (Coordinates.mu * normalizedXi d) * tau⁻¹ = normalizedXi d := by
      decide +kernel
    exact hl d
  rcases hcases d i with h | h | h | h | h | h | h | h
  · rw [h, map_one] at hc
    have he : f Coordinates.pi = f 1 := (isConj_one_left.mp hc).trans f.map_one.symm
    have : Coordinates.pi = (1 : H) := (D.a10ModelEmbedding_injective e) he
    exact False.elim ((by decide +kernel : Coordinates.pi ≠ (1 : H)) this)
  · exact False.elim (hm (hi.symm.trans (congrArg f h)))
  · exact False.elim (hnot (by simpa only [h] using hc))
  · rw [h] at hc
    exact False.elim (hnot (hc.trans hp))
  · rw [h] at hc
    exact False.elim (hxi (by
      simpa only [f, D.a10ModelEmbedding_central e] using hc))
  · rw [h] at hc
    exact False.elim (hxi (by
      simpa only [f, D.a10ModelEmbedding_central e] using hc.trans hx))
  · exact Or.inl (hi.symm.trans (congrArg f h))
  · exact Or.inr (hi.symm.trans (congrArg f h))


variable (D e)

/-- The pi--pi*xi fusion branch supplies the actual order-192 overgroup of Held 2.9. -/
public theorem exists_section213Overgroup_of_piXi_fusion
    (hfusion : ¬ IsConj D.z (D.a10NoncentralInvolution e))
    (d : Bit) (hxi : ¬ IsConj D.z (D.a10ModelEmbedding e (normalizedXi d)))
    (hpiXi : IsConj D.z (D.a10ModelEmbedding e (Coordinates.pi * normalizedXi d))) :
    Nonempty (Section213Overgroup D e) := by
  let f := D.a10ModelEmbedding e
  obtain ⟨T, hTc, hTN, hTC, hTH⟩ := overgroup_exists_T D e d hpiXi
  let L := overgroupP D e ⊔ T
  have hLN : L ≤ normalizer (section213Eight D e : Set G) :=
    sup_le (overgroupP_normalizes D e) hTN
  have hLC : L ≤ centralizer ({f corePi} : Set G) :=
    sup_le (overgroupP_centralizes D e) hTC
  have hinter : (L ⊓ D.centralizer : Subgroup G) = overgroupP D e := by
    apply le_antisymm
    · rw [← overgroupP_intersection]
      exact le_inf inf_le_right (inf_le_left.trans hLC)
    · exact le_inf le_sup_left (overgroupP_le D e)
  have hpi : f Coordinates.pi = D.z := D.a10ModelEmbedding_central e
  have hpiL : f Coordinates.pi ∈ L := by
    apply (show overgroupP D e ≤ L from le_sup_left)
    apply mem_map_of_mem f
    exact mem_centralizer_singleton_iff.mpr (by decide +kernel)
  have hbound : Nat.card L ≤ 192 := by
    have hh := overgroup_card_bound L (f Coordinates.pi)
      (f (Coordinates.pi * normalizedXi d)) (f (corePi * normalizedXi d)) hpiL (by
        intro g hg
        by_cases hm : g * f Coordinates.pi * g⁻¹ = f Coordinates.pi
        · exact Or.inl hm
        · right
          simpa only [inv_inv] using overgroup_pi_conjugate_choices d hfusion hxi g⁻¹
            ((normalizer _).inv_mem (hLN hg)) (by simpa only [inv_inv] using hm))
    rw [hpi] at hh
    change Nat.card L ≤ 3 * Nat.card (L ⊓ D.centralizer : Subgroup G) at hh
    rw [hinter, overgroupP_card] at hh
    exact hh
  have hnot64 : Nat.card L ≠ 64 := by
    intro h
    have he : overgroupP D e = L := eq_of_le_of_card_ge le_sup_left (by rw [h, overgroupP_card])
    exact hTH (le_sup_right.trans (he ▸ overgroupP_le D e))
  have hnot128 : Nat.card L ≠ 128 := by
    intro h
    have hp : IsPGroup 2 L := IsPGroup.of_card (n := 7) (by rw [h]; decide)
    have hcore : IsConj (f corePi) (D.a10NoncentralInvolution e) := by
      change IsConj (f corePi) (f Coordinates.mu)
      apply f.map_isConj
      exact isConj_iff.mpr ⟨taup, by decide +kernel⟩
    have hh := overgroup_two_subgroup_card_le D e hfusion hcore L hp hLC
    omega
  have hcard : Nat.card L = 192 := by
    have hd := card_dvd_of_le (show overgroupP D e ≤ L from le_sup_left)
    rw [overgroupP_card] at hd
    have hpos := Nat.card_pos (α := L)
    omega
  exact ⟨⟨L, hcard, hLN, hLC, by rw [hinter, overgroupP_card]⟩⟩

end Theory.GroupTheory.HeldM22A10.A10Identification.NoncentralAnalysis.Fusion.InitialS
