module

public import Theory.GroupTheory.Commutator.NilpotentSaturation
public import Theory.Frattini.PGroup

/-!
# The derived Frattini subgroup of a powerful two-group

For a finite two-group `G` satisfying `G′ ≤ G⁴`, conjugation by `G` acts
trivially on `G′ / Φ(G′)`. This is the Frattini consequence of powerful
embedding needed to prove that a two-generated powerful two-group has cyclic
derived subgroup: in the quotient by `Φ(G′)`, the derived subgroup is central,
so the commutator of a generating pair generates it.

Write `D = G′`, `F = Φ(D)` (viewed in `G`) and `C = [D,G]`. In the quotient
by `F[C,G]`, the derived subgroup has exponent two and the third commutators
are central. The commutator product identity gives `[x²,y] = [x,[x,y]]`,
and hence `[x⁴,y] = 1`. Powerfulness therefore makes the derived subgroup
central in this quotient, yielding `C ≤ F[C,G]`. Nilpotent absorption gives
`C ≤ F`.

This proof uses elementary commutator calculus and the nilpotence of finite
p-groups. It supplies the embedding input to the two-generator argument in
Traustason–Williams, *Powerfully nilpotent groups of rank 2 or small order*,
Section 2 (arXiv:2002.02694), without requiring the stronger bound `[D,G] ≤ D⁴`.
-/
open Subgroup
open scoped commutatorElement

variable {G : Type*} [Group G]

private theorem fourth_central
    (hsq : ∀ d ∈ _root_.commutator G, d ^ 2 = 1)
    (hc : ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤ center G) (x : G) :
    x ^ 4 ∈ center G := by
  apply mem_center_iff.mpr
  intro y
  have hxy : ⁅x,y⁆ ∈ _root_.commutator G :=
    commutator_mem_commutator (mem_top x) (mem_top y)
  have ht : ⁅x,⁅x,y⁆⁆ ∈ center G := by
    apply hc
    rw [commutator_comm]
    exact commutator_mem_commutator (mem_top x) hxy
  have hs : ⁅x ^ 2,y⁆ = ⁅x,⁅x,y⁆⁆ := by
    rw [pow_two, commutatorElement_mul_left_eq_conj_mul]
    have h := hsq ⁅x,y⁆ hxy
    rw [pow_two] at h
    calc
      x * ⁅x,y⁆ * x⁻¹ * ⁅x,y⁆ = ⁅x,⁅x,y⁆⁆ * (⁅x,y⁆ * ⁅x,y⁆) := by
        simp [commutatorElement_def, mul_assoc]
      _ = ⁅x,⁅x,y⁆⁆ := by rw [h, mul_one]
  have ht2 : ⁅x,⁅x,y⁆⁆ ^ 2 = 1 :=
    hsq _ (commutator_mem_commutator (mem_top x) (mem_top _))
  apply (commutatorElement_eq_one_iff_mul_comm.mp ?_).symm
  rw [show x ^ 4 = x ^ 2 * x ^ 2 by simp [← pow_add],
    commutatorElement_mul_left_eq_conj_mul, hs,
    mem_center_iff.mp ht (x ^ 2), mul_inv_cancel_right, ← pow_two, ht2]

/-- In a powerful finite two-group, the ambient group centralizes the Frattini
quotient of its derived subgroup. The right-hand side views `Φ(G′)` in `G`. -/
public theorem IsPGroup.commutator_derived_le_map_frattini_of_le_fourthPowers [Finite G] (hG : IsPGroup 2 G)
    (hp : _root_.commutator G ≤ closure (Set.range (fun x : G => x ^ 4))) :
    ⁅_root_.commutator G, (⊤ : Subgroup G)⁆ ≤
      (frattini (_root_.commutator G)).map (_root_.commutator G).subtype := by
  let D := _root_.commutator G
  let F := (frattini D).map D.subtype
  let C := ⁅D, (⊤ : Subgroup G)⁆
  let K := F ⊔ ⁅C, (⊤ : Subgroup G)⁆
  have hC : C ≤ K := by
    let q := QuotientGroup.mk' K
    have hsurj : Function.Surjective q := QuotientGroup.mk'_surjective K
    have hD : D.map q = _root_.commutator (G ⧸ K) := by
      change (_root_.commutator G).map q = _
      rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hsurj]
      rfl
    have hCmap : C.map q = ⁅_root_.commutator (G ⧸ K), (⊤ : Subgroup (G ⧸ K))⁆ := by
      change (⁅D, (⊤ : Subgroup G)⁆).map q = _
      rw [map_commutator, hD,
        map_top_of_surjective q hsurj]
    have hcentral : ⁅_root_.commutator (G ⧸ K), (⊤ : Subgroup (G ⧸ K))⁆ ≤
        center (G ⧸ K) := by
      apply commutator_top_right_eq_bot_iff_le_center.mp
      rw [← hCmap, ← map_top_of_surjective q hsurj, ← map_commutator]
      apply (Subgroup.map_eq_bot_iff _).mpr
      rw [QuotientGroup.ker_mk']
      exact le_sup_right
    have hsquare : ∀ d ∈ _root_.commutator (G ⧸ K), d ^ 2 = 1 := by
      intro d hd
      rw [← hD] at hd
      obtain ⟨e, he, rfl⟩ := hd
      rw [← map_pow]
      apply (QuotientGroup.eq_one_iff _).mpr
      apply (le_sup_left : F ≤ K)
      let : Fact (IsPGroup 2 D) := ⟨hG.to_subgroup D⟩
      exact ⟨(⟨e, he⟩ : D) ^ 2,
        pth_power_mem_frattini_of_isPGroup (p := 2) (⟨e, he⟩ : D), rfl⟩
    have hDC : _root_.commutator (G ⧸ K) ≤ center (G ⧸ K) := by
      rw [← hD]
      apply map_le_iff_le_comap.mpr
      apply hp.trans
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨x, rfl⟩
      change q (x ^ 4) ∈ center (G ⧸ K)
      rw [map_pow]
      exact fourth_central hsquare hcentral (q x)
    have hzero : C.map q = ⊥ := by
      rw [hCmap]
      exact commutator_top_right_eq_bot_iff_le_center.mpr hDC
    simpa only [q, QuotientGroup.ker_mk'] using (Subgroup.map_eq_bot_iff C).mp hzero
  exact le_of_le_sup_commutator_of_isNilpotent ⊤ C F ⊤
    (Group.isNilpotent_top.mpr hG.isNilpotent) le_top le_top le_top
    (by rw [normalizer_eq_top]) hC
