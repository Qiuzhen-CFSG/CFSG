module

public import Theory.PGroupCore
public import Theory.ThreeSubgroups

/-!
# Detecting p-group automorphisms on a self-centralizing normal subgroup

Let A be a p-group normalizing Y, with O_p(Y) trivial. If A fixes a normal
self-centralizing subgroup N of Y pointwise, then A fixes Y. The three-subgroups
lemma places [A,Y] in C_Y(N), which is abelian and contained in N. Thus A fixes
its own displacements. Each displacement has p-power order, and so lies in the
p-core of the normal abelian group C_Y(N), hence in O_p(Y).

Source: the automorphism argument in Aschbacher–Smith A.1.9, printed p.21.
Taking N to be the intrinsic generalized Fitting subgroup gives that lemma.
-/

open Subgroup
open scoped commutatorElement

/-- A p-group fixing a normal self-centralizing subgroup of a group with
trivial p-core fixes that whole group. Normalization is relative to the target. -/
public theorem Subgroup.centralizes_of_pGroup_of_selfCentralizing_normal {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (A Y : Subgroup G) (N : Subgroup Y) [N.Normal]
    (hA : IsPGroup p A) (hn : A ≤ normalizer (Y : Set G))
    (hcore : pCore p Y = ⊥)
    (hself : centralizer (N : Set Y) ≤ N)
    (hfix : A ≤ centralizer (N.map Y.subtype : Set G)) :
    A ≤ centralizer (Y : Set G) := by
  let F := N.map Y.subtype
  let C := centralizer (N : Set Y)
  have hYN : Y ≤ normalizer (F : Set G) := by
    have hh := (N.le_normalizer_map Y.subtype)
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype] using hh
  have hNA : ⁅F, A⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hfix
  have hNYA : ⁅⁅F,Y⁆,A⁆ = ⊥ := by
    apply bot_unique
    exact (commutator_mono (le_normalizer_iff_commutator_le_left.mp hYN) le_rfl).trans hNA.le
  have hAYN : ⁅⁅A,Y⁆,F⁆ = ⊥ := by
    apply commutator_commutator_eq_bot_of_rotate
    · simpa only [commutator_comm Y F] using hNYA
    · simp only [hNA, commutator_bot_left]
  have hAYY : ⁅A,Y⁆ ≤ Y := by
    rw [commutator_comm]
    exact le_normalizer_iff_commutator_le_left.mp hn
  have hAYC : ⁅A,Y⁆ ≤ centralizer (F : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp hAYN
  let _ : IsMulCommutative C := ⟨⟨fun x y => Subtype.ext
    ((mem_centralizer_iff.mp x.property) y (hself y.property)).symm⟩⟩
  have hpc : (pCore p C).map C.subtype ≤ pCore p Y :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map C.subtype⟩
  intro a ha y hy
  let x := ⁅a,y⁆
  have hxY : x ∈ Y := hAYY (commutator_mem_commutator ha hy)
  have hxC : (⟨x,hxY⟩ : Y) ∈ C := by
    intro z hz
    apply Subtype.ext
    exact hAYC (commutator_mem_commutator ha hy) z (mem_map_of_mem Y.subtype hz)
  have hxF : x ∈ F := mem_map_of_mem Y.subtype (hself hxC)
  have hax : Commute a x := (hfix ha x hxF).symm
  obtain ⟨n, hn⟩ := hA.exists_pow_pow_eq_one ⟨a,ha⟩
  have hapow : a ^ p ^ n = 1 := congrArg Subtype.val hn
  have hpow : x ^ p ^ n = 1 := by
    have he : a⁻¹ * x = y * a⁻¹ * y⁻¹ := by dsimp [x]; group
    have hh : Commute a (a⁻¹*x) := (Commute.refl a).inv_right.mul_right hax
    calc
      x ^ p ^ n = (a * (a⁻¹*x)) ^ p ^ n := by simp
      _ = a ^ p ^ n * (a⁻¹*x) ^ p ^ n := hh.mul_pow _
      _ = 1 := by rw [he, conj_pow, inv_pow, hapow]; simp
  let c : C := ⟨⟨x,hxY⟩,hxC⟩
  have hcp : c ^ p ^ n = 1 := Subtype.ext (Subtype.ext hpow)
  have hcyc : IsPGroup p (zpowers c) := IsPGroup.of_card_dvd_pow
    (by rw [Nat.card_zpowers]; exact orderOf_dvd_of_pow_eq_one hcp)
  have hc : c ∈ pCore p C := (le_sSup ⟨inferInstance, hcyc⟩ : zpowers c ≤ pCore p C)
    (mem_zpowers _)
  have hxbot : (⟨x,hxY⟩ : Y) ∈ (⊥ : Subgroup Y) := by
    rw [← hcore]
    exact hpc (mem_map_of_mem C.subtype hc)
  have hxone : x = 1 := congrArg Subtype.val (mem_bot.mp hxbot)
  exact (commutatorElement_eq_one_iff_mul_comm.mp hxone).symm
