module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SupportActions
public import Theory.GroupTheory.PrimeSubgroupInvolution
public import Theory.GroupAction.CommutatorSemidirect
public import Theory.Representation.InvertedOddSupportRank

/-!
# Saturating the five-support displacement planes

An involution moving a normalized five-factor inverts it; the square-order
identity for an inverted odd support gives a displacement plane on its
sixteen-element support. A centralizing involution fixes that support.

For two pure involutions, the paired displacement homomorphism has kernel
the common fixed subgroup. Cross-fixed supports put the product of their
two planes in its image. A global fixed-index bound of sixteen therefore
makes that product the entire image, proving both full-support identities.
The one-involution argument is the same cardinal comparison with bound four.
Finally, coprime splitting proves fixation of the odd fixed complement.

These are algebraic steps in Aschbacher–Smith, combined manuscript
(1 March 2004), 13.8.13, printed p.951 / PDF p.968. Normalization, support
orders and the global bound are explicit inputs; the assembly module derives
the actor alternatives and supplies them.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives.SplitAction
variable {W : Type*} [Group W] [Finite W] [IsElementaryAbelian 2 W]

private def delta (t : MulAut W) : W →* W where
  toFun w := w⁻¹ * t w
  map_one' := by simp
  map_mul' x y := by simp only [mul_inv_rev, map_mul]; ac_rfl

omit [Finite W] [IsElementaryAbelian 2 W] in
private theorem two_elements (A : Subgroup (MulAut W)) (hA : Nat.card A = 2)
    (t : A) (ht : t ≠ 1) (b : A) : b = 1 ∨ b = t := by
  by_cases hb : b = 1
  · exact Or.inl hb
  · obtain ⟨s, _, hs⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
    exact Or.inr ((hs b hb).trans (hs t ht).symm)

omit [Finite W] in
private theorem delta_ker (A : Subgroup (MulAut W)) (hA : Nat.card A = 2)
    (t : A) (ht : t ≠ 1) :
    (delta (t : MulAut W)).ker = FixedPoints.subgroup A W := by
  ext w
  constructor
  · intro hw b
    have hf : (t : MulAut W) w = w := (inv_mul_eq_one.mp hw).symm
    rcases two_elements A hA t ht b with rfl | rfl
    · exact one_smul A w
    · exact hf
  · intro hw
    exact inv_mul_eq_one.mpr (hw t).symm

omit [Finite W] in
private theorem delta_map (A : Subgroup (MulAut W)) (hA : Nat.card A = 2)
    (t : A) (ht : t ≠ 1) (X : Subgroup W) :
    X.map (delta (t : MulAut W)) = commutatorSubgroup A W X := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact subset_closure ⟨t, x, hx, rfl⟩
  · rw [commutatorSubgroup, closure_le]
    rintro _ ⟨b, x, hx, rfl⟩
    rcases two_elements A hA t ht b with rfl | rfl
    · change x⁻¹ * ((1 : A) • x) ∈ X.map (delta (t : MulAut W))
      simp only [one_smul, inv_mul_cancel]
      exact (X.map _).one_mem
    · exact mem_map_of_mem _ hx

omit [Finite W] [IsElementaryAbelian 2 W] in
private theorem fixed_sup (A B : Subgroup (MulAut W)) :
    FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W =
      FixedPoints.subgroup A W ⊓ FixedPoints.subgroup B W := by
  ext w
  constructor
  · intro hw
    exact ⟨fun a => hw ⟨a, (show A ≤ A ⊔ B from le_sup_left) a.property⟩,
      fun b => hw ⟨b, (show B ≤ A ⊔ B from le_sup_right) b.property⟩⟩
  · rintro ⟨hA, hB⟩ b
    have hfix : A ⊔ B ≤ MulAction.stabilizer (MulAut W) w :=
      sup_le (fun a ha => hA ⟨a, ha⟩) (fun a ha => hB ⟨a, ha⟩)
    exact hfix b.property

omit [Finite W] in
theorem involution_displacement_index (A : Subgroup (MulAut W)) (hA : Nat.card A = 2) :
    Nat.card (commutatorAction A W) = (FixedPoints.subgroup A W).index := by
  obtain ⟨t, ht, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  rw [← delta_ker A hA t ht, index_ker, MonoidHom.range_eq_map, delta_map A hA t ht]

/-- Equality in the global fixed-index bound saturates both pure displacements. -/
theorem split_saturation (A B : Subgroup (MulAut W)) (X Y : Subgroup W)
    (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hXB : X ≤ FixedPoints.subgroup B W) (hYA : Y ≤ FixedPoints.subgroup A W)
    (hX : Nat.card (commutatorSubgroup A W X) = 4)
    (hY : Nat.card (commutatorSubgroup B W Y) = 4)
    (hbound : (FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W).index ≤ 16) :
    commutatorSubgroup A W X = commutatorAction A W ∧
    commutatorSubgroup B W Y = commutatorAction B W ∧
    (FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W).relIndex (X ⊔ Y) = 16 := by
  obtain ⟨t, ht, _⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
  obtain ⟨u, hu, _⟩ := (Nat.card_eq_two_iff' (1 : B)).mp hB
  let d := (delta (t : MulAut W)).prod (delta (u : MulAut W))
  let DX := X.map (delta (t : MulAut W))
  let DY := Y.map (delta (u : MulAut W))
  have hker : d.ker = FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W := by
    rw [MonoidHom.ker_prod, delta_ker A hA t ht, delta_ker B hB u hu, fixed_sup]
  have hDX : Nat.card DX = 4 := by
    dsimp only [DX]
    rw [delta_map A hA t ht X]
    exact hX
  have hDY : Nat.card DY = 4 := by
    dsimp only [DY]
    rw [delta_map B hB u hu Y]
    exact hY
  have hle_support : DX.prod DY ≤ (X ⊔ Y).map d := by
    rintro ⟨dx, dy⟩ ⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩⟩
    refine ⟨x * y, (X ⊔ Y).mul_mem
      ((show X ≤ X ⊔ Y from le_sup_left) hx)
      ((show Y ≤ X ⊔ Y from le_sup_right) hy), ?_⟩
    have hux : (u : MulAut W) x = x := hXB hx u
    have hty : (t : MulAut W) y = y := hYA hy t
    apply Prod.ext
    · change delta (t : MulAut W) (x * y) = delta (t : MulAut W) x
      rw [map_mul]
      change _ * (y⁻¹ * (t : MulAut W) y) = _
      rw [hty, inv_mul_cancel, mul_one]
    · change delta (u : MulAut W) (x * y) = delta (u : MulAut W) y
      rw [map_mul]
      change (x⁻¹ * (u : MulAut W) x) * _ = _
      rw [hux, inv_mul_cancel, one_mul]
  have hle : DX.prod DY ≤ d.range :=
    hle_support.trans (map_le_range _ _)
  have heq : DX.prod DY = d.range := by
    apply eq_of_le_of_card_ge hle
    rw [Nat.card_congr (prodEquiv DX DY).toEquiv, Nat.card_prod, hDX, hDY]
    simpa only [← index_ker, hker] using hbound
  have hrelative :
      (FixedPoints.subgroup (A ⊔ B : Subgroup (MulAut W)) W).relIndex (X ⊔ Y) = 16 := by
    rw [← hker, relIndex_ker]
    have he : (X ⊔ Y).map d = DX.prod DY :=
      le_antisymm ((map_le_range _ _).trans heq.symm.le) hle_support
    rw [he, Nat.card_congr (prodEquiv DX DY).toEquiv, Nat.card_prod, hDX, hDY]
  refine ⟨?_, ?_, hrelative⟩
  · rw [← delta_map A hA t ht X]
    apply le_antisymm
    · rw [delta_map A hA t ht X]
      exact commutatorSubgroup_mono le_top
    · rw [commutatorAction, ← delta_map A hA t ht ⊤]
      rintro _ ⟨w, _, rfl⟩
      have hm : d w ∈ DX.prod DY := heq.symm ▸ (show d w ∈ d.range from ⟨w, rfl⟩)
      exact hm.1
  · rw [← delta_map B hB u hu Y]
    apply le_antisymm
    · rw [delta_map B hB u hu Y]
      exact commutatorSubgroup_mono le_top
    · rw [commutatorAction, ← delta_map B hB u hu ⊤]
      rintro _ ⟨w, _, rfl⟩
      have hm : d w ∈ DX.prod DY := heq.symm ▸ (show d w ∈ d.range from ⟨w, rfl⟩)
      exact hm.2

/-- A moving normalized involution has a plane as its restricted displacement. -/
theorem five_support_plane (A R : Subgroup (MulAut W))
    (hA : Nat.card A = 2) (hR : Nat.card R = 5)
    (hS : Nat.card (commutatorAction R W) = 16)
    (hn : A ≤ normalizer (R : Set (MulAut W))) (hm : ⁅A, R⁆ ≠ ⊥) :
    Nat.card (commutatorSubgroup A W (commutatorAction R W)) = 4 ∧
      commutatorSubgroup A W (commutatorAction R W) ≤ commutatorAction R W := by
  classical
  have hnc : ¬ A ≤ centralizer (R : Set (MulAut W)) :=
    fun h => hm (commutator_eq_bot_iff_le_centralizer.mpr h)
  obtain ⟨t, ht, htc⟩ := SetLike.not_le_iff_exists.mp hnc
  have htne : t ≠ 1 := fun he => htc (he ▸ one_mem _)
  have ht2 : t ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := (⟨t, ht⟩ : A))
    rw [hA] at hh
    exact congrArg Subtype.val hh
  have htA : zpowers t = A := by
    apply eq_of_le_of_card_ge (zpowers_le.mpr ht)
    rw [Nat.card_zpowers, orderOf_eq_prime ht2 htne, hA]
  have hinv : ∀ r ∈ R, t * r * t⁻¹ = r⁻¹ := by
    rcases centralizes_or_inverts_prime_subgroup_of_sq_eq_one R
      (by rw [hR]; decide) t ht2 (hn ht) with hc | hi
    · exact (htc (mem_centralizer_iff.mpr fun r hr => (hc r hr).eq.symm)).elim
    · exact hi
  obtain ⟨hsquare, hle, _⟩ :=
    invertedOddSubgroup_support_card_data (W := W) R (by rw [hR]; decide)
      t ⟨htne, ht2⟩ hinv
  rw [htA] at hsquare hle
  rw [hS] at hsquare
  exact ⟨by nlinarith, hle⟩

/-- A centralizing involution fixes the entire five-support. -/
theorem five_support_fixed (A R : Subgroup (MulAut W))
    (hA : Nat.card A = 2) (hR : Nat.card R = 5)
    (hS : Nat.card (commutatorAction R W) = 16) (hc : ⁅A, R⁆ = ⊥) :
    commutatorAction R W ≤ FixedPoints.subgroup A W := by
  have hcop : Nat.Coprime (Nat.card R) (Nat.card W) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hR, hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  intro w hw b
  have hb2 : (b : MulAut W) ^ 2 = 1 := by
    have hh := pow_card_eq_one' (x := b)
    rw [hA] at hh
    exact congrArg Subtype.val hh
  exact Localization.fixes_support_of_centralizes_five R hR hcop hS b hb2
    (commutator_eq_bot_iff_le_centralizer.mp hc b.property) w hw

/-- A plane already exhausts the displacement allowed by an index-four bound. -/
theorem single_saturation (A : Subgroup (MulAut W)) (X : Subgroup W)
    (hA : Nat.card A = 2) (hX : Nat.card (commutatorSubgroup A W X) = 4)
    (hbound : (FixedPoints.subgroup A W).index ≤ 4) :
    commutatorSubgroup A W X = commutatorAction A W ∧
      Nat.card (commutatorAction A W) = 4 := by
  have he : commutatorSubgroup A W X = commutatorAction A W :=
    eq_of_le_of_card_ge (commutatorSubgroup_mono le_top)
      (by rw [involution_displacement_index A hA, hX]; exact hbound)
  exact ⟨he, he ▸ hX⟩

/-- Exhausting the displacement on the odd support forces fixation of its
coprime fixed complement. This also controls the P-fixed complement in the
application, since P contains the relevant five-factor. -/
theorem fixes_odd_complement (A R : Subgroup (MulAut W))
    (hR : Nat.card R = 5) (hn : A ≤ normalizer (R : Set (MulAut W)))
    (hfull : commutatorAction A W ≤ commutatorAction R W) :
    FixedPoints.subgroup R W ≤ FixedPoints.subgroup A W := by
  have hcop : Nat.Coprime (Nat.card R) (Nat.card W) := by
    obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 W).exists_card_eq
    rw [hR, hn]
    exact (by decide : Nat.Coprime 5 2).pow_right n
  have hcompl :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (G := W) (A := R) (Group.isSolvable_of_comm fun x y => mul_comm x y)
      hcop inferInstance
  have hi := fixedPoints_isInvariant_of_normalizing_actor (V := W) A R hn
  intro w hw t
  have hdelta : w⁻¹ * (t • w) ∈ commutatorAction R W :=
    hfull (subset_closure ⟨t, w, mem_top w, rfl⟩)
  have hdeltaC : w⁻¹ * (t • w) ∈ FixedPoints.subgroup R W :=
    (FixedPoints.subgroup R W).mul_mem ((FixedPoints.subgroup R W).inv_mem hw)
      ((hi.invariant t w).mp hw)
  exact (inv_mul_eq_one.mp (hcompl.disjoint.le_bot ⟨hdeltaC, hdelta⟩)).symm

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.ActorAlternatives.SplitAction

end
