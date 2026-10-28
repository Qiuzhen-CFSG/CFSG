module

public import CFSG.Quasithin.ChapterB.Section01.SolvableStructure.Glauberman.BlockConstruction.Basic
public import Theory.Representation.GoldschmidtONan.Basic
public import Theory.Representation.BinaryOffender.IrreducibleMovedGeneration
public import Theory.GroupTheory.PGroup.Subnormal
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-!
# Separation of subnormal cubic plane supports

Two relatively subnormal cubic subgroups of an odd-order subgroup have equal
binary plane supports, or disjoint supports which they fix pointwise across.
All supports below are the literal commutator subspaces of the original action.

For this cubic special case, the standard subnormal-p-subgroup theorem puts
both actors in the same three-core. Their join acts faithfully on the sum of
their supports by odd-order splitting. This sum has dimension at most four;
the three-part of |GL₄(2)| is nine, so the join is abelian. This supplies the
commutation inference without presupposing mutual normalization. Each plane
support is irreducible: a proper invariant binary line would be fixed, contrary
to coprime splitting. The invariant intersection now gives equality or zero;
in the latter case all cross-displacements vanish in that intersection.

Source: Kurzweil–Stellmacher, *The Theory of Finite Groups*, 9.3.5, printed
pp.243–244 (PDF pp.256–257 of `refs/original/kurzweil.pdf`). The source proves
the more general irreducible-support theorem by induction on conjugate subnormal
subgroups. The order bound here exploits the explicit cubic and plane hypotheses
of `CubicSupportSeparation`; it does not assert the general theorem.
-/

public section

open Subgroup Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

private theorem split (X : Subgroup G) [Finite X] (hodd : Odd (Nat.card X)) :
    IsCompl (fixedSpace ρ X) (subspaceCommutator ρ ⊤ X) := by
  have he : subspaceCommutator ρ ⊤ X =
      Representation.RegularCyclicNormalClosure.displacementSpan ρ X ⊤ := by
    unfold subspaceCommutator Representation.RegularCyclicNormalClosure.displacementSpan
    congr 1
    ext v
    simp only [eq_comm]
  rw [he]
  exact Representation.GoldschmidtONan.isCompl_fixed_moved_of_odd hodd

private theorem moved_mono {X Y : Subgroup G} (h : X ≤ Y) :
    subspaceCommutator ρ ⊤ X ≤ subspaceCommutator ρ ⊤ Y := by
  apply Submodule.span_mono
  rintro _ ⟨x, hx, v, hv, rfl⟩
  exact ⟨x, h hx, v, hv, rfl⟩

private theorem moved_sup (X Y : Subgroup G) :
    subspaceCommutator ρ ⊤ (X ⊔ Y) =
      subspaceCommutator ρ ⊤ X ⊔ subspaceCommutator ρ ⊤ Y := by
  let W := subspaceCommutator ρ ⊤ X ⊔ subspaceCommutator ρ ⊤ Y
  let T : Subgroup G := {
    carrier := {g | ∀ v, ρ g v - v ∈ W}
    one_mem' := by intro v; simp
    mul_mem' := by
      intro a b ha hb v
      have hh := W.add_mem (ha (ρ b v)) (hb v)
      simpa only [map_mul, Module.End.mul_apply, sub_add_sub_cancel] using hh
    inv_mem' := by
      intro a ha v
      have hh := W.neg_mem (ha (ρ a⁻¹ v))
      simpa only [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply, neg_sub] using hh }
  have hT : X ⊔ Y ≤ T := by
    apply sup_le
    · intro x hx v
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨x, hx, v, trivial, rfl⟩)
    · intro y hy v
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨y, hy, v, trivial, rfl⟩)
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    exact hT hg v
  · exact sup_le (moved_mono ρ le_sup_left) (moved_mono ρ le_sup_right)

private theorem support_faithful (hρ : Function.Injective ρ)
    (X : Subgroup G) [Finite X] (hodd : Odd (Nat.card X)) :
    Function.Injective (invariantSubspace ρ X (subspaceCommutator ρ ⊤ X)
      (subspaceCommutator_invariant ρ ⊤ X)).toRepresentation.asGroupHom := by
  apply (injective_iff_map_eq_one _).mpr
  intro x hx
  apply Subtype.ext
  apply hρ
  ext v
  have hc := split ρ X hodd
  obtain ⟨c, hc, w, hw, rfl⟩ := Submodule.mem_sup.mp
    (show v ∈ fixedSpace ρ X ⊔ subspaceCommutator ρ ⊤ X by
      rw [hc.sup_eq_top]; trivial)
  have hwfix : ρ (x : G) w = w := congrArg Subtype.val
    (LinearMap.congr_fun (congrArg Units.val hx) ⟨w, hw⟩)
  have hcfix : ρ (x : G) c = c := hc x
  simp only [map_add, hcfix, hwfix, Subgroup.coe_one, map_one, Module.End.one_apply]

private theorem three_group_commutative_of_small_dimension
    [Finite G] [FiniteDimensional (ZMod 2) V]
    (hp : IsPGroup 3 G) (hf : Function.Injective ρ.asGroupHom)
    (hd : Module.finrank (ZMod 2) V ≤ 4) : IsMulCommutative G := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hGL : ∀ d : ℕ, d ≤ 4 →
      Nat.card (Matrix.GeneralLinearGroup (Fin d) (ZMod 2)) ∣ 20160 := by
    intro d hd
    rw [Matrix.card_GL_field]
    interval_cases d <;> norm_num [Fin.prod_univ_succ]
  let b := Module.finBasis (ZMod 2) V
  let f := (Matrix.GeneralLinearGroup.toLin' b).symm.toMonoidHom.comp ρ.asGroupHom
  have hf' : Function.Injective f := (Matrix.GeneralLinearGroup.toLin' b).symm.injective.comp hf
  have hdiv := Subgroup.card_dvd_of_injective f hf'
  have horder : Nat.card G ∣ 20160 := hdiv.trans (hGL _ hd)
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra hnot
    have hbad : 27 ∣ 20160 := (show 27 ∣ 3 ^ n from
      Nat.pow_dvd_pow 3 (by omega : 3 ≤ n)).trans (hn ▸ horder)
    norm_num at hbad
  interval_cases n
  · have : Subsingleton G := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
    exact ⟨⟨fun _ _ => Subsingleton.elim _ _⟩⟩
  · let : IsCyclic G := isCyclic_of_prime_card (p := 3) (by simpa using hn)
    infer_instance
  · exact IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hn

private theorem cubic_join_commutative [Finite G] [FiniteDimensional (ZMod 2) V]
    (hρ : Function.Injective ρ) (K X Y : Subgroup G) (hodd : Odd (Nat.card K))
    (hXK : X ≤ K) (hYK : Y ≤ K)
    (hX : (X.subgroupOf K).IsSubnormal) (hY : (Y.subgroupOf K).IsSubnormal)
    (hcX : Nat.card X = 3) (hcY : Nat.card Y = 3)
    (hdX : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2)
    (hdY : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Y) = 2) :
    IsMulCommutative (X ⊔ Y : Subgroup G) := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hXp : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by simpa using hcX)
  have hYp : IsPGroup 3 Y := IsPGroup.of_card (n := 1) (by simpa using hcY)
  have hle : X ⊔ Y ≤ (pCore 3 K).map K.subtype := sup_le
    (isPGroup_le_pCoreAmbient_of_isSubnormalIn K X 3 hXK hX hXp)
    (isPGroup_le_pCoreAmbient_of_isSubnormalIn K Y 3 hYK hY hYp)
  have hp : IsPGroup 3 (X ⊔ Y : Subgroup G) :=
    ((pCore_isPGroup (p := 3) (G := K)).map K.subtype).of_injective
      (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have ho : Odd (Nat.card (X ⊔ Y : Subgroup G)) :=
    hodd.of_dvd_nat (Subgroup.card_dvd_of_le (sup_le hXK hYK))
  let W := subspaceCommutator ρ ⊤ (X ⊔ Y)
  let σ := (invariantSubspace ρ (X ⊔ Y) W
    (subspaceCommutator_invariant ρ ⊤ (X ⊔ Y))).toRepresentation
  apply three_group_commutative_of_small_dimension σ hp (support_faithful ρ hρ _ ho)
  change Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ (X ⊔ Y)) ≤ 4
  rw [moved_sup]
  have hh := Submodule.finrank_sup_add_finrank_inf_eq
    (subspaceCommutator ρ ⊤ X) (subspaceCommutator ρ ⊤ Y)
  omega

private theorem line_fixed [FiniteDimensional (ZMod 2) V]
    (X : Subgroup G) (D : Submodule (ZMod 2) V)
    (hD : X ≤ subspaceStabilizer ρ D) (hd : Module.finrank (ZMod 2) D = 1) :
    D ≤ fixedSpace ρ X := by
  have hcard : Nat.card D = 2 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
    norm_num
  obtain ⟨z, _, hall⟩ := (Nat.card_eq_two_iff' (0 : D)).mp hcard
  intro v hv x
  by_cases hv0 : v = 0
  · simp [hv0]
  · have hvz : (⟨v, hv⟩ : D) = z := hall _ (fun h => hv0 (congrArg Subtype.val h))
    have hx0 : ρ (x : G) v ≠ 0 := by
      intro h
      apply hv0
      exact Representation.GoldschmidtONan.action_injective (ρ := ρ) x
        (h.trans (map_zero _).symm)
    have hxz : (⟨ρ (x : G) v, (hD x.property v).2 hv⟩ : D) = z :=
      hall _ (fun h => hx0 (congrArg Subtype.val h))
    exact congrArg Subtype.val (hxz.trans hvz.symm)

private theorem cubic_invariant_subspace [Finite G] [FiniteDimensional (ZMod 2) V]
    (X : Subgroup G) (hc : Nat.card X = 3)
    (hd : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2)
    (D : Submodule (ZMod 2) V) (hs : X ≤ subspaceStabilizer ρ D)
    (hle : D ≤ subspaceCommutator ρ ⊤ X) :
    D = ⊥ ∨ D = subspaceCommutator ρ ⊤ X := by
  by_cases he : D = subspaceCommutator ρ ⊤ X
  · exact Or.inr he
  left
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hle he)
  have hdle : Module.finrank (ZMod 2) D ≤ 1 := by omega
  by_cases hd0 : Module.finrank (ZMod 2) D = 0
  · exact Submodule.finrank_eq_zero.mp hd0
  have hd1 : Module.finrank (ZMod 2) D = 1 := by omega
  exact le_bot_iff.mp ((le_inf (line_fixed ρ X D hs hd1) hle).trans
    (split ρ X (by rw [hc]; decide)).disjoint.le_bot)


private theorem separation_of_commuting_cubics
    [Finite G] [FiniteDimensional (ZMod 2) V]
    (X Y : Subgroup G) (hcomm : Y ≤ centralizer (X : Set G))
    (hcX : Nat.card X = 3)
    (hdX : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ X) = 2)
    (hdY : Module.finrank (ZMod 2) (subspaceCommutator ρ ⊤ Y) = 2) :
    subspaceCommutator ρ ⊤ X = subspaceCommutator ρ ⊤ Y ∨
      Disjoint (subspaceCommutator ρ ⊤ X) (subspaceCommutator ρ ⊤ Y) ∧
        subspaceCommutator ρ ⊤ X ≤ fixedSpace ρ Y ∧
        subspaceCommutator ρ ⊤ Y ≤ fixedSpace ρ X := by
  let U := subspaceCommutator ρ ⊤ X
  let W := subspaceCommutator ρ ⊤ Y
  have hYX : X ≤ centralizer (Y : Set G) := le_centralizer_iff.mp hcomm
  have htop (A : Subgroup G) : A ≤ subspaceStabilizer ρ ⊤ :=
    le_subspaceStabilizer ρ ⊤ (fun _ _ _ _ => trivial)
  have hYU : Y ≤ subspaceStabilizer ρ U :=
    subspaceCommutator_invariant_normalizer ρ (htop Y)
      (hcomm.trans (centralizer_le_normalizer _))
  have hXW : X ≤ subspaceStabilizer ρ W :=
    subspaceCommutator_invariant_normalizer ρ (htop X)
      (hYX.trans (centralizer_le_normalizer _))
  have hXI : X ≤ subspaceStabilizer ρ (U ⊓ W) := by
    apply le_subspaceStabilizer
    intro x hx v hv
    exact ⟨(subspaceCommutator_invariant ρ ⊤ X hx v).2 hv.1, (hXW hx v).2 hv.2⟩
  rcases cubic_invariant_subspace ρ X hcX hdX (U ⊓ W) hXI inf_le_left with hb | he
  · right
    refine ⟨disjoint_iff.mpr hb, ?_, ?_⟩
    · intro v hv y
      apply sub_eq_zero.mp
      have hm : ρ (y : G) v - v ∈ U ⊓ W :=
        ⟨U.sub_mem ((hYU y.property v).2 hv) hv,
          Submodule.subset_span ⟨y, y.property, v, trivial, rfl⟩⟩
      rw [hb] at hm
      exact hm
    · intro v hv x
      apply sub_eq_zero.mp
      have hm : ρ (x : G) v - v ∈ U ⊓ W :=
        ⟨Submodule.subset_span ⟨x, x.property, v, trivial, rfl⟩,
          W.sub_mem ((hXW x.property v).2 hv) hv⟩
      rw [hb] at hm
      exact hm
  · left
    exact Submodule.eq_of_le_of_finrank_eq
      (he.symm.le.trans inf_le_right) (hdX.trans hdY.symm)

/-- The cubic plane-support special case of Kurzweil–Stellmacher 9.3.5.
The relative subnormality hypotheses place both actors in the three-core;
faithfulness on their at-most-four-dimensional joint support bounds their join
by nine and hence proves commutation. Irreducibility then separates the supports. -/
theorem cubic_support_separation [Finite G] [FiniteDimensional (ZMod 2) V]
    (hρ : Function.Injective ρ) (K : Subgroup G) (hodd : Odd (Nat.card K)) :
    CubicSupportSeparation ρ K := by
  intro X Y hXK hYK hX hY hcX hcY hdX hdY
  have hcomm := cubic_join_commutative ρ hρ K X Y hodd hXK hYK hX hY hcX hcY hdX hdY
  have hXY : Y ≤ centralizer (X : Set G) := by
    intro y hy
    apply mem_centralizer_iff.mpr
    intro x hx
    exact congrArg Subtype.val (hcomm.is_comm.comm
      (⟨x, (le_sup_left : X ≤ X ⊔ Y) hx⟩ : ↥(X ⊔ Y))
      ⟨y, (le_sup_right : Y ≤ X ⊔ Y) hy⟩)
  exact separation_of_commuting_cubics ρ X Y hXY hcX hdX hdY

end CFSG.Quasithin.ChapterB.Glauberman.BlockConstruction
