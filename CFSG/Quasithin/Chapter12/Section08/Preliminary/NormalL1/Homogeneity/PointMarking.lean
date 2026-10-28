module

public import CFSG.Quasithin.Chapter12.Section08.Preliminary.NormalL1.Homogeneity.Actions
public import Theory.LinearAlgebra.BinaryFivePointStabilizer.Quotient
public import Theory.SpecificGroups.BinaryLinear.SmallParabolicLevi.Models
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.SpecificGroups.BinaryLinear.Perfect
public import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# The natural marking of the literal point quotient

The ambient natural marking pulls the full linear point stabilizer back to
L ∩ N_G(V₁). Its action on V/V₁ is onto GL_(n−1)(2) with a two-group kernel.
The actual quotient map identifies V/V₁ with the literal image of V in G₁/V₁.
Surjective residual transport then gives GL_(n−1)(2)′, and its trivial
two-core identifies the restricted kernel with O₂(L₁). All coordinate
changes retain their pointwise compatibility with ambient conjugation.

In dimension three the quotient actor is GL₂(2)′ ≅ C₃. For point index one,
L₁ is always the two-residual, including in dimension five. The argument
works for every n ≥ 3 and requires no separate kernel or quotient premise.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
Notation 12.8.2 and the opening observation in the proof of Lemma 12.8.5,
printed pp.849–850 (PDF pp.866–867). The ambient natural marking remains
an earlier-source input; this module constructs the induced seed marking.
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
  [IsElementaryAbelian 2 (F.tilde V)]

namespace PointMarking
open Theory.LinearAlgebra.BinaryFivePointStabilizer

omit [IsElementaryAbelian 2 (F.tilde V)] in
private theorem seed_le_H : V ≤ F.H :=
  (le_conjugateSpanBy V F.H).trans F.U_le_H

private noncomputable def projection : Additive V →ₗ[ZMod 2] Additive (F.tilde V) :=
  (F.tildeMap V (seed_le_H F)).toAdditive.toZModLinearMap 2

private theorem projection_surjective : Function.Surjective (projection F) := by
  intro v
  obtain ⟨w, hw⟩ := F.tildeMap_surjective V (seed_le_H F) v.toMul
  exact ⟨Additive.ofMul w, congrArg Additive.ofMul hw⟩

private theorem projection_eq_zero (v : Additive V) :
    projection F v = 0 ↔ (v.toMul : G) ∈ F.Vi 1 := by
  change F.tildeMap V (seed_le_H F) v.toMul = 1 ↔ _
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

omit [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 (F.tilde V)] in
private theorem exists_point (hn : 1 ≤ n) :
    ∃ z : Additive V, z ≠ 0 ∧ ∀ v : Additive V,
      (v.toMul : G) ∈ F.Vi 1 ↔ v = 0 ∨ v = z := by
  have hc : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 hn
  obtain ⟨u, hu, hall⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hc
  let z : Additive V := Additive.ofMul ⟨u, F.le_seed 1 u.property⟩
  refine ⟨z, ?_, ?_⟩
  · intro he
    apply hu
    exact Subtype.ext (congrArg (fun v : Additive V => (v.toMul : G)) he)
  · intro v
    constructor
    · intro hv
      by_cases he : v = 0
      · exact Or.inl he
      · right
        have heq := hall ⟨v.toMul, hv⟩ (fun h =>
          he (Additive.toMul.injective (Subtype.ext (congrArg (fun a : F.Vi 1 => (a : G)) h))))
        exact Additive.toMul.injective (Subtype.ext (congrArg (fun a : F.Vi 1 => (a : G)) heq))
    · rintro (rfl | rfl)
      · exact one_mem _
      · exact u.property

private theorem projection_ker (z : Additive V)
    (hz : ∀ v : Additive V, (v.toMul : G) ∈ F.Vi 1 ↔ v = 0 ∨ v = z) :
    (projection F).ker = line z := by
  ext v
  rw [LinearMap.mem_ker, projection_eq_zero, hz]
  constructor
  · rintro (rfl | rfl)
    · exact Submodule.zero_mem _
    · exact Submodule.mem_span_singleton_self _
  · intro hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) a with rfl | rfl <;> simp

private noncomputable def quotientEquiv (z : Additive V)
    (hz : ∀ v : Additive V, (v.toMul : G) ∈ F.Vi 1 ↔ v = 0 ∨ v = z) :
    QuotientSpace z ≃ₗ[ZMod 2] Additive (F.tilde V) :=
  (Submodule.quotEquivOfEq _ _ (projection_ker F z hz).symm).trans
    ((projection F).quotKerEquivOfSurjective (projection_surjective F))

@[simp] private theorem quotientEquiv_mk (z : Additive V)
    (hz : ∀ v : Additive V, (v.toMul : G) ∈ F.Vi 1 ↔ v = 0 ∨ v = z)
    (v : Additive V) : quotientEquiv F z hz ((line z).mkQ v) = projection F v := rfl

end PointMarking
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Subgroup
open scoped IsMulCommutative
open BinaryLinear.SmallParabolicLevi
open Theory.LinearAlgebra.BinaryFivePointStabilizer
variable {G : Type*} [Group G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
variable {L : Subgroup G} {hLV : L ≤ normalizer (V : Set G)}
variable (A : AmbientNaturalMarking L hLV n)
namespace PointMarking

private noncomputable def ambientAction : L →* BinaryLinear.GL (Additive V) :=
  (linearGroupCongr A.coordinates.symm).toMonoidHom.comp
    (A.quotientEquiv.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L)))

private theorem ambientAction_surjective : Function.Surjective (ambientAction A) :=
  (linearGroupCongr A.coordinates.symm).surjective.comp
    (A.quotientEquiv.surjective.comp (QuotientGroup.mk'_surjective _))

private theorem ambientAction_apply (l : L) (v : Additive V) :
    ambientAction A l v = Additive.ofMul ⟨(l : G) * v.toMul * (l : G)⁻¹,
      (mem_normalizer_iff.mp (hLV l.property) v.toMul).mp v.toMul.property⟩ := by
  apply A.coordinates.injective
  exact (A.coordinates.apply_symm_apply _).trans (A.equivariant l v).symm

private theorem ambientAction_ker : (ambientAction A).ker = pCore 2 L := by
  rw [ambientAction, MonoidHom.ker_comp_of_injective _ _
    (linearGroupCongr A.coordinates.symm).injective,
    MonoidHom.ker_comp_of_injective _ _ A.quotientEquiv.injective, QuotientGroup.ker_mk']

variable (z : Additive V) (hz0 : z ≠ 0)
variable (hz : ∀ v : Additive V, (v.toMul : G) ∈ F.Vi 1 ↔ v = 0 ∨ v = z)

include hz0 hz in
private theorem mem_pointNormalizer_iff (l : L) :
    (l : G) ∈ F.H ↔ ambientAction A l z = z := by
  constructor
  · intro hl
    have hmem : ((ambientAction A l z).toMul : G) ∈ F.Vi 1 := by
      rw [ambientAction_apply]
      exact (mem_normalizer_iff.mp hl z.toMul).mp ((hz z).mpr (Or.inr rfl))
    rcases (hz _).mp hmem with hzero | heq
    · exact False.elim (hz0 ((ambientAction A l).map_eq_zero_iff.mp hzero))
    · exact heq
  · intro hl
    apply mem_normalizer_iff.mpr
    intro x
    constructor
    · intro hx
      have hxV := F.le_seed 1 hx
      let v : Additive V := Additive.ofMul ⟨x, hxV⟩
      have hv := (hz v).mp hx
      have hm : ((ambientAction A l v).toMul : G) ∈ F.Vi 1 := by
        apply (hz _).mpr
        rcases hv with hv | hv
        · exact Or.inl (by rw [hv, map_zero])
        · exact Or.inr (by rw [hv, hl])
      rw [ambientAction_apply] at hm
      exact hm
    · intro hx
      have hxV : x ∈ V :=
        (mem_normalizer_iff.mp (hLV l.property) x).mpr (F.le_seed 1 hx)
      let v : Additive V := Additive.ofMul ⟨x, hxV⟩
      have hm : ((ambientAction A l v).toMul : G) ∈ F.Vi 1 := by
        rw [ambientAction_apply]
        exact hx
      apply (hz v).mpr
      rcases (hz _).mp hm with he | he
      · exact Or.inl ((ambientAction A l).map_eq_zero_iff.mp he)
      · exact Or.inr ((ambientAction A l).injective (he.trans hl.symm))

private noncomputable def stabilizerMap : (L ⊓ F.H : Subgroup G) →* stabilizer z :=
  ((ambientAction A).comp (inclusion inf_le_left)).codRestrict _
    (fun l => (mem_pointNormalizer_iff F A z hz0 hz ⟨l, l.property.1⟩).mp l.property.2)

private theorem stabilizerMap_surjective :
    Function.Surjective (stabilizerMap F A z hz0 hz) := by
  intro g
  obtain ⟨l, hl⟩ := ambientAction_surjective A g.val
  refine ⟨⟨l, l.property, ?_⟩, Subtype.ext hl⟩
  apply (mem_pointNormalizer_iff F A z hz0 hz l).mpr
  rw [hl]
  exact g.property

private theorem stabilizerMap_ker_isPGroup : IsPGroup 2 (stabilizerMap F A z hz0 hz).ker := by
  let f : (stabilizerMap F A z hz0 hz).ker →* (ambientAction A).ker :=
    { toFun k := ⟨⟨k.val, k.val.property.1⟩, congrArg Subtype.val k.property⟩
      map_one' := rfl
      map_mul' _ _ := rfl }
  have hp : IsPGroup 2 (ambientAction A).ker := by
    rw [ambientAction_ker]
    exact pCore_isPGroup
  apply hp.of_injective f
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun a : (ambientAction A).ker =>
    ((a : L) : G)) h))

end PointMarking
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag.PointMarking
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi

private theorem symmetricThree_residual :
    pResidual 2 (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  apply le_antisymm
  · apply sInf_le
    refine ⟨inferInstance, IsPGroup.of_card (n := 1) ?_⟩
    change (alternatingGroup (Fin 3)).index = 2 ^ 1
    simp
  · intro x hx
    have hc : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [nat_card_alternatingGroup, Nat.card_fin]
      rfl
    have hp : x ^ 3 = 1 := congrArg Subtype.val
      (hc ▸ pow_card_eq_one' (x := (⟨x, hx⟩ : alternatingGroup (Fin 3))))
    exact mem_pResidual_of_orderOf_coprime
      ((by decide : Nat.Coprime 2 3).of_dvd_right (orderOf_dvd_of_pow_eq_one hp))

private theorem symmetricThree_commutator :
    commutator (Equiv.Perm (Fin 3)) = alternatingGroup (Fin 3) := by
  apply le_antisymm
  · exact Abelianization.commutator_subset_ker Equiv.Perm.sign
  · intro g hg
    have h : ∀ g : Equiv.Perm (Fin 3), Equiv.Perm.sign g = 1 →
        ∃ a b : Equiv.Perm (Fin 3), ⁅a,b⁆ = g := by decide +kernel
    obtain ⟨a, b, rfl⟩ := h g hg
    exact commutator_mem_commutator (mem_top _) (mem_top _)

private theorem perfect_residual_top {K : Type*} [Group K] [Finite K]
    [Group.IsPerfect K] : pResidual 2 K = ⊤ := by
  apply (pResidual_eq_top_iff 2 K).mpr
  intro N hN hq
  let : N.Normal := hN
  by_contra hne
  let : Nontrivial (K ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
  let : Group.IsPerfect (K ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  let : Group.IsNilpotent (K ⧸ N) := hq.isNilpotent
  exact Group.IsPerfect.not_isSolvable (K ⧸ N) inferInstance

/-- The binary quotient actor retains its derived-group convention in dimension two. -/
private theorem linear_residual (m : ℕ) (hm : 2 ≤ m) :
    pResidual 2 (LinearGroup m) = commutator (LinearGroup m) := by
  let : Finite (LinearGroup m) := Finite.of_injective
    (fun g : LinearGroup m => (g : Space m → Space m)) DFunLike.coe_injective
  by_cases h3 : 3 ≤ m
  · let : Group.IsPerfect (LinearGroup m) := BinaryLinear.linearGroup_isPerfect m h3
    rw [perfect_residual_top, Group.IsPerfect.commutator_eq_top]
  · have hm2 : m = 2 := by omega
    subst m
    apply Subgroup.map_injective (f := linearTwoEquivSymmetricThree.toMonoidHom)
      linearTwoEquivSymmetricThree.injective
    rw [Subgroup.map_pResidual, symmetricThree_residual, _root_.map_commutator_eq,
      MonoidHom.range_eq_top_of_surjective _ linearTwoEquivSymmetricThree.surjective,
      ← _root_.commutator_def, symmetricThree_commutator]

/-- The derived binary quotient actor has no nontrivial normal two-subgroup. -/
private theorem linear_derived_core (m : ℕ) : pCore 2 (commutator (LinearGroup m)) = ⊥ := by
  have h : (pCore 2 (commutator (LinearGroup m))).map
      (commutator (LinearGroup m)).subtype ≤ pCore 2 (LinearGroup m) :=
    le_sSup ⟨inferInstance, pCore_isPGroup.map _⟩
  rw [linearGroup_twoCore_eq_bot] at h
  apply (Subgroup.eq_bot_iff_forall _).mpr
  intro x hx
  apply Subtype.ext
  exact h (mem_map.mpr ⟨x, hx, rfl⟩)

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag.PointMarking

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Subgroup
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic BinaryLinear.SmallParabolicLevi
open Theory.LinearAlgebra.BinaryFivePointStabilizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
  [IsElementaryAbelian 2 (F.tilde V)]
variable {L : Subgroup G} {hLV : L ≤ normalizer (V : Set G)}
namespace PointMarking

/-- The full point normalizer acts as the full linear group on the literal
quotient seed, with two-group kernel. -/
private theorem exists_normalizer_action (hn : 1 ≤ n) (A : AmbientNaturalMarking L hLV n) :
    ∃ c : Additive (F.tilde V) ≃ₗ[ZMod 2] Space (n - 1),
    ∃ f : (L ⊓ F.H : Subgroup G) →* LinearGroup (n - 1),
      Function.Surjective f ∧ IsPGroup 2 f.ker ∧
      ∀ (k : (L ⊓ F.H : Subgroup G)) (v : Additive (F.tilde V)),
        c (Additive.ofMul (F.tildeAction (L ⊓ F.H) V inf_le_right
          (inf_le_left.trans hLV) k v.toMul)) = f k (c v) := by
  obtain ⟨z, hz0, hz⟩ := exists_point F hn
  let e := PointMarking.quotientEquiv F z hz
  have hdim : Module.finrank (ZMod 2) (QuotientSpace z) = n - 1 := by
    have hd := (line z).finrank_quotient_add_finrank
    change Module.finrank (ZMod 2) (QuotientSpace z) +
      Module.finrank (ZMod 2) (line z) = Module.finrank (ZMod 2) (Additive V) at hd
    have hv : Module.finrank (ZMod 2) (Additive V) = n :=
      A.coordinates.finrank_eq.trans (by simp)
    have hl := finrank_span_singleton (K := ZMod 2) hz0
    change Module.finrank (ZMod 2) (line z) = 1 at hl
    rw [hl, hv] at hd
    omega
  let b : QuotientSpace z ≃ₗ[ZMod 2] Space (n - 1) :=
    LinearEquiv.ofFinrankEq _ _ (by simpa only [Space, Module.finrank_pi, Fintype.card_fin] using hdim)
  let c := e.symm.trans b
  let s := stabilizerMap F A z hz0 hz
  let f : (L ⊓ F.H : Subgroup G) →* LinearGroup (n - 1) :=
    (linearGroupCongr b).toMonoidHom.comp ((quotientAction z).comp s)
  have hf : Function.Surjective f := (linearGroupCongr b).surjective.comp
    ((quotientAction_surjective z).comp (stabilizerMap_surjective F A z hz0 hz))
  have hk : IsPGroup 2 f.ker := by
    dsimp only [f]
    rw [MonoidHom.ker_comp_of_injective _ _ (linearGroupCongr b).injective,
      ← MonoidHom.comap_ker]
    exact (IsElementaryAbelian.isPGroup 2 (kernel z)).comap_of_ker_isPGroup s
      (stabilizerMap_ker_isPGroup F A z hz0 hz)
  refine ⟨c, f, hf, hk, ?_⟩
  intro k v
  obtain ⟨w, rfl⟩ := projection_surjective F v
  have he (w : Additive V) : e.symm (projection F w) = (line z).mkQ w := by
    rw [← quotientEquiv_mk F z hz w]
    exact e.symm_apply_apply _
  have hp : Additive.ofMul (F.tildeAction (L ⊓ F.H) V inf_le_right
      (inf_le_left.trans hLV) k (projection F w).toMul) =
      projection F (ambientAction A ⟨k, k.property.1⟩ w) := by
    rw [ambientAction_apply]
    exact congrArg Additive.ofMul (F.tildeAction_apply_map (L ⊓ F.H) V inf_le_right
      (seed_le_H F) (inf_le_left.trans hLV) k w.toMul)
  rw [hp]
  dsimp only [c, f, LinearEquiv.trans_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom]
  rw [linearGroupCongr_apply, he, LinearEquiv.symm_apply_apply, he,
    Theory.LinearAlgebra.BinaryFivePointStabilizer.quotientAction_mk]
  rfl

end PointMarking
end CFSG.Quasithin.Chapter12.Section08.InvariantFlag

namespace CFSG.Quasithin.Chapter12.Section08.InvariantFlag
open Subgroup
open scoped IsMulCommutative
open BinaryLinear.OuterCyclic
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {V : Subgroup G} {n : ℕ}
variable (F : InvariantFlag T V n) [IsElementaryAbelian 2 V]
  [IsElementaryAbelian 2 (F.tilde V)]

/-- The ambient natural marking induces the natural marking of the literal point
quotient. The actor is the derived linear group, including the cyclic-three
actor when n=3. This is the opening observation in the proof of 12.8.5. -/
theorem naturalSeedMarking_of_ambient (hn : 3 ≤ n) (L : Subgroup G)
    (hLV : L ≤ normalizer (V : Set G)) (A : AmbientNaturalMarking L hLV n) :
    Nonempty (F.NaturalSeedMarking L hLV) := by
  obtain ⟨c, f, hf, hk, hc⟩ := PointMarking.exists_normalizer_action F (by omega) A
  let N : Subgroup G := L ⊓ F.H
  let R := pResidual 2 N
  let D := commutator (LinearGroup (n - 1))
  have hLi : F.Li L 1 = R.map N.subtype := by
    unfold Li
    rw [if_neg (by omega)]
    rfl
  have hmap : R.map f = D := by
    rw [map_pResidual_of_surjective 2 f hf, PointMarking.linear_residual _ (by omega)]
  have hLN : F.Li L 1 ≤ N := F.Li_le L 1
  let g₀ : F.Li L 1 →* LinearGroup (n - 1) := f.comp (inclusion hLN)
  have hgD (k : F.Li L 1) : g₀ k ∈ D := by
    have hm : (k : G) ∈ R.map N.subtype := by rw [← hLi]; exact k.property
    obtain ⟨r, hr, he⟩ := mem_map.mp hm
    rw [← hmap]
    refine mem_map.mpr ⟨r, hr, ?_⟩
    exact congrArg f (Subtype.ext he)
  let g : F.Li L 1 →* D := g₀.codRestrict D hgD
  have hg : Function.Surjective g := by
    intro d
    have hm : (d : LinearGroup (n - 1)) ∈ R.map f := by rw [hmap]; exact d.property
    obtain ⟨r, hr, he⟩ := mem_map.mp hm
    let k : F.Li L 1 := ⟨r, by rw [hLi]; exact mem_map.mpr ⟨r, hr, rfl⟩⟩
    exact ⟨k, Subtype.ext he⟩
  have hkg : IsPGroup 2 g.ker := by
    dsimp only [g, g₀]
    rw [MonoidHom.ker_codRestrict, ← MonoidHom.comap_ker]
    exact hk.comap_of_injective (inclusion hLN) (inclusion_injective hLN)
  let : Finite (LinearGroup (n - 1)) := Finite.of_injective
    (fun g : LinearGroup (n - 1) => (g : Space (n - 1) → Space (n - 1))) DFunLike.coe_injective
  have hker : g.ker = pCore 2 (F.Li L 1) := by
    have he := g.comap_pCore_of_ker_isPGroup hg hkg
    rw [PointMarking.linear_derived_core] at he
    exact he
  let e : (F.Li L 1 ⧸ pCore 2 (F.Li L 1)) ≃* D :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg)
  refine ⟨⟨e, c, ?_⟩⟩
  intro k v
  exact hc (inclusion hLN k) v

end CFSG.Quasithin.Chapter12.Section08.InvariantFlag
