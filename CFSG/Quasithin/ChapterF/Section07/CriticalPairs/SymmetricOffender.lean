module

public import CFSG.Quasithin.ChapterF.Section07.CriticalPairs.SourceAction
public import Mathlib.LinearAlgebra.Quotient.Card

/-!
# The symmetric offender argument for an even critical pair

The image of A in the literal quotient G₁/C_G₁(V) has binary rank
log₂ |A:C_A(V)|. Counting the actual fixed vectors identifies its fixed
codimension with log₂ |V:C_V(A)|. Only G₁ needs to be finite.

For the conjugate pair V, Vᵍ, pull the reverse orientation back by g⁻¹.
Both resulting actors lie in G₁ and act on the same intrinsic V through the
same faithful quotient. The conjugation equivalence reverses the two
centralizer indices. If neither image were an offender, those indices would
satisfy opposing strict inequalities. The critical-pair theorem supplies
noncommutation and both vertex containments, proving the even case of
F.7.11(7) with no additional source premise.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), F.7.11(7),
printed pp.313–314 (PDF pp.324–325). The counting argument follows the local
rank calculation of E.3.11, without its full-ambient automizer.
-/

@[expose] public section

open Subgroup
open scoped IsMulCommutative
open Subgroup.CosetGeometry.RankTwo
open CFSG.Quasithin.ChapterF.Section07.Track
open Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterF.Section07.CriticalPairs.SymmetricOffender
open SourceAction
variable {G : Type*} [Group G] {F : Bool → Subgroup G} (D : SourceSetup F)
local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
local instance : IsElementaryAbelian 2 D.V := D.reduced.elementary
local instance : D.V.Normal := D.reduced.normal

private theorem centralizer_seed_comap :
    (centralizer (D.seed : Set G)).comap (F false).subtype =
      centralizer (D.V : Set (F false)) := by
  ext a
  constructor
  · intro h x hx
    apply Subtype.ext
    exact h (x : G) (mem_map_of_mem (F false).subtype hx)
  · intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact congrArg Subtype.val (h y hy)

private abbrev quotientImage (A : Subgroup G) :=
  (A.subgroupOf (F false)).map
    (QuotientGroup.mk' (centralizer (D.V : Set (F false))))

private theorem rank_quotientImage (A : Subgroup G) (hA : A ≤ F false) :
    rank (quotientImage D A) = Nat.log 2 ((centralizer (D.seed : Set G)).relIndex A) := by
  unfold rank quotientImage
  rw [← relIndex_ker, QuotientGroup.ker_mk', ← centralizer_seed_comap D,
    relIndex_comap, map_subgroupOf_eq_of_le hA]

private theorem mem_fixedSpace_quotientImage (A : Subgroup G) (hA : A ≤ F false)
    (x : Additive D.V) :
    x ∈ fixedSpace (faithfulRepresentation D) (quotientImage D A) ↔
      ((x.toMul : F false) : G) ∈ centralizer (A : Set G) := by
  constructor
  · intro h a ha
    have he := h ⟨QuotientGroup.mk' (centralizer (D.V : Set (F false))) ⟨a, hA ha⟩,
      mem_map_of_mem _ (show (⟨a, hA ha⟩ : F false) ∈ A.subgroupOf (F false) from ha)⟩
    have he' := congrArg (fun w : Additive D.V => ((w.toMul : F false) : G)) he
    change a * ((x.toMul : F false) : G) * a⁻¹ = ((x.toMul : F false) : G) at he'
    exact mul_inv_eq_iff_eq_mul.mp he'
  · intro h a
    obtain ⟨b, hb, hab⟩ := a.property
    change faithfulRepresentation D (a : _) x = x
    rw [← hab, faithfulRepresentation_mk]
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Subtype.ext
    change (b : G) * ((x.toMul : F false) : G) * (b : G)⁻¹ = _
    rw [h b hb, mul_inv_cancel_right]

private noncomputable def fixedSpaceEquiv (A : Subgroup G) (hA : A ≤ F false) :
    fixedSpace (faithfulRepresentation D) (quotientImage D A) ≃
      (((centralizer (A : Set G)).comap (F false).subtype).subgroupOf D.V) where
  toFun x := ⟨x.val.toMul, (mem_fixedSpace_quotientImage D A hA x.val).mp x.property⟩
  invFun x := ⟨Additive.ofMul x.val, (mem_fixedSpace_quotientImage D A hA _).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem fixedCodim_quotientImage (A : Subgroup G) (hA : A ≤ F false) :
    fixedCodim (faithfulRepresentation D) (quotientImage D A) =
      Nat.log 2 ((centralizer (A : Set G)).relIndex D.seed) := by
  let : Finite (F false) := D.finite false
  let C := ((centralizer (A : Set G)).comap (F false).subtype).subgroupOf D.V
  let W := fixedSpace (faithfulRepresentation D) (quotientImage D A)
  have hc : Nat.card W = Nat.card C := Nat.card_congr (fixedSpaceEquiv D A hA)
  have h1 := Submodule.card_eq_card_quotient_mul_card W
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup C
  have hq : Nat.card (Additive D.V ⧸ W) = Nat.card (D.V ⧸ C) := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := C))
    calc
      _ = Nat.card (Additive D.V) := by rw [← hc, mul_comm, ← h1]
      _ = Nat.card D.V := rfl
      _ = _ := h2
  have hv := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive D.V ⧸ W)
  rw [Nat.card_zmod] at hv
  rw [show D.seed = D.V.map (F false).subtype from rfl, ← relIndex_comap,
    relIndex, index_eq_card, ← hq, hv, Nat.log_pow (by decide)]
  rfl

private theorem quotientImage_ne_bot (A : Subgroup G) (hA : A ≤ F false)
    (hc : ⁅D.seed, A⁆ ≠ ⊥) : quotientImage D A ≠ ⊥ := by
  intro h
  have hle := (Subgroup.map_eq_bot_iff _).mp h
  rw [QuotientGroup.ker_mk', ← centralizer_seed_comap D] at hle
  apply hc
  rw [commutator_comm, commutator_eq_bot_iff_le_centralizer]
  intro a ha
  exact hle (show (⟨a, hA ha⟩ : F false) ∈ A.subgroupOf (F false) from ha)

private theorem index_lt_of_not_ff (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hA : A ≤ F false) (hc : ⁅D.seed, A⁆ ≠ ⊥) (hn : ¬ IsFF D) :
    Nat.log 2 ((centralizer (D.seed : Set G)).relIndex A) <
      Nat.log 2 ((centralizer (A : Set G)).relIndex D.seed) := by
  rw [← rank_quotientImage D A hA, ← fixedCodim_quotientImage D A hA]
  apply Nat.lt_of_not_ge
  intro h
  let : IsElementaryAbelian 2 (A.subgroupOf (F false)) := IsElementaryAbelian.subgroupOf hA
  exact hn ⟨quotientImage D A, ⟨quotientImage_ne_bot D A hA hc,
    IsElementaryAbelian.map _⟩, h⟩

private theorem centralizer_map_equiv (A : Subgroup G) (e : G ≃* G) :
    (centralizer (A : Set G)).map e.toMonoidHom =
      centralizer (A.map e.toMonoidHom : Set G) := by
  apply le_antisymm
  · exact map_centralizer_le_centralizer_image _ _
  · intro x hx
    refine ⟨e.symm x, ?_, e.apply_symm_apply x⟩
    intro y hy
    apply e.injective
    simpa only [map_mul, e.apply_symm_apply] using hx (e y) (mem_map_of_mem _ hy)

private theorem centralizer_relIndex_map (A B : Subgroup G) (e : G ≃* G) :
    (centralizer (B.map e.toMonoidHom : Set G)).relIndex (A.map e.toMonoidHom) =
      (centralizer (B : Set G)).relIndex A := by
  rw [← centralizer_map_equiv, relIndex_map_map_of_injective _ _ e.injective]

/-- The symmetric offender calculation in the literal first-vertex quotient.
The reverse pair is carried by the inverse conjugator into the same vertex
and seed, reversing the two centralizer indices. -/
theorem isFF_of_conjugate_pair (g : G)
    (hleft : D.seed.map (MulAut.conj g).toMonoidHom ≤ F false)
    (hright : D.seed ≤ (F false).map (MulAut.conj g).toMonoidHom)
    (hc : ⁅D.seed, D.seed.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥) : IsFF D := by
  classical
  let e : G ≃* G := MulAut.conj g
  let W := D.seed.map e.toMonoidHom
  let U := D.seed.map e.symm.toMonoidHom
  let : IsElementaryAbelian 2 D.seed := IsElementaryAbelian.map (F false).subtype
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.map _
  have hcancel (A : Subgroup G) :
      (A.map e.toMonoidHom).map e.symm.toMonoidHom = A := by
    simp [map_map]
  have hU : U ≤ F false := by
    have h := map_mono (f := e.symm.toMonoidHom) hright
    rwa [hcancel] at h
  have hW : W.map e.symm.toMonoidHom = D.seed := hcancel _
  have hc' : ⁅D.seed, U⁆ ≠ ⊥ := by
    intro h
    have he : (⁅D.seed, W⁆).map e.symm.toMonoidHom = ⊥ := by
      rw [map_commutator, hW, commutator_comm]
      exact h
    exact hc ((map_eq_bot_iff_of_injective _ e.symm.injective).mp he)
  by_contra hn
  have h1 := index_lt_of_not_ff D W hleft hc hn
  have h2 := index_lt_of_not_ff D U hU hc' hn
  have hswap1 := centralizer_relIndex_map D.seed W e.symm
  have hswap2 := centralizer_relIndex_map W D.seed e.symm
  rw [hW] at hswap1 hswap2
  change (centralizer (D.seed : Set G)).relIndex U = _ at hswap1
  change (centralizer (U : Set G)).relIndex D.seed = _ at hswap2
  rw [hswap1, hswap2] at h2
  exact Nat.lt_asymm h1 h2

/-- F.7.11(7), the even-critical-pair implication: the genuine source action
on the intrinsic V is an FF-module for G₁/C_G₁(V). -/
theorem even_critical_pair_isFF (hne : D.V ≠ ⊥) {v : Vertex F}
    (hd : (graph F).dist (base F false) v = D.track hne)
    (hb : Even (D.track hne)) (hcritical : ¬ D.seed ≤ ballKernel F v 1) :
    IsFF D := by
  have hv := even_endpoint_type F D hne hd hb
  obtain ⟨g, hg⟩ := Subgroup.CosetGeometry.exists_smul_base F v
  rw [hv] at hg
  have hm : vertexModule F D.seed v = D.seed.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, vertexModule_translate_base F D.seed D.seed_normalized]
  have hpair := SourceAction.even_critical_pair D hne hd hb hcritical
  have hright : D.seed ≤ stabilizer F v := by
    have h := firstModule_le_stabilizer_at_dist_le F D hne
      (a := base F false) rfl hd.le
    rwa [firstModule_base F D.seed D.seed_normalized] at h
  rw [← hg, stabilizer_translate,
    show stabilizer F (base F false) = F false from
      Subgroup.CosetGeometry.stabilizer_base F false] at hright
  apply isFF_of_conjugate_pair D g
  · rw [← hm]
    exact hpair.2.2.1
  · exact hright
  · rw [← hm]
    exact hpair.1

end CFSG.Quasithin.ChapterF.Section07.CriticalPairs.SymmetricOffender
