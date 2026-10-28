module

public import Theory.GroupTheory.GeneralizedFitting.ComponentCalculus
public import Theory.SpecificGroups.PSL2.PrimeFieldTwoRank
public import Theory.GroupTheory.PrimeRankElementary
public import Theory.Representation.BinaryOffender.Defs
public import Mathlib.LinearAlgebra.Projectivization.PSL.PSL2

/-!
# Commutators and elementary rank in SL₂(7) central products

The exact overlap with the two-core identifies the component centralizer and
identifies the quotient with the literal matrix PSL₂(7). Quasisimple component
calculus gives the full commutator with every subgroup outside the core.
An elementary subgroup disjoint from the core injects into that quotient, whose
two-rank is two; its order is at most four and its binary rank at most two.

These are group-theoretic ingredients for the offender reduction motivated by
Aschbacher–Smith, C.1.31–34, printed pp.135–137, and B.2.3–5, pp.75–76.
No representation-theoretic classification is used.
-/

public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Representation.BinaryOffender.SL2SevenCentralProduct
local instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private instance sl7_quasisimple : IsQuasisimple SL(2, ZMod 7) where
  toIsPerfect := ⟨Matrix.SL2.commutator_eq_top (a := (2 : ZMod 7)) (by decide) (by decide)⟩
  simple := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (F := ZMod 7) (by norm_num)

variable {H : Type*} [Group H]

/-- The centralizer of the embedded component is precisely the two-core. -/
theorem centralizer_range_eq_pCore (f : SL(2, ZMod 7) →* H)
    (hf : Function.Injective f)
    (hc : ⁅pCore 2 H, f.range⁆ = ⊥)
    (hs : pCore 2 H ⊔ f.range = ⊤)
    (hz : (pCore 2 H).comap f = center SL(2, ZMod 7)) :
    centralizer (f.range : Set H) = pCore 2 H := by
  have hp := commutator_eq_bot_iff_le_centralizer.mp hc
  apply le_antisymm ?_ hp
  intro a ha
  obtain ⟨p, hpp, l, ⟨x, rfl⟩, rfl⟩ :=
    mem_sup_of_normal_left.mp (show a ∈ pCore 2 H ⊔ f.range by rw [hs]; trivial)
  have hx : f x ∈ centralizer (f.range : Set H) := by
    simpa using (centralizer (f.range : Set H)).mul_mem
      ((centralizer (f.range : Set H)).inv_mem (hp hpp)) ha
  have hxc : x ∈ center SL(2, ZMod 7) := by
    apply mem_center_iff.mpr
    intro y
    apply hf
    simpa only [map_mul] using mem_centralizer_iff.mp hx (f y) ⟨y, rfl⟩
  exact (pCore 2 H).mul_mem hpp (show f x ∈ pCore 2 H by
    change x ∈ (pCore 2 H).comap f
    rwa [hz])

/-- The component factor is normal in the generated central product. -/
theorem range_normal (f : SL(2, ZMod 7) →* H)
    (hc : ⁅pCore 2 H, f.range⁆ = ⊥)
    (hs : pCore 2 H ⊔ f.range = ⊤) : f.range.Normal := by
  apply normalizer_eq_top_iff.mp
  apply top_unique
  rw [← hs]
  exact sup_le ((commutator_eq_bot_iff_le_centralizer.mp hc).trans
    (Subgroup.centralizer_le_normalizer _)) f.range.le_normalizer

/-- Every subgroup outside the core has full commutator with the component. -/
theorem commutator_range_eq (f : SL(2, ZMod 7) →* H)
    (hf : Function.Injective f)
    (hc : ⁅pCore 2 H, f.range⁆ = ⊥)
    (hs : pCore 2 H ⊔ f.range = ⊤)
    (hz : (pCore 2 H).comap f = center SL(2, ZMod 7))
    (A : Subgroup H) (hA : ¬ A ≤ pCore 2 H) : ⁅f.range, A⁆ = f.range := by
  let : f.range.Normal := range_normal f hc hs
  let : IsQuasisimple f.range := IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hf)
  have hL : IsComponent H f.range := ⟨(inferInstance : f.range.Normal).isSubnormal,
    inferInstance⟩
  rcases hL.commutator_dichotomy A with hb | he
  · have h := commutator_eq_bot_iff_le_centralizer.mp (commutator_comm f.range A ▸ hb)
    rw [centralizer_range_eq_pCore f hf hc hs hz] at h
    exact (hA h).elim
  · exact le_antisymm (commutator_le_left _ _)
      ((le_iSup_conjugates f.range A).trans he.symm.le)

/-- The exact overlap identifies the quotient with the matrix PSL₂(7). -/
noncomputable def quotientEquivPSL (f : SL(2, ZMod 7) →* H)
    (hs : pCore 2 H ⊔ f.range = ⊤)
    (hz : (pCore 2 H).comap f = center SL(2, ZMod 7)) :
    (H ⧸ pCore 2 H) ≃* PSL(2, ZMod 7) := by
  let q := QuotientGroup.mk' (pCore 2 H)
  let g := q.comp f
  have hg : Function.Surjective g := by
    intro a
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) a
    obtain ⟨p, hpp, l, ⟨x, rfl⟩, rfl⟩ :=
      mem_sup_of_normal_left.mp (show a ∈ pCore 2 H ⊔ f.range by rw [hs]; trivial)
    refine ⟨x, ?_⟩
    change q (f x) = q (p * f x)
    rw [map_mul, show q p = 1 from (QuotientGroup.eq_one_iff p).mpr hpp, one_mul]
  have hk : g.ker = center SL(2, ZMod 7) := by
    change (q.comp f).ker = _
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hz
  exact ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)).symm


/-- An elementary subgroup disjoint from the core has order at most four. -/
theorem elementary_card_le_four (f : SL(2, ZMod 7) →* H)
    (hs : pCore 2 H ⊔ f.range = ⊤)
    (hz : (pCore 2 H).comap f = center SL(2, ZMod 7))
    (B : Subgroup H) [IsElementaryAbelian 2 B] (hB : B ⊓ pCore 2 H = ⊥) :
    Nat.card B ≤ 4 := by
  let e := quotientEquivPSL f hs hz
  let q := QuotientGroup.mk' (pCore 2 H)
  let k := e.toMonoidHom.comp q
  have hi : Function.Injective (k.subgroupMap B) := by
    apply (k.subgroupMap B).ker_eq_bot_iff.mp
    apply bot_unique
    intro b hb
    apply Subtype.ext
    have he0 : k (b : H) = 1 :=
      congrArg (fun t : B.map k => (t : PSL(2, ZMod 7))) (MonoidHom.mem_ker.mp hb)
    have he : e (q (b : H)) = e 1 := he0.trans (map_one e).symm
    have hp : (b : H) ∈ pCore 2 H :=
      (QuotientGroup.eq_one_iff _).mp (e.injective he)
    have hb' : (b : H) ∈ B ⊓ pCore 2 H := ⟨b.property, hp⟩
    simpa [hB] using hb'
  have hcard : Nat.card B ≤ Nat.card (B.map k) := Nat.card_le_card_of_injective _ hi
  have hr := (primeRank_le_iff_elementary_card_le PSL(2, ZMod 7)).mp
    (Theory.PSL2.primeField_two_rank (p := 7) (by decide)).le
    (B.map k) (IsElementaryAbelian.map k)
  exact hcard.trans hr

/-- The logarithmic binary rank of a disjoint elementary subgroup is at most two. -/
theorem elementary_rank_le_two (f : SL(2, ZMod 7) →* H)
    (hs : pCore 2 H ⊔ f.range = ⊤)
    (hz : (pCore 2 H).comap f = center SL(2, ZMod 7))
    (B : Subgroup H) [IsElementaryAbelian 2 B] (hB : B ⊓ pCore 2 H = ⊥) :
    rank B ≤ 2 := by
  exact (Nat.log_mono_right (b := 2) (elementary_card_le_four f hs hz B hB)).trans
    (by decide)
end Representation.BinaryOffender.SL2SevenCentralProduct
