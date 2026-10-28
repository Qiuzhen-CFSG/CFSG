module
public import CFSG.Quasithin.ChapterG.Section11.LowRank
public import CFSG.Quasithin.ChapterG.Section09.DefiningCharacteristic.G2Recognition.SharpDegree
public import Theory.Representation.G2NaturalInvolutionExclusion
public import CFSG.Quasithin.ClassificationModels.Families

/-!
# Nonbinary whole G₂ components cannot have the strict low-rank involution

The full G.9 automorphism bound puts the irreducible component module in
its natural-degree window. The proved Frobenius parameters and descent
construct genuine natural coordinates. The ambient normalizer theorem then
forces every involution to move at least twice the field degree, contradicting
the source rank-two witness when the field has more than two elements.

`StrictWholeModels` applies the exclusion to the original strict quotient.
Source: Aschbacher--Smith G.9.3(10) and G.11.7, pp.354,356--357,367.
-/

public noncomputable section
open Subgroup Module Representation Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterG.Section11.WholeG2
open Section09.DefiningCharacteristic.G2Recognition
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X L : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X} {C : GroupClass}
  {k : Type*} [Field k] [Finite k] [CharP k 2]
attribute [local instance] ZMod.algebra

/-- The original G.9 action of a normal nonbinary G₂ component is its natural action. -/
theorem natural_of_component
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (e : L ≃* Atlas.G2.Model k) {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) :
    Section09.Quasiequivalent (ρ.comp L.subtype) (naturalBinary k) := by
  let σ := (ρ.comp L.subtype).comp e.symm.toMonoidHom
  let : IsIrreducible σ :=
    (irreducible_comp_surjective_iff e.symm.toMonoidHom e.symm.surjective
      (ρ.comp L.subtype)).mpr h9.irreducible
  have hf : Function.Injective σ := h9.faithful.comp (L.subtype_injective.comp e.symm.injective)
  have hw := actor_bound_of_model_rank h9 e
    (Atlas.G2.EvenTwoRank.source_automorphism_two_rank_le k hn hcard)
  obtain ⟨_,t,l,ht,_,hnt,hdim,hne,hbasic,hnatural⟩ :=
    Nonbinary.exists_basic_parameters_and_natural σ hn hcard hf
  obtain ⟨_,ht1,hb6,_⟩ := small_orbit_parameters (by omega : 0<n) ht
    ((basic_product_alternatives l hbasic).resolve_left hne) hnt hdim hw.2
  obtain ⟨a,f,hf⟩ := hnatural ht1 hb6
  refine ⟨e.trans a,f,?_⟩
  intro g w
  have hh := hf (e g) w
  simpa only [σ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,
    e.symm_apply_apply,MulEquiv.trans_apply,Subgroup.coe_subtype] using hh

/-- Every ambient involution has binary displacement at least four, contrary
 to the original low-rank witness. -/
theorem not_nonbinary
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) (e : L ≃* Atlas.G2.Model k)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card k = 2^n) : False := by
  let := h9.normal_H
  obtain ⟨e,f,hf⟩ := natural_of_component h9 e hn hcard
  obtain ⟨a,_,ho,_,hr,_⟩ := hw.exists_involution h.point_ne_zero
  have hb := Atlas.G2.Natural.Normalizer.ambient_involution_displacement_ge k
    ρ L e f hf h.faithful hn hcard a ho
  change 2*n ≤ finrank (ZMod 2) (RankTwo.movedSpace ρ a) at hb
  omega

/-- Exclusion with the source's actual field and group carrier. -/
theorem not_nonbinary_model
    (h : Section10.Hypothesis ρ B v W X X₀)
    (h9 : Section09.ComponentHypothesis C ρ X L L
      (finrank (ZMod 2) (Additive X)))
    (hw : LowRankWitness ρ v X) {n : ℕ} (hn : 2 ≤ n)
    (model : ClassificationModels.IsG2At L (2^n)) : False := by
  obtain ⟨k,_,_,hcard,⟨e⟩⟩ := model
  let : Fintype k := Fintype.ofFinite k
  let : CharP k 2 := charP_of_card_eq_prime_pow
    (by simpa only [Nat.card_eq_fintype_card] using hcard)
  exact not_nonbinary h h9 hw e hn hcard
end CFSG.Quasithin.ChapterG.Section11.WholeG2
