module
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.J2.OuterInvolutionCentralizer.PermutationComparison
public import Theory.GroupTheory.SolvableOuterQuotient
public import Theory.SpecificGroups.PSL3Two.Parabolics.Actions
public import Theory.SpecificGroups.PSL3Two.Automorphisms
import Mathlib.Tactic.FinCases

/-!
# Native J₂ outer fixed-subgroup comparison

The actual fourteen-point fixed-subgroup model is matched to the natural and
contragredient actions of `SL₃(2)` on the two seven-point orbits. The two
literal matrix generators have orders 7 and 4, with product of order 3;
these orders and simplicity force generation of `SL₃(2)`. Four checked
stabilizer words give a trivial ambient centralizer, so conjugation identifies
the complete order-336 model with `Aut(PSL₃(2))`.

This is a native comparison of the retained ATLAS representative, with no
model-comparison callback. The existing outer-involution fusion theorem then
transports the fixed-subgroup equivalence to every outer involution.
Source: GLS3 Table 5.3g, class 2C; Aschbacher–Smith 16.1.5(8), p.1172.
-/

@[expose] public section
namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.LinearModel
open Matrix.PSL3Two Matrix.PSL3Two.Fano

def vector (i : Fin 8) : Vector :=
  ![(if i.val % 2 = 0 then 0 else 1),
    (if i.val / 2 % 2 = 0 then 0 else 1), (if i.val < 4 then 0 else 1)]
def code (v : Vector) : Fin 8 :=
  ⟨(v 0).val + 2 * (v 1).val + 4 * (v 2).val, by
    have := (v 0).val_lt; have := (v 1).val_lt; have := (v 2).val_lt; omega⟩
def point (i : Fin 7) : Point :=
  ⟨vector ⟨i.val + 1, by omega⟩, by
    have h : ∀ j : Fin 7, vector ⟨j.val+1,by omega⟩ ≠ 0 := by decide +kernel
    exact h i⟩

def vertexMap : Fin 14 → Point ⊕ Line :=
  ![Sum.inl (point 0), Sum.inr ⟨point 6⟩, Sum.inr ⟨point 2⟩,
    Sum.inl (point 1), Sum.inl (point 3), Sum.inl (point 4),
    Sum.inr ⟨point 4⟩, Sum.inr ⟨point 5⟩, Sum.inr ⟨point 1⟩,
    Sum.inr ⟨point 3⟩, Sum.inr ⟨point 0⟩, Sum.inl (point 5),
    Sum.inl (point 2), Sum.inl (point 6)]
def vertexIndex : Point ⊕ Line → Fin 14
  | .inl p => ![0,0,3,12,4,5,11,13] (code p.val)
  | .inr l => ![0,10,8,2,9,6,7,1] (code l.normal.val)

def vertices : Fin 14 ≃ Point ⊕ Line where
  toFun := vertexMap
  invFun := vertexIndex
  left_inv := by decide +kernel
  right_inv := by
    have hl : Function.LeftInverse vertexIndex vertexMap := by decide +kernel
    have hs : Function.Surjective vertexMap :=
      ((Nat.bijective_iff_injective_and_card vertexMap).mpr ⟨hl.injective, by
        simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_sum,
          card_point, card_line]⟩).2
    exact hl.rightInverse_of_surjective hs

noncomputable def action : SL →* Equiv.Perm (Fin 14) :=
  vertices.symm.permCongrHom.toMonoidHom.comp
    ((Equiv.Perm.sumCongrHom Point Line).comp
      ((MulAction.toPermHom SL Point).prod (MulAction.toPermHom SL Line)))

theorem action_injective : Function.Injective action := by
  intro g h he
  apply (MulAction.toPerm_injective : Function.Injective (MulAction.toPermHom SL Point))
  have hs := Equiv.Perm.sumCongrHom_injective
    (vertices.symm.permCongrHom.injective he)
  exact congrArg Prod.fst hs

def X : SL := ⟨!![0,0,1; 0,1,1; 1,1,0], by decide +kernel⟩
def Y : SL := ⟨!![1,1,0; 0,1,0; 1,0,1], by decide +kernel⟩

theorem action_X : action X = modelA * modelB := by
  apply Equiv.ext
  have h : ∀ i : Fin 14, action X i = (modelA * modelB) i := by decide +kernel
  exact h

theorem action_Y : action Y = modelB ^ 2 := by
  apply Equiv.ext
  have h : ∀ i : Fin 14, action Y i = (modelB ^ 2) i := by decide +kernel
  exact h

end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.LinearModel

namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.LinearModel
open Matrix.PSL3Two Subgroup

private theorem X_order : orderOf X = 7 := by
  let : Fact (Nat.Prime 7) := ⟨by decide⟩
  apply orderOf_eq_prime
  · apply action_injective
    rw [map_pow, map_one, action_X]
    decide +kernel
  · intro h
    have hh := congrArg action h
    rw [action_X, map_one] at hh
    exact (by decide +kernel : modelA * modelB ≠ 1) hh

private theorem Y_order : orderOf Y = 4 := by
  apply orderOf_eq_prime_pow (p := 2) (n := 1)
  · intro h
    have hh := congrArg action h
    rw [map_pow, map_one, action_Y] at hh
    exact (by decide +kernel : (modelB ^ 2) ^ (2 ^ 1) ≠ 1) hh
  · apply action_injective
    rw [map_pow, map_one, action_Y]
    decide +kernel

private theorem XY_order : orderOf (X * Y) = 3 := by
  apply orderOf_eq_prime
  · apply action_injective
    rw [map_pow, map_mul, map_one, action_X, action_Y]
    decide +kernel
  · intro h
    have hh := congrArg action h
    rw [map_mul, map_one, action_X, action_Y] at hh
    exact (by decide +kernel : (modelA * modelB) * modelB ^ 2 ≠ 1) hh

/-- The exact matrix pair generates SL₃(2): its orders force index at most two,
and simplicity excludes index two. -/
theorem generated : closure ({X,Y} : Set SL) = ⊤ := by
  let S : Subgroup SL := closure {X,Y}
  have hx : X ∈ S := subset_closure (by simp)
  have hy : Y ∈ S := subset_closure (by simp)
  have h7 : 7 ∣ Nat.card S := by simpa only [X_order] using S.orderOf_dvd_natCard hx
  have h4 : 4 ∣ Nat.card S := by simpa only [Y_order] using S.orderOf_dvd_natCard hy
  have h3 : 3 ∣ Nat.card S := by simpa only [XY_order] using S.orderOf_dvd_natCard (S.mul_mem hx hy)
  have hd : 84 ∣ Nat.card S := by
    have hh := Nat.lcm_dvd h7 (Nat.lcm_dvd h4 h3)
    norm_num at hh ⊢
    exact hh
  have hc := S.card_mul_index
  rw [card_SL] at hc
  obtain ⟨k,hk⟩ := hd
  have hi : S.index = 1 ∨ S.index = 2 := by
    have hd : S.index ∣ 2 := ⟨k, by rw [hk] at hc; nlinarith [hc]⟩
    exact (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hd
  rcases hi with hi | hi
  · exact index_eq_one.mp hi
  · let := Atlas.Comparisons.Exceptional.sl3Two_simple
    let := S.normal_of_index_eq_two hi
    rcases (inferInstance : S.Normal).eq_bot_or_eq_top with hb | ht
    · rw [hb, index_bot, card_SL] at hi
      omega
    · exact ht
end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.LinearModel

namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.LinearModel
open Matrix.PSL3Two Subgroup

private def letter : Fin 4 → Equiv.Perm (Fin 14) :=
  ![modelA * modelB, modelB ^ 2, (modelA * modelB)⁻¹, (modelB ^ 2)⁻¹]
private def word (w : List (Fin 4)) : Equiv.Perm (Fin 14) := (w.map letter).prod

private theorem word_mem (w : List (Fin 4)) : word w ∈ action.range := by
  have hl (i : Fin 4) : letter i ∈ action.range := by
    fin_cases i
    · exact (show modelA * modelB ∈ action.range from ⟨X, action_X⟩)
    · exact (show modelB ^ 2 ∈ action.range from ⟨Y, action_Y⟩)
    · exact action.range.inv_mem ((show modelA * modelB ∈ action.range from ⟨X, action_X⟩))
    · exact action.range.inv_mem ((show modelB ^ 2 ∈ action.range from ⟨Y, action_Y⟩))
  induction w with
  | nil => exact action.range.one_mem
  | cons i w ih => exact action.range.mul_mem (hl i) ih

private def orbitWord : Fin 14 → List (Fin 4) :=
  ![[], [], [1,2], [1,2], [0], [1], [0], [1], [0,1], [3], [2], [2,1], [0,0], [2]]
private def base : Fin 14 → Fin 14 := ![0,1,1,0,0,0,1,1,1,1,1,0,0,0]

private theorem orbit_word : ∀ i, word (orbitWord i) (base i) = i := by decide +kernel
private theorem base_cases : ∀ i, base i = 0 ∨ base i = 1 := by decide +kernel

private theorem stabilizer_zero :
    word [1,1] 0 = 0 ∧ word [2,1,0] 0 = 0 ∧
    ∀ i, word [1,1] i = i → word [2,1,0] i = i → i = 0 := by decide +kernel
private theorem stabilizer_one :
    word [0,0,3] 1 = 1 ∧ word [1,1,0] 1 = 1 ∧
    ∀ i, word [0,0,3] i = i → word [1,1,0] i = i → i = 1 := by decide +kernel

/-- The embedded linear group has trivial centralizer even in Sym(14).
Its two point stabilizers each have a unique fixed vertex; its two seven-point
orbits then recover every value of a commuting permutation. -/
theorem centralizer_range : centralizer (action.range : Set (Equiv.Perm (Fin 14))) = ⊥ := by
  apply le_bot_iff.mp
  intro p hp
  have hc (w : List (Fin 4)) (i : Fin 14) : word w (p i) = p (word w i) :=
    congrArg (fun q : Equiv.Perm (Fin 14) => q i) (hp (word w) (word_mem w))
  have hf (w : List (Fin 4)) (i : Fin 14) (hi : word w i = i) : word w (p i) = p i := by
    rw [hc, hi]
  have h0 : p 0 = 0 := stabilizer_zero.2.2 _
    (hf _ _ stabilizer_zero.1) (hf _ _ stabilizer_zero.2.1)
  have h1 : p 1 = 1 := stabilizer_one.2.2 _
    (hf _ _ stabilizer_one.1) (hf _ _ stabilizer_one.2.1)
  apply mem_bot.mpr
  apply Equiv.ext
  intro i
  change p i = i
  have hb : p (base i) = base i := by rcases base_cases i with h | h <;> simp [h,h0,h1]
  calc
    p i = p (word (orbitWord i) (base i)) := congrArg p (orbit_word i).symm
    _ = word (orbitWord i) (p (base i)) := (hc _ _).symm
    _ = i := by rw [hb, orbit_word]
end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.LinearModel

namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.LinearModel
open Matrix.PSL3Two Subgroup

/-- The natural-plus-dual linear action is contained in the actual model. -/
theorem range_le_model : action.range ≤ model := by
  have h : closure ({X,Y} : Set SL) ≤ model.comap action := by
    apply (Subgroup.closure_le _).mpr
    intro g hg
    rcases Set.mem_insert_iff.mp hg with rfl | hg
    · change action X ∈ model
      rw [action_X]
      exact model.mul_mem modelA_mem modelB_mem
    · rw [Set.mem_singleton_iff] at hg
      subst g
      change action Y ∈ model
      rw [action_Y]
      exact model.pow_mem modelB_mem 2
  rw [generated] at h
  rintro p ⟨g,rfl⟩
  exact h (mem_top g)

noncomputable def normalPart : Subgroup model := action.range.subgroupOf model

/-- The actual subgroup, with its embedding retained, is the matrix PSL₃(2). -/
noncomputable def normalEquiv : normalPart ≃* PSL :=
  ((subgroupOfEquivOfLe range_le_model).trans
    (MonoidHom.ofInjective action_injective).symm).trans equiv

theorem card_normalPart : Nat.card normalPart = 168 :=
  (Nat.card_congr normalEquiv.toEquiv).trans card_PSL

theorem index_normalPart : normalPart.index = 2 := by
  have h := normalPart.card_mul_index
  rw [card_normalPart, card_model] at h
  omega

instance normalPart_normal : normalPart.Normal :=
  normalPart.normal_of_index_eq_two index_normalPart

theorem centralizer_normalPart : centralizer (normalPart : Set model) = ⊥ := by
  apply le_bot_iff.mp
  intro p hp
  have hc : (p : Equiv.Perm (Fin 14)) ∈ centralizer (action.range : Set (Equiv.Perm (Fin 14))) := by
    intro g hg
    have hm : (⟨g,range_le_model hg⟩ : model) ∈ normalPart := hg
    exact congrArg Subtype.val (hp _ hm)
  exact mem_bot.mpr (Subtype.ext (mem_bot.mp (centralizer_range.le hc)))

noncomputable def conjugation : model →* MulAut PSL :=
  (MulAut.congr normalEquiv).toMonoidHom.comp (MulAut.conjNormal : model →* MulAut normalPart)

theorem conjugation_injective : Function.Injective conjugation :=
  (MulAut.congr normalEquiv).injective.comp
    (MulAut.conjNormal_injective_of_centralizer_eq_bot normalPart centralizer_normalPart)

/-- Faithful conjugation exhausts Aut(PSL₃(2)), both groups having order 336. -/
noncomputable def modelEquivAut : model ≃* MulAut PSL :=
  MulEquiv.ofBijective conjugation ((Nat.bijective_iff_injective_and_card conjugation).mpr
    ⟨conjugation_injective, card_model.trans Automorphisms.card_aut.symm⟩)
end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer.LinearModel

namespace Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
open ExceptionalParabolics
/-- The whole fixed subgroup of the native representative is Aut(PSL₃(2)). -/
noncomputable def fixedEquivAut : involutionAut.fixedSubgroup ≃* MulAut Matrix.PSL3Two.PSL :=
  fixedEquivModel.trans LinearModel.modelEquivAut

/-- The same actual fixed subgroup is the PGL₂(7) source table model. -/
noncomputable def fixedEquivPGL : involutionAut.fixedSubgroup ≃* GorensteinWalter.PGL2 (ZMod 7) :=
  fixedEquivAut.trans Matrix.PSL3Two.Automorphisms.pgl2SevenEquivAut.symm
end Sporadic.LeechRelated.J2.OuterInvolutionCentralizer
