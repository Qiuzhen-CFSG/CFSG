module
public import Theory.GroupTheory.Recognition.ReeTwo.SmallEvenExceptionalCoordinates
public import Theory.GroupTheory.PGroup.CharacteristicSeriesAutomorphisms

/-!
# An intrinsic characteristic flag for the exceptional Ree two subgroup

The last two root coordinates form precisely the set of elements with 80
square roots. This makes that four-group characteristic. Its upper central
step and the center supply the other terms of a four-step automorphism flag.
The explicit generators also provide small tests for centrality and centrality
modulo the four-group. Normality is checked in the order-64 tail quotient.

Source: the verified Shinoda (1975), (2.3), pp. 81–82 coordinate model;
the square counts are proved in SmallEvenExceptionalCoordinates.
-/

@[expose] public section
open scoped commutatorElement
namespace ReeTwo.SylowModel.SmallEvenExceptional
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

abbrev U := coordinateSubgroup
def fourMap : Multiplicative (Fin 2 → ZMod 2) →* SylowModel where
  toFun v := last ![0,v.toAdd 0,v.toAdd 1]
  map_one' := rfl
  map_mul' := by decide +kernel
def E : Subgroup U := fourMap.range.comap U.subtype
theorem mem_E (x : U) : x ∈ E ↔
    (x : SylowModel) = last ![0,x.val.left.b8,x.val.left.b9] := by
  constructor
  · rintro ⟨v,hv⟩
    change fourMap v = (x : SylowModel) at hv
    have h8 := congrArg (fun x : SylowModel => x.left.b8) hv
    have h9 := congrArg (fun x : SylowModel => x.left.b9) hv
    change v.toAdd 0 = _ at h8
    change v.toAdd 1 = _ at h9
    rw [← hv]
    change last ![0,v.toAdd 0,v.toAdd 1] = last ![0,_,_]
    rfl
  · intro hx
    exact ⟨Multiplicative.ofAdd ![x.val.left.b8,x.val.left.b9], hx.symm⟩
theorem last_injective : Function.Injective last := by
  intro v w h
  funext i
  fin_cases i
  · exact congrArg (fun x : SylowModel => x.left.b7) h
  · exact congrArg (fun x : SylowModel => x.left.b8) h
  · exact congrArg (fun x : SylowModel => x.left.b9) h
theorem square_last (x : U) :
    (x : SylowModel) ^ 2 = last (sq (equiv x)) := by
  have h := congrArg (fun y : U => (y : SylowModel)) (equiv.symm_apply_apply x)
  change element (equiv x) = x at h
  rw [← h]
  exact square_formula (equiv x)
theorem roots_card (w : Fin 3 → ZMod 2) :
    Nat.card {x : U // (x : SylowModel) ^ 2 = last w} = if w 0 = 0 then 80 else 48 := by
  trans Nat.card {v : V // sq v = w}
  · apply Nat.card_congr
    refine {
      toFun := fun x => ⟨equiv x, last_injective ((square_last x).symm.trans x.property)⟩
      invFun := fun v => ⟨equiv.symm v, ?_⟩
      left_inv := fun x => Subtype.ext (equiv.symm_apply_apply x)
      right_inv := fun v => Subtype.ext (equiv.apply_symm_apply v) }
    rw [square_last, equiv.apply_symm_apply, v.property]
  · rw [Nat.card_eq_fintype_card]
    exact sq_count w
theorem fiber_card_aut (f : MulAut U) (x : U) :
    Nat.card {y : U // y ^ 2 = f x} = Nat.card {y : U // y ^ 2 = x} := by
  apply Nat.card_congr
  refine {
    toFun := fun y => ⟨f.symm y, ?_⟩
    invFun := fun y => ⟨f y, ?_⟩
    left_inv := fun y => Subtype.ext (f.apply_symm_apply y)
    right_inv := fun y => Subtype.ext (f.symm_apply_apply y) }
  · apply f.injective
    simpa only [map_pow, f.apply_symm_apply] using y.property
  · simpa only [map_pow] using congrArg f y.property
theorem fiber_card_coe (x : U) :
    Nat.card {y : U // y ^ 2 = x} = Nat.card {y : U // (y : SylowModel) ^ 2 = (x : SylowModel)} := by
  apply Nat.card_congr
  exact Equiv.subtypeEquivRight (fun y => Subtype.ext_iff)
theorem mem_E_iff_card (x : U) : x ∈ E ↔ Nat.card {y : U // y ^ 2 = x} = 80 := by
  rw [fiber_card_coe]
  constructor
  · intro hx
    rw [(mem_E x).mp hx, roots_card]
    rfl
  · intro hx
    have hpos : 0 < Nat.card {y : U // (y : SylowModel) ^ 2 = (x : SylowModel)} := by omega
    obtain ⟨y,hy⟩ := Nat.card_pos_iff.mp hpos |>.1
    have heq := (square_last y).symm.trans hy
    rw [← heq, roots_card] at hx
    have hzero : sq (equiv y) 0 = 0 := by split_ifs at hx with h; exact h; omega
    rw [mem_E, ← heq]
    congr 1
    funext i
    fin_cases i <;> first | exact hzero | rfl
instance : E.Characteristic := by
  apply Subgroup.characteristic_iff_le_comap.mpr
  intro f x hx
  change f x ∈ E
  rw [mem_E_iff_card, fiber_card_aut]
  exact (mem_E_iff_card x).mp hx

def C : Subgroup U := Subgroup.upperCentralSeriesStep E
instance : C.Characteristic := inferInstanceAs
  (Subgroup.upperCentralSeriesStep E).Characteristic
abbrev D : Subgroup U := Subgroup.center U

def gen (i : Fin 9) : U := ⟨element (fun j => if j = i then 1 else 0),element_mem _⟩
theorem gen_values :
    (gen 0 : SylowModel) = rootOne ^ 2 ∧
    ∀ i : Fin 8, (gen ⟨i.val+1,by omega⟩ : SylowModel) = root ⟨i.val+2,by omega⟩ :=
  by decide +kernel
theorem generated (H : Subgroup U) (h : ∀ i, gen i ∈ H) : H = ⊤ := by
  apply top_unique
  intro x _
  let M := H.map U.subtype
  have h0 : rootOne ^ 2 ∈ M := gen_values.1 ▸ Subgroup.mem_map_of_mem _ (h 0)
  have hr : ∀ i : CoreRoot, 2 ≤ i.val → root i ∈ M := by
    intro i hi
    have hh := Subgroup.mem_map_of_mem U.subtype (h ⟨i.val-1,by omega⟩)
    have hv := gen_values.2 ⟨i.val-2,by omega⟩
    have he : (⟨(i.val-2)+1,by omega⟩ : Fin 9) = ⟨i.val-1,by omega⟩ := by ext; dsimp; omega
    rw [he] at hv
    have he' : (⟨(i.val-2)+2,by omega⟩ : CoreRoot) = i := by ext; dsimp; omega
    rw [he'] at hv
    exact hv ▸ hh
  have hw : word (coords x) ∈ M := by
    unfold word
    repeat apply Subgroup.mul_mem
    all_goals apply Subgroup.pow_mem
    all_goals first | exact h0 | exact hr _ (by decide)
  rw [word_coords _ x.property] at hw
  obtain ⟨y,hy,he⟩ := hw
  have : y = x := Subtype.ext he
  exact this ▸ hy
theorem center_of_gen (x : U) (h : ∀ i, gen i * x = x * gen i) : x ∈ D := by
  have ht := generated (Subgroup.centralizer ({x} : Set U)) (fun i => by
    intro y hy
    have : y = x := Set.mem_singleton_iff.mp hy
    subst y
    exact (h i).symm)
  exact Subgroup.mem_center_iff.mpr (fun y => by
    have hy : y ∈ Subgroup.centralizer ({x} : Set U) := ht.symm ▸ Subgroup.mem_top y
    exact (hy x (Set.mem_singleton x)).symm)
theorem C_of_gen (x : U) (h : ∀ i, ⁅x,gen i⁆ ∈ E) : x ∈ C := by
  let q := QuotientGroup.mk' E
  let H := (Subgroup.centralizer ({q x} : Set (U ⧸ E))).comap q
  have hh : H = ⊤ := generated H (fun i => by
    change ∀ y ∈ ({q x} : Set (U ⧸ E)), y * q (gen i) = q (gen i) * y
    intro y hy
    have : y = q x := Set.mem_singleton_iff.mp hy
    subst y
    have hc : q ⁅x,gen i⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (h i)
    have he := congrArg (fun a => a * q (gen i) * q x) hc
    simpa [q, commutatorElement_def, mul_assoc] using he)
  intro y
  have hy : y ∈ H := hh.symm ▸ Subgroup.mem_top y
  have he := hy (q x) (Set.mem_singleton _)
  apply (QuotientGroup.eq_one_iff _).mp (show q ⁅x,y⁆ = 1 from ?_)
  change q (x * y * x⁻¹ * y⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, he]
  simp [mul_assoc]

instance : qnode.Normal where
  conj_mem := by
    change ∀ n, qmember n → ∀ g, qmember (g * n * g⁻¹)
    decide +kernel
instance : U.Normal := inferInstanceAs (qnode.comap TailQuotient.projection).Normal
theorem rootOne_normalizes : rootOne ∈ Subgroup.normalizer (U : Set SylowModel) := by
  rw [Subgroup.normalizer_eq_top]
  trivial

end ReeTwo.SylowModel.SmallEvenExceptional
