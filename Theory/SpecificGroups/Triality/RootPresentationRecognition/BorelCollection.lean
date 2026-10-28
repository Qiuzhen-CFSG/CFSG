module
public import Theory.SpecificGroups.Triality.RootPresentationRecognition.TorusRelations

/-!
# Borel collection from the triality equations

The torus normalizes the collected positive subgroup, so every generated Borel
element is a positive product times a torus word. The filtered positive
collector permits either simple root to be placed last. Its other five factors
stay positive under the corresponding reflection. This proves the local Borel
exchange needed by the abstract Bruhat argument without coordinate uniqueness.

Source: the Bruhat exchange argument of GLS3 2.3.5, using the explicit
relations of 2.4.5 and 2.4.7–8. The two parameter fields remain distinct.
-/

@[expose] public noncomputable section
namespace Triality.Standard.RootPresentationRecognition.SignedRoots
open Parabolics ConcreteBruhat.TorusCoordinates
variable {n : ℕ} {hn : 0 < n} {Y : Type*} [Group Y]
local notation "P" => binaryParameters n hn
variable (L : SignedRoots (n := n) (hn := hn) Y) (R : L.Relations)

theorem factor_mem_borel (i : Fin 6) (v : PositiveParameters n hn) :
    L.positive.factor i v ∈ L.borel R :=
  Subgroup.mem_sup_left (Subgroup.subset_closure ⟨(i,v),rfl⟩)

theorem short_mem_borel (i : Fin 3) (t : ExtensionField P) :
    L.shortValue i t ∈ L.borel R := by
  fin_cases i
  · exact L.factor_mem_borel R 0 (fun _ => t, 0)
  · exact L.factor_mem_borel R 2 (fun _ => t, 0)
  · exact L.factor_mem_borel R 3 (fun _ => t, 0)

theorem long_mem_borel (i : Fin 3) (t : fixedField P) :
    L.longValue i t ∈ L.borel R := by
  fin_cases i
  · exact L.factor_mem_borel R 1 (0, fun _ => t)
  · exact L.factor_mem_borel R 4 (0, fun _ => t)
  · exact L.factor_mem_borel R 5 (0, fun _ => t)

theorem simple_mem_borel (a : Bool) (v : PositiveParameters n hn) :
    L.simpleValue a v ∈ L.borel R := by
  cases a
  · exact L.long_mem_borel R _ _
  · exact L.short_mem_borel R _ _

theorem torus_mem_borel (p : TorusParameters n hn) : L.torus p ∈ L.borel R :=
  Subgroup.mem_sup_right ⟨p,rfl⟩

theorem torus_normalizes {t u : Y} (ht : t ∈ (L.torusHom R).range)
    (hu : u ∈ L.positive.positiveClosure) :
    t * u * t⁻¹ ∈ L.positive.positiveClosure := by
  obtain ⟨p,rfl⟩ := ht
  obtain ⟨a,rfl⟩ := (L.positive.mem_positiveClosure_iff R.positiveRelations u).mp hu
  rw [torusHom_apply, L.torus_product R]
  exact (L.positive.mem_positiveClosure_iff R.positiveRelations _).mpr ⟨_,rfl⟩

private def borelRange : Subgroup Y where
  carrier := {g | ∃ u ∈ L.positive.positiveClosure, ∃ t ∈ (L.torusHom R).range, g = u*t}
  one_mem' := ⟨1,Subgroup.one_mem _,1,Subgroup.one_mem _,by simp⟩
  mul_mem' := by
    rintro x y ⟨u,hu,t,ht,rfl⟩ ⟨v,hv,s,hs,rfl⟩
    refine ⟨u*(t*v*t⁻¹), Subgroup.mul_mem _ hu (L.torus_normalizes R ht hv),
      t*s,Subgroup.mul_mem _ ht hs,?_⟩
    group
  inv_mem' := by
    rintro x ⟨u,hu,t,ht,rfl⟩
    refine ⟨t⁻¹*u⁻¹*(t⁻¹)⁻¹,
      L.torus_normalizes R (Subgroup.inv_mem _ ht) (Subgroup.inv_mem _ hu),
      t⁻¹,Subgroup.inv_mem _ ht,?_⟩
    group

private theorem borel_eq_range : L.borel R = L.borelRange R := by
  apply le_antisymm
  · apply sup_le
    · intro u hu
      exact ⟨u,hu,1,Subgroup.one_mem _,by simp⟩
    · intro t ht
      exact ⟨1,Subgroup.one_mem _,t,ht,by simp⟩
  · rintro g ⟨u,hu,t,ht,rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ht)

/-- Every abstract Borel element has the six positive coordinates and the two torus units. -/
theorem mem_borel_iff (g : Y) : g ∈ L.borel R ↔
    ∃ (v : PositiveParameters n hn) (p : TorusParameters n hn),
      g = L.positive.product v * L.torus p := by
  rw [L.borel_eq_range R]
  constructor
  · rintro ⟨u,hu,t,⟨p,rfl⟩,rfl⟩
    obtain ⟨a,rfl⟩ := (L.positive.mem_positiveClosure_iff R.positiveRelations u).mp hu
    exact ⟨a,p,rfl⟩
  · rintro ⟨a,p,rfl⟩
    exact ⟨_,(L.positive.mem_positiveClosure_iff R.positiveRelations _).mpr ⟨a,rfl⟩,
      _,⟨p,rfl⟩,rfl⟩

include R in
theorem torus_simple (p : TorusParameters n hn) (a : Bool) (v : PositiveParameters n hn) :
    L.torus p * L.simpleValue a v * (L.torus p)⁻¹ = L.simpleValue a (scale p v) := by
  cases a
  · exact L.torus_factor R p 1 v
  · exact L.torus_factor R p 0 v

theorem reflection_torus_mem (a : Bool) (p : TorusParameters n hn) :
    L.reflection a * L.torus p * (L.reflection a)⁻¹ ∈ L.borel R := by
  cases a
  · change L.nB 1 * L.torus p * (L.nB 1)⁻¹ ∈ _
    rw [R.central]
    exact L.torus_mem_borel R _
  · change L.nA 1 * L.torus p * (L.nA 1)⁻¹ ∈ _
    rw [R.arms]
    exact L.torus_mem_borel R _

/-- The other five positive factors stay positive under the chosen reflection. -/
theorem reflection_factor_mem (a : Bool) (i : Fin 6)
    (hi : i ≠ if a then 0 else 1) (v : PositiveParameters n hn) :
    L.reflection a * L.positive.factor i v * (L.reflection a)⁻¹ ∈ L.borel R := by
  have hs0 := R.arms_short0 true
  have hs1 := R.arms_short1 true
  have hs2 := R.arms_short2 true
  have hl := R.arms_long true
  have hcs := R.central_short true
  have hcl1 := R.central_long1 true
  have hcl2 := R.central_long2 true
  simp only [shortSigned, longSigned, if_true] at hs0 hs1 hs2 hl hcs hcl1 hcl2
  cases a <;> fin_cases i <;> simp only [if_true, Bool.false_eq_true, if_false] at hi
  all_goals simp only [reflection, if_true, Bool.false_eq_true, if_false]
  · change L.nB 1 * L.shortValue 0 _ * _ ∈ _
    rw [hcs]; exact L.short_mem_borel R _ _
  · exact (hi rfl).elim
  · change L.nB 1 * L.shortValue 1 _ * _ ∈ _
    rw [hcs]; exact L.short_mem_borel R _ _
  · change L.nB 1 * L.shortValue 2 _ * _ ∈ _
    rw [hcs]; exact L.short_mem_borel R _ _
  · change L.nB 1 * L.longValue 1 _ * _ ∈ _
    rw [hcl1]; exact L.long_mem_borel R _ _
  · change L.nB 1 * L.longValue 2 _ * _ ∈ _
    rw [hcl2]; exact L.long_mem_borel R _ _
  · exact (hi rfl).elim
  · change L.nA 1 * L.longValue 0 _ * _ ∈ _
    rw [hl]; exact L.long_mem_borel R _ _
  · change L.nA 1 * L.shortValue 1 _ * _ ∈ _
    rw [hs1]; exact L.short_mem_borel R _ _
  · change L.nA 1 * L.shortValue 2 _ * _ ∈ _
    rw [hs2]; exact L.short_mem_borel R _ _
  · change L.nA 1 * L.longValue 1 _ * _ ∈ _
    rw [hl]; exact L.long_mem_borel R _ _
  · change L.nA 1 * L.longValue 2 _ * _ ∈ _
    rw [hl]; exact L.long_mem_borel R _ _

private def simpleLastOrder (a : Bool) : List (Fin 6) :=
  if a then [1,2,3,4,5,0] else [0,2,3,4,5,1]

private theorem reflection_positive (a : Bool) (u : Y) (hu : u ∈ L.positive.positiveClosure) :
    ∃ c v, c ∈ L.borel R ∧ L.reflection a * u = c * L.reflection a * L.simpleValue a v := by
  obtain ⟨v,rfl⟩ := (L.positive.mem_positiveClosure_iff R.positiveRelations u).mp hu
  have hall (i : Fin 6) : i ∈ simpleLastOrder a := by cases a <;> fin_cases i <;> decide
  obtain ⟨p,hp⟩ := FilteredCollection.filteredCollection_exists_params height L.positive.factor
    (simpleLastOrder a) (by cases a <;> decide) 6
    (by intro i _; fin_cases i <;> decide)
    (fun i v w => (L.positive.factor_add i v w).symm)
    (by
      intro i j v w _ _ hij
      obtain ⟨c,hc,he⟩ := R.positiveRelations.higher i j v w hij
      exact ⟨c,fun z hz => ⟨hall _,hc z hz⟩,he⟩)
    (List.ofFn fun i : Fin 6 => (i,v)) (fun z _ => hall _)
  change L.positive.product v = _ at hp
  rw [hp]
  let w := L.reflection a
  let radicalWord := ((simpleLastOrder a).take 5 |>.map fun i => L.positive.factor i (p i)).prod
  have hradicalWord : w * radicalWord * w⁻¹ ∈ L.borel R := by
    change (MulAut.conj w) radicalWord ∈ _
    dsimp only [radicalWord]
    rw [map_list_prod, List.map_map]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hg
    apply L.reflection_factor_mem R a i
    cases a <;> fin_cases i <;> simp_all [simpleLastOrder]
  cases a
  · refine ⟨w * radicalWord * w⁻¹,p 1,hradicalWord,?_⟩
    dsimp [radicalWord,w,simpleLastOrder,simpleValue]
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    group
    rfl
  · refine ⟨w * radicalWord * w⁻¹,p 0,hradicalWord,?_⟩
    dsimp [radicalWord,w,simpleLastOrder,simpleValue]
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    group
    rfl

/-- Isolate the simple root on the right of a reflected Borel element. -/
theorem reflection_borel (a : Bool) (b : Y) (hb : b ∈ L.borel R) :
    ∃ c v, c ∈ L.borel R ∧ L.reflection a * b = c * L.reflection a * L.simpleValue a v := by
  obtain ⟨v,p,rfl⟩ := (L.mem_borel_iff R b).mp hb
  obtain ⟨c,t,hc,he⟩ := L.reflection_positive R a (L.positive.product v)
    ((L.positive.mem_positiveClosure_iff R.positiveRelations _).mpr ⟨v,rfl⟩)
  have ht : (L.torus p)⁻¹ * L.simpleValue a t * L.torus p = L.simpleValue a (scale p⁻¹ t) := by
    have hh := L.torus_simple R p⁻¹ a t
    have hi : L.torus p⁻¹ = (L.torus p)⁻¹ := (L.torusHom R).map_inv p
    simpa only [hi,inv_inv] using hh
  refine ⟨c * (L.reflection a * L.torus p * (L.reflection a)⁻¹),scale p⁻¹ t,
    Subgroup.mul_mem _ hc (L.reflection_torus_mem R a p),?_⟩
  rw [← ht]
  calc
    _ = (L.reflection a * L.positive.product v) * L.torus p := by group
    _ = _ := by rw [he]; group

/-- The torus normalizes the whole collected positive subgroup, in both directions. -/
theorem torus_range_le_normalizer : (L.torusHom R).range ≤
    Subgroup.normalizer (L.positive.positiveClosure : Set Y) := by
  intro t ht
  apply Subgroup.mem_normalizer_iff.mpr
  intro u
  constructor
  · exact fun hu => L.torus_normalizes R ht hu
  · intro hu
    have h := L.torus_normalizes R (Subgroup.inv_mem _ ht) hu
    simpa only [inv_inv, mul_assoc, inv_mul_cancel_left, mul_inv_cancel_right, inv_mul_cancel, mul_one] using h

/-- The generated Borel normalizes U. This connects the abstract collector to
source conventions where the full Borel is N(U). -/
theorem borel_le_normalizer : L.borel R ≤
    Subgroup.normalizer (L.positive.positiveClosure : Set Y) :=
  sup_le Subgroup.le_normalizer (L.torus_range_le_normalizer R)

end Triality.Standard.RootPresentationRecognition.SignedRoots
