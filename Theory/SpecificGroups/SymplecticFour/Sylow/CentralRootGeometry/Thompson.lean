module

public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates
public import Theory.SpecificGroups.SymplecticFour.EvenTwoRank
public import Stellmacher.ElementaryAbelianMaxJMap
/-!
# The maximum-elementary Thompson subgroup of the symplectic Sylow group

The kernels of the two outside-coordinate homomorphisms have exponent two
and order q³. The existing elementary-subgroup bound proves their maximality;
the coordinate factorization shows they generate the whole Sylow group.

Source: Aschbacher–Smith, Lemma 16.5.13, printed p.1202. We use precisely the
maximum-elementary Thompson subgroup, with the intrinsic and ambient groups
kept distinct.
-/

public section
open Subgroup
namespace Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
variable {F : Type*} [Field F] [CharP F 2] [Finite F]

private def outerEntry (i : Bool) (x : unipotent (F := F)) : F :=
  if i then x.val.val (.inl 0) (.inl 1) else x.val.val (.inl 1) (.inr 1)

omit [Finite F] in
private theorem outerEntry_element (i : Bool) (b u w v : F) :
    outerEntry i (element b u w v) = if i then b else v := by
  unfold outerEntry
  rw [element_matrix]
  cases i <;> rfl

private noncomputable def outerHom (i : Bool) : unipotent (F := F) →* Multiplicative F where
  toFun x := Multiplicative.ofAdd (outerEntry i x)
  map_one' := by cases i <;> rfl
  map_mul' x y := by
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    obtain ⟨⟨c,z,t,a⟩,rfl⟩ := element_surjective y
    change Multiplicative.ofAdd (outerEntry i (element b u w v * element c z t a)) =
      Multiplicative.ofAdd (outerEntry i (element b u w v) + outerEntry i (element c z t a))
    rw [element_mul, outerEntry_element, outerEntry_element, outerEntry_element]
    cases i <;> rfl

/-- The two elementary subgroups defined by b = 0 and v = 0. -/
noncomputable def wing (i : Bool) : Subgroup (unipotent (F := F)) := (outerHom i).ker

theorem element_mem_wing (i : Bool) (b u w v : F) :
    element b u w v ∈ wing i ↔ (if i then b else v) = 0 := by
  change Multiplicative.ofAdd (outerEntry i (element b u w v)) = 1 ↔ _
  rw [outerEntry_element]
  rfl

private def wingParam (i : Bool) (x : F × F × F) : wing (F := F) i :=
  if h : i then ⟨element 0 x.1 x.2.1 x.2.2, (element_mem_wing _ _ _ _ _).mpr (by simp [h])⟩
  else ⟨element x.1 x.2.1 x.2.2 0, (element_mem_wing _ _ _ _ _).mpr (by simp [h])⟩

private theorem wingParam_bijective (i : Bool) : Function.Bijective (wingParam (F := F) i) := by
  constructor
  · intro x y h
    have hh := congrArg Subtype.val h
    cases i
    · change element x.1 x.2.1 x.2.2 0 = element y.1 y.2.1 y.2.2 0 at hh
      obtain ⟨h1,h2,h3,_⟩ := (element_eq_iff _ _ _ _ _ _ _ _).mp hh
      exact Prod.ext h1 (Prod.ext h2 h3)
    · change element 0 x.1 x.2.1 x.2.2 = element 0 y.1 y.2.1 y.2.2 at hh
      obtain ⟨_,h1,h2,h3⟩ := (element_eq_iff _ _ _ _ _ _ _ _).mp hh
      exact Prod.ext h1 (Prod.ext h2 h3)
  · rintro ⟨x,hx⟩
    obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
    rw [element_mem_wing] at hx
    cases i
    · simp only [Bool.false_eq_true, ↓reduceIte] at hx
      subst v
      exact ⟨(b,u,w),rfl⟩
    · simp only [↓reduceIte] at hx
      subst b
      exact ⟨(u,w,v),rfl⟩

theorem card_wing (i : Bool) : Nat.card (wing (F := F) i) = Nat.card F^3 := by
  rw [← Nat.card_congr (Equiv.ofBijective _ (wingParam_bijective i))]
  simp only [Nat.card_prod]
  ring

private theorem wing_square (i : Bool) (x : wing (F := F) i) : x^2=1 := by
  obtain ⟨p,rfl⟩ := (wingParam_bijective i).surjective x
  apply Subtype.ext
  cases i <;> change (element _ _ _ _)^2 = 1
  all_goals
    rw [element_square]
    simpa [theta] using (element_zero (F := F))

theorem wing_elementary (i : Bool) : IsElementaryAbelian 2 (wing (F := F) i) := by
  have hi (x : wing (F := F) i) : x⁻¹=x :=
    inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using wing_square i x)
  have hc : IsMulCommutative (wing (F := F) i) := by
    apply IsMulCommutative.of_comm
    intro x y
    simpa only [hi] using (mul_inv_rev x y)
  exact {
    toIsMulCommutative := hc
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one (wing_square i) }

theorem wings_generate : wing (F := F) false ⊔ wing true = ⊤ := by
  apply top_unique
  intro x _
  obtain ⟨⟨b,u,w,v⟩,rfl⟩ := element_surjective x
  have he : element b u w v = element b u w 0 * element 0 0 0 v := by
    simp [element_mul]
  change element b u w v ∈ wing false ⊔ wing true
  rw [he]
  exact mul_mem_sup ((element_mem_wing _ _ _ _ _).mpr rfl)
    ((element_mem_wing _ _ _ _ _).mpr rfl)

theorem elementaryAbelianMaxJ_top :
    Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (unipotent (F := F))) = ⊤ := by
  have hw (i : Bool) : wing (F := F) i ≤
      Stellmacher.elementaryAbelianMaxJ (⊤ : Subgroup (unipotent (F := F))) := by
    apply le_sSup
    refine ⟨le_top, wing_elementary i, ?_⟩
    intro A _ hA
    let := hA
    rw [card_wing]
    exact EvenTwoRank.elementary_card_le A
  apply top_unique
  conv_lhs => rw [← wings_generate]
  exact sup_le (hw false) (hw true)

theorem elementaryAbelianMaxJ_unipotent :
    Stellmacher.elementaryAbelianMaxJ (unipotent (F := F)) = unipotent := by
  have he := Stellmacher.elementaryAbelianMaxJ_map_injective
    (unipotent (F := F)).subtype Subtype.val_injective ⊤
  simpa only [← MonoidHom.range_eq_map, Subgroup.range_subtype, elementaryAbelianMaxJ_top] using he
end Theory.SpecificGroups.SymplecticFour.CentralRootGeometry
