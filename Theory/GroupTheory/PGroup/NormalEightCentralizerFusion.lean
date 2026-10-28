module

public import Theory.GroupTheory.PGroup.NormalAbelianIndexFour
public import Theory.GroupTheory.PGroup.NormalEightFour
public import Theory.GroupTheory.PGroup.OrderThirtyTwoFourFusion

/-!
# Centralizer fusion without normal elementary eights

A central elementary four in a normal subgroup is the omega subgroup of
that subgroup's center: the latter is normal and has order at most four.
Consequently the four itself is normal. This replaces the bound on all
elementary subgroups used in `NormalFourCentralizerAutomorphisms`.

An embedding of the index-two centralizer of a unique normal four back
into the Sylow subgroup therefore preserves that four and its centralizer.
Ambient fusion of the four then induces automorphisms of the centralizer
transitive on the three involutions belonging to the four. Other involutions
in the centralizer are allowed.

Source: Janko–Thompson, Math. Z. 113 (1970), §6, printed p.395. These are
fusion reductions toward 1.4, not an invocation of the MacWilliams theorem.
-/

open Subgroup

namespace Subgroup

/-- A central elementary four in a normal subgroup is itself normal if normal
 elementary eights are absent. -/
public theorem normal_four_of_normal_centralizing_overgroup_of_no_normal_eight
    {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ A : Subgroup P, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E C : Subgroup P) [IsElementaryAbelian 2 E] [C.Normal]
    (hE : Nat.card E = 4) (hEC : E ≤ C)
    (hCE : C ≤ centralizer (E : Set P)) : E.Normal := by
  let Z := (center C).map C.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  let : IsMulCommutative Z := inferInstance
  let O := omega₁ Z (p := 2)
  let : O.Characteristic := omega₁_characteristic _
  let K := O.map Z.subtype
  let : K.Normal := ConjAct.normal_of_characteristic_of_normal
  have hEZ : E ≤ Z := by
    intro e he
    refine ⟨⟨e, hEC he⟩, mem_center_iff.mpr ?_, rfl⟩
    intro c
    exact Subtype.ext ((hCE c.property) e he).symm
  have hEK : E ≤ K := by
    intro e he
    refine ⟨⟨e, hEZ he⟩, subset_closure ?_, rfl⟩
    apply Subtype.ext
    simpa using elemPow_eq_one_of_isElementaryAbelian e he
  have hK : Nat.card K ≤ 4 := by
    rw [card_map_of_injective Z.subtype_injective]
    exact card_omega_one_le_four_of_normal_abelian_of_no_normal_eight hno Z
  have heq : E = K := eq_of_le_of_card_ge hEK (by omega)
  exact heq ▸ inferInstance

end Subgroup

namespace Sylow

/-- Embeddings of the centralizer preserve the unique normal four under the
 normal-only elementary bound. -/
public theorem range_eq_centralizer_of_injective_of_unique_normal_four_of_no_normal_eight
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (hi : (centralizer (E : Set S)).index = 2)
    (f : centralizer (E : Set S) →* S) (hf : Function.Injective f) :
    f.range = centralizer (E : Set S) := by
  let C := centralizer (E : Set S)
  have hEC : E ≤ C := le_centralizer E
  let F := E.subgroupOf C
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hEC
  have hF : Nat.card F = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hEC).toEquiv).trans hE
  have hfr : Nat.card f.range = Nat.card C :=
    (Nat.card_congr (MulEquiv.ofBijective f.rangeRestrict
      ⟨fun _ _ h => hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩).toEquiv).symm
  have hfi : f.range.index = 2 := by
    have h₁ := f.range.card_mul_index
    have h₂ := C.card_mul_index
    rw [hfr] at h₁
    rw [hi] at h₂
    have hp := Nat.card_pos (α := C)
    nlinarith
  let : f.range.Normal := f.range.normal_of_index_eq_two hfi
  let : IsElementaryAbelian 2 (F.map f) := IsElementaryAbelian.map f
  have hFc : f.range ≤ centralizer (F.map f : Set S) := by
    rintro _ ⟨c, rfl⟩ _ ⟨e, he, rfl⟩
    have hc : (e : S) * (c : S) = (c : S) * (e : S) := c.property e he
    simpa only [map_mul] using congrArg f (show e * c = c * e from Subtype.ext hc)
  have hFm : F.map f ≤ f.range := map_le_range f F
  have hFE : F.map f = E := hunique _
    (normal_four_of_normal_centralizing_overgroup_of_no_normal_eight hno (F.map f) f.range
      (by rwa [card_map_of_injective hf]) hFm hFc)
    inferInstance (by rwa [card_map_of_injective hf])
  apply eq_of_le_of_card_ge
  · simpa only [hFE] using hFc
  · exact hfr.ge

/-- Ambient fusion induces automorphisms of the centralizer transitive on
the three involutions of the given four. -/
public theorem centralizer_four_automorphism_transitive_of_no_normal_eight
    {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G)
    (hno : ¬ ∃ A : Subgroup S, A.Normal ∧ IsElementaryAbelian 2 A ∧ 8 ≤ Nat.card A)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (E : Subgroup S) [E.Normal] [IsElementaryAbelian 2 E] (hE : Nat.card E = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = E)
    (z : S) (hz : orderOf z = 2) (hzc : z ∈ center S)
    (hfusion : ∀ x y : E, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    ∀ x y : centralizer (E : Set S), (x : S) ∈ E → (y : S) ∈ E →
      orderOf x = 2 → orderOf y = 2 →
      ∃ a : MulAut (centralizer (E : Set S)), a x = y := by
  let C := centralizer (E : Set S)
  have hi := centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
    S.isPGroup' hZ E hE
  have hzE : z ∈ E := omega_one_center_le_normal_four_of_no_normal_eight hno E hE
    ⟨⟨z, hzc⟩, subset_closure (by
      change (⟨z, hzc⟩ : center S) ^ (2 ^ 1) = 1
      apply Subtype.ext
      change z ^ 2 = 1
      simpa only [hz] using pow_orderOf_eq_one z), rfl⟩
  have hto (x : C) (hxE : (x : S) ∈ E) (hx : orderOf x = 2) :
      ∃ a : MulAut C, (a x : S) = z := by
    have hxcenter : x ∈ center C := by
      apply mem_center_iff.mpr
      intro c
      exact Subtype.ext (c.property x hxE).symm
    have hconj : IsConj ((x : S) : G) (z : G) :=
      hfusion ⟨x, hxE⟩ ⟨z, hzE⟩
        (fun he => (orderOf_eq_prime_iff.mp hx).2 (Subtype.ext (show (x : S) = 1 from congrArg (fun e : E => (e : S)) he)))
        (fun he => (orderOf_eq_prime_iff.mp hz).2 (congrArg Subtype.val he))
    obtain ⟨f, hf, hfx⟩ :=
      S.exists_injective_hom_of_central_isConj C x hxcenter z hzc hconj
    have hr := S.range_eq_centralizer_of_injective_of_unique_normal_four_of_no_normal_eight
      hno E hE hunique hi f hf
    let g : C →* C := f.codRestrict C (fun c => by change f c ∈ centralizer (E : Set S); rw [← hr]; exact ⟨c, rfl⟩)
    have hg : Function.Injective g := fun _ _ he => hf (congrArg Subtype.val he)
    exact ⟨MulEquiv.ofBijective g ⟨hg, Finite.surjective_of_injective hg⟩, hfx⟩
  intro x y hxE hyE hx hy
  obtain ⟨a, ha⟩ := hto x hxE hx
  obtain ⟨b, hb⟩ := hto y hyE hy
  refine ⟨a.trans b.symm, ?_⟩
  change b.symm (a x) = y
  apply b.injective
  rw [b.apply_symm_apply]
  exact Subtype.ext (ha.trans hb.symm)


end Sylow
