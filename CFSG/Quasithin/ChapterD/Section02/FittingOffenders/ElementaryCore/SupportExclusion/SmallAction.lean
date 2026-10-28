module

public import Theory.GroupAction.ThreeGroupSixteenFaithful
public import Theory.Representation.BinaryGroupAction
public import Theory.Frattini.PGroupMap

/-!
# The image on a small binary support

Pad a faithful binary action of degree at most four with a trivial summand.
The faithful sixteen-vector calculation makes a three-group elementary abelian.
Apply this to the actual restricted image of P, and map its Frattini subgroup
to the trivial Frattini subgroup of that image. This proves pointwise fixation
of the original support, with the actual action map and kernel.

Source: Aschbacher--Smith D.2.14, printed p.186, paragraph (++).
The application to the central-line support is in `SupportExclusion`.
-/

public section

open Subgroup Representation Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterD.ElementaryCore.SupportExclusion
variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module (ZMod 2) V]
  [FiniteDimensional (ZMod 2) V]

/-- A faithful three-group in binary degree at most four is elementary abelian.
A trivial complementary summand reduces to the checked sixteen-vector action. -/
theorem small_faithful_elementary (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hG : IsPGroup 3 G)
    (hd : Module.finrank (ZMod 2) V ≤ 4) : IsElementaryAbelian 3 G := by
  let W := V × (Fin (4 - Module.finrank (ZMod 2) V) → ZMod 2)
  let σ : Representation (ZMod 2) G W := ρ.prod (Representation.trivial _ _ _)
  have hi : Function.Injective σ := by
    intro a b hab
    apply hρ
    ext v
    exact congrArg Prod.fst (LinearMap.congr_fun hab (v, 0))
  have hdim : Module.finrank (ZMod 2) W = 4 := by
    simp only [W, Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
    omega
  let := BinaryGroupAction.action σ
  let := BinaryGroupAction.elementary (V := W)
  have hc : Nat.card (Multiplicative W) = 16 := by
    rw [Nat.card_congr Multiplicative.toAdd, Module.natCard_eq_pow_finrank (K := ZMod 2),
      Nat.card_zmod, hdim]
    decide
  let : Finite (Multiplicative W) := Nat.finite_of_card_ne_zero (by omega)
  have hf : fixingSubgroup G (Set.univ : Set (Multiplicative W)) = ⊥ := by
    apply le_bot_iff.mp
    intro g hg
    apply mem_bot.mpr
    apply hi
    apply LinearMap.ext
    intro w
    rw [mem_fixingSubgroup_iff] at hg
    have he := hg (Multiplicative.ofAdd w) (Set.mem_univ _)
    change σ g w = w at he
    simpa only [map_one, Module.End.one_apply] using he
  exact (three_group_faithful_sixteen_is_elementary hG hc hf).1

/-- The actual image on an invariant subspace of dimension at most four
is elementary abelian; no faithfulness of the original action is required. -/
theorem small_image_elementary (ρ : Representation (ZMod 2) G V)
    (W : Submodule (ZMod 2) V) (P : Subgroup G) (hP : IsPGroup 3 P)
    (hstable : P ≤ subspaceStabilizer ρ W) (hd : Module.finrank (ZMod 2) W ≤ 4) :
    IsElementaryAbelian 3 (restrictedSubgroup ρ W P) := by
  let σ := (subspaceImageRepresentation ρ W).comp (restrictedSubgroup ρ W P).subtype
  apply small_faithful_elementary σ
  · exact (subspaceImageRepresentation_injective ρ W).comp Subtype.val_injective
  · rw [← subgroupActionHom_range ρ W P hstable]
    exact hP.of_surjective _ (subgroupActionHom ρ W P hstable).rangeRestrict_surjective
  · exact hd

/-- The source Frattini subgroup lies in the literal pointwise kernel,
by its image in the Frattini subgroup of the restricted action image. -/
theorem frattini_fixes_small (ρ : Representation (ZMod 2) G V)
    (W : Submodule (ZMod 2) V) (P : Subgroup G) (hP : IsPGroup 3 P)
    (hstable : P ≤ subspaceStabilizer ρ W) (hd : Module.finrank (ZMod 2) W ≤ 4) :
    (frattini P).map P.subtype ≤ subspaceKernel ρ W P := by
  let f := (subgroupActionHom ρ W P hstable).rangeRestrict
  have hi : IsPGroup 3 (subgroupActionHom ρ W P hstable).range :=
    hP.of_surjective f (subgroupActionHom ρ W P hstable).rangeRestrict_surjective
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let : Fact (IsPGroup 3 P) := ⟨hP⟩
  let : Fact (IsPGroup 3 (subgroupActionHom ρ W P hstable).range) := ⟨hi⟩
  let : IsElementaryAbelian 3 (subgroupActionHom ρ W P hstable).range := by
    rw [subgroupActionHom_range]
    exact small_image_elementary ρ W P hP hstable hd
  have hm := frattini_map_le_of_isPGroup (p := 3) f
  rw [frattini_eq_bot_of_isElementaryAbelian
    (R := (subgroupActionHom ρ W P hstable).range) (p := 3)] at hm
  rintro x ⟨p, hp, rfl⟩
  refine ⟨p.property, ?_⟩
  have he : f p = 1 := mem_bot.mp (hm (mem_map_of_mem f hp))
  have he' : subgroupActionHom ρ W P hstable p = 1 := congrArg Subtype.val he
  intro w hw
  have h := congrArg (fun g => subspaceImageRepresentation ρ W g ⟨w, hw⟩) he'
  exact congrArg (fun v : W => (v : V)) h

end CFSG.Quasithin.ChapterD.ElementaryCore.SupportExclusion
