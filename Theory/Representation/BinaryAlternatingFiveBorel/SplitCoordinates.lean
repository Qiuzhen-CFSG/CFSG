module
public import Theory.Representation.BinaryOffender.IrreducibleTransport
public import Theory.Representation.BinaryAlternatingFiveBorel
/-!
# Coordinates on the moved space of a split A₄ action

A fixed complementary summand contributes no commutators. An equivariant
identification of the other summand with the natural five-point core, together
with a surjective map onto its A₄ point stabilizer, therefore identifies the
whole commutator with the concrete moved three-space. Its checked submodule
classification excludes every invariant plane contained in that commutator.
Source application: Aschbacher–Smith, 13.6.15, printed p.930.
-/

public section
open Subgroup Representation Representation.BinaryOffender
namespace BinaryPermutation.AlternatingFiveBorel
variable {H W : Type*} [Group H] [AddCommGroup W] [Module (ZMod 2) W]
private theorem source_commutator :
    subspaceCommutator (alternatingCoreRepresentation (Fin 5)) ⊤ B = moved := by
  rw [← commutator_eq_moved]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, v, _, rfl⟩
    exact Coinvariants.sub_mem_ker (ρ := action) ⟨g, hg⟩ v
  · apply Submodule.span_le.mpr
    rintro _ ⟨⟨g, v⟩, rfl⟩
    exact Submodule.subset_span ⟨g.val, g.property, v, Submodule.mem_top, rfl⟩

theorem split_commutator (ρ : Representation (ZMod 2) H W)
    (I J : Submodule (ZMod 2) W) (hs : I ⊔ J = ⊤)
    (hJ : ∀ h (z : J), ρ h z=z) :
    subspaceCommutator ρ ⊤ ⊤ = subspaceCommutator ρ I ⊤ := by
  apply le_antisymm
  swap
  · apply Submodule.span_mono
    rintro _ ⟨h,hh,w,hw,rfl⟩
    exact ⟨h,hh,w,Submodule.mem_top,rfl⟩
  apply Submodule.span_le.mpr
  rintro _ ⟨h,_,x,_,rfl⟩
  have hx : x ∈ I ⊔ J := hs.symm ▸ Submodule.mem_top
  obtain ⟨w,hw,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add, hJ h ⟨z,hz⟩]
  simpa only [add_sub_add_right_eq_sub, subspaceCommutator] using
    (Submodule.subset_span ⟨h,mem_top h,w,hw,rfl⟩ : ρ h w-w ∈ subspaceCommutator ρ I ⊤)

theorem commutator_coordinates (ρ : Representation (ZMod 2) H W)
    (I J : Submodule (ZMod 2) W) (hs : I ⊔ J = ⊤)
    (hJ : ∀ h (z : J), ρ h z=z)
    (e : I ≃ₗ[ZMod 2] core (Fin 5)) (q : H →* B) (hq : Function.Surjective q)
    (he : ∀ h (w : I), ρ h w = (e.symm (action (q h) (e w)) : W)) :
    ∃ f : moved →ₗ[ZMod 2] W, Function.Injective f ∧
      LinearMap.range f = subspaceCommutator ρ ⊤ ⊤ ∧
      ∀ h w, ρ h (f w) = f (movedRepresentation (q h) w) := by
  let j : core (Fin 5) →ₗ[ZMod 2] W := I.subtype.comp e.symm.toLinearMap
  have hj : Function.Injective j := I.subtype_injective.comp e.symm.injective
  have hI : (⊤ : Submodule (ZMod 2) (core (Fin 5))).map j = I := by
    apply le_antisymm
    · rintro _ ⟨x,_,rfl⟩; exact (e.symm x).property
    · intro w hw
      exact ⟨e ⟨w,hw⟩,Submodule.mem_top,congrArg Subtype.val (e.symm_apply_apply _)⟩
  let a : H →* alternatingGroup (Fin 5) := B.subtype.comp q
  have ha : (⊤ : Subgroup H).map a=B := by
    ext b
    constructor
    · rintro ⟨h,_,rfl⟩; exact (q h).property
    · intro hb
      obtain ⟨h,he⟩ := hq ⟨b,hb⟩
      exact ⟨h,mem_top h,congrArg Subtype.val he⟩
  have hact : ∀ h x, ρ h (j x) = j (alternatingCoreRepresentation (Fin 5) (a h) x) := by
    intro h x
    change ρ h (e.symm x : W) = (e.symm (action (q h) x) : W)
    simpa only [e.apply_symm_apply] using he h (e.symm x)
  have hc := subspaceCommutator_map_embedding ρ (alternatingCoreRepresentation (Fin 5)) a j hact ⊤ ⊤
  rw [hI,ha,source_commutator] at hc
  have hr : moved.map j = subspaceCommutator ρ ⊤ ⊤ := by
    rw [split_commutator ρ I J hs hJ]
    exact hc.symm
  refine ⟨j.comp moved.subtype,hj.comp moved.subtype_injective,?_,?_⟩
  · rw [LinearMap.range_comp, Submodule.range_subtype]
    exact hr
  · intro h w
    change ρ h (j w.val) = j ((movedRepresentation (q h) w).val)
    rw [movedRepresentation_apply]
    exact hact h w

theorem no_invariant_plane_in_commutator (ρ : Representation (ZMod 2) H W)
    (I J : Submodule (ZMod 2) W) (hs : I ⊔ J = ⊤)
    (hJ : ∀ h (z : J), ρ h z=z)
    (e : I ≃ₗ[ZMod 2] core (Fin 5)) (q : H →* B) (hq : Function.Surjective q)
    (he : ∀ h (w : I), ρ h w = (e.symm (action (q h) (e w)) : W))
    (P : Submodule (ZMod 2) W) (hP : ∀ h x, x ∈ P → ρ h x ∈ P)
    (hPC : P ≤ subspaceCommutator ρ ⊤ ⊤) : Module.finrank (ZMod 2) P ≠ 2 := by
  obtain ⟨f,hf,hr,ha⟩ := commutator_coordinates ρ I J hs hJ e q hq he
  let Q := P.comap f
  have hQ : ∀ b x, x ∈ Q → movedRepresentation b x ∈ Q := by
    intro b x hx
    obtain ⟨h,rfl⟩ := hq b
    change f (movedRepresentation (q h) x) ∈ P
    rw [←ha]
    exact hP h (f x) hx
  have hmap : Q.map f = P := by
    rw [Submodule.map_comap_eq]
    exact inf_eq_right.mpr (hr.symm ▸ hPC)
  have hd : Module.finrank (ZMod 2) Q = Module.finrank (ZMod 2) P :=
    (Submodule.equivMapOfInjective f hf Q).finrank_eq.trans (congrArg (fun S : Submodule (ZMod 2) W => Module.finrank (ZMod 2) S) hmap)
  exact hd ▸ no_invariant_plane Q hQ


/-- The same obstruction with the quotient convention for the natural module. -/
theorem no_invariant_plane_of_natural_split (ρ : Representation (ZMod 2) H W)
    (I J : Submodule (ZMod 2) W) (hs : I ⊔ J = ⊤)
    (hJ : ∀ h (z : J), ρ h z=z)
    (e : I ≃ₗ[ZMod 2] natural (Fin 5)) (q : H →* B) (hq : Function.Surjective q)
    (he : ∀ h (w : I), ρ h w =
      (e.symm (naturalRepresentation (Fin 5) (q h).val.val (e w)) : W))
    (P : Submodule (ZMod 2) W) (hP : ∀ h x, x ∈ P → ρ h x ∈ P)
    (hPC : P ≤ subspaceCommutator ρ ⊤ ⊤) : Module.finrank (ZMod 2) P ≠ 2 := by
  let t := coreEquivNatural (Fin 5) (by decide)
  let c := e.trans t.symm
  apply no_invariant_plane_in_commutator ρ I J hs hJ c q hq ?_ P hP hPC
  intro h w
  have ht : t (action (q h) (t.symm (e w))) =
      naturalRepresentation (Fin 5) (q h).val.val (e w) := by
    have hh := coreEquivNatural_equivariant (Fin 5) (by decide) (q h).val.val (t.symm (e w))
    change t (action (q h) (t.symm (e w))) =
      naturalRepresentation (Fin 5) (q h).val.val (t (t.symm (e w))) at hh
    rwa [t.apply_symm_apply] at hh
  change ρ h w = (e.symm (t (action (q h) (t.symm (e w)))) : W)
  rw [ht]
  exact he h w

end BinaryPermutation.AlternatingFiveBorel
