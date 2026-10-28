module
public import CFSG.Quasithin.ChapterB.Section05.Quasisimple.SourceCompletion.BinarySemisimple

/-!
# Actual natural coordinates for proper source terms

A homogeneous action contains copies of one irreducible module. Projection of
an already marked natural submodule to a nonzero coordinate is an isomorphism
by irreducibility. Applying that same intertwiner to every coordinate gives a
single common natural group mark, over every binary field.

The strict B.5.1 conclusion on a fully moved fixed-free binary action then
gives repeated-natural or natural-plus-dual coordinates. The final chief-flag
consumer proves the source hypotheses and strict dimension decrease for the
original proper term, and constructs its natural submodule from the first
literal chief section. It does not assume the desired full classifier.

Source: Aschbacher--Smith, B.5.1, printed pp.101--102, the maximal-submodule
alternatives (A)--(C). Full-module recombination is the subsequent step.
-/

public section
open Representation Representation.BinaryOffender Theory.GroupTheory Subgroup
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
universe u v
variable {G : Type u} [Group G]
  {V : Type v} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

/-- A natural submodule fixes the common mark of an arbitrary homogeneous
chart. A nonzero coordinate projection identifies its irreducible summand. -/
theorem homogeneous_natural_coordinates
    {H X : Type*} [Group H] [AddCommGroup X] [Module (ZMod 2) X]
    {σ : Representation (ZMod 2) H X} (e : ActionEquiv ρ σ)
    (hh : IsHomogeneousAction σ) (N : Subrepresentation ρ)
    (F : BinaryField) {d : ℕ} (hd : 2 ≤ d) (hn : IsLinearNatural N.toRepresentation F d) :
    ∃ r : ℕ, 0 < r ∧ IsRepeatedLinearNatural ρ F d r := by
  classical
  obtain ⟨r,hr,W,hi,f,hf⟩ := hh
  obtain ⟨a⟩ := hn
  let τ := W.toRepresentation.comp e.groupEquiv.toMonoidHom
  let b : ActionEquiv τ W.toRepresentation :=
    ⟨e.groupEquiv,LinearEquiv.refl _ _,fun _ _ => rfl⟩
  let : IsIrreducible τ := ExtensionConsequences.irreducible_of_equiv b hi
  let : IsIrreducible N.toRepresentation := ExtensionConsequences.irreducible_of_equiv a
    (ExtensionConsequences.linearNatural_irreducible F hd)
  let : Nontrivial N.toSubmodule := Subrepresentation.irreducible_module_nontrivial N.toRepresentation
  obtain ⟨v,hv⟩ := exists_ne (0 : N.toSubmodule)
  have hne : f (e.linearEquiv v.val) ≠ 0 := by
    intro hz
    apply hv
    apply Subtype.ext
    apply e.linearEquiv.injective
    apply f.injective
    simpa using hz
  obtain ⟨i,hi⟩ : ∃ i : Fin r, f (e.linearEquiv v.val) i ≠ 0 := by
    by_contra! h
    exact hne (funext h)
  let p : N.toRepresentation.IntertwiningMap τ :=
    ((LinearMap.proj i).comp (f.toLinearMap.comp (e.linearEquiv.toLinearMap.comp N.toSubmodule.subtype))).intertwiningMap_of_isIntertwiningMap _ _ (by
      intro g v
      change f (e.linearEquiv (ρ g v.val)) i = W.toRepresentation (e.groupEquiv g) (f (e.linearEquiv v.val) i)
      rw [e.intertwines,hf]
      rfl)
  have hp : p ≠ 0 := by
    intro hp
    apply hi
    exact congrArg (fun q : N.toRepresentation.IntertwiningMap τ => q v) hp
  let E := p.ofBijective ((IsIrreducible.bijective_or_eq_zero p).resolve_right hp)
  let q : W.toSubmodule ≃ₗ[ZMod 2] (Fin d → F.Carrier) :=
    E.symm.toLinearEquiv.trans a.linearEquiv
  refine ⟨r,hr,⟨⟨a.groupEquiv,
    (e.linearEquiv.trans f).trans (LinearEquiv.piCongrRight fun _ : Fin r => q),?_⟩⟩⟩
  intro g x
  funext j
  change a.linearEquiv (E.symm (f (e.linearEquiv (ρ g x)) j)) =
    linearNatural F d (a.groupEquiv g) (a.linearEquiv (E.symm (f (e.linearEquiv x) j)))
  rw [e.intertwines,hf]
  change a.linearEquiv (E.symm (τ g (f (e.linearEquiv x) j))) = _
  have he := IntertwiningMap.isIntertwining (ρ := τ) (σ := N.toRepresentation) E.symm.toIntertwiningMap g (f (e.linearEquiv x) j)
  exact (congrArg a.linearEquiv he).trans (a.intertwines g _)

/-- In the fully moved, fixed-free binary action, the complete source
conclusion and one actual natural submodule yield explicit repeated-natural
or natural-plus-dual coordinates. This is used only after strict induction. -/
theorem binary_coordinates_of_source_conclusion
    {L : Subgroup G} (c : SourceInduction.ProjectiveLine.QuasisimpleSourceConclusion ρ L)
    (hL : L = ⊤) (hm : moved ρ L = ⊤) (hz : fixedSpace ρ L = ⊥)
    (N : Subrepresentation ρ) {d : ℕ} (hd : d = 4 ∨ d = 5)
    (hn : IsLinearNatural N.toRepresentation BinaryField.two d) :
    (∃ r : ℕ, 0 < r ∧ IsRepeatedLinearNatural ρ BinaryField.two d r) ∨
      IsNaturalPlusDual ρ d := by
  let S := c.sectionData
  have hs : S.space.toSubmodule = ⊤ := S.space_eq.trans hm
  let E : S.space.toSubmodule ≃ₗ[ZMod 2] V :=
    LinearEquiv.ofBijective S.space.toSubmodule.subtype
      ⟨Subtype.val_injective,fun v => ⟨⟨v,hs ▸ Submodule.mem_top⟩,rfl⟩⟩
  let e : ActionEquiv (S.space.toRepresentation.comp L.subtype) ρ :=
    ⟨(MulEquiv.subgroupCongr hL).trans Subgroup.topEquiv,E,fun _ _ => rfl⟩
  have hzρ : ρ.invariants = ⊥ := by
    apply bot_unique
    intro v hv
    have hvL : v ∈ fixedSpace ρ L := fun g => hv g.val
    rw [hz] at hvL
    exact hvL
  rcases c.clause_three with hh | ⟨d',hd',hn'⟩
  · left
    have hS := ExtensionConsequences.invariants_of_equiv e hzρ
    let q := ExtensionConsequences.movedQuotientEquiv S hS
    let t : ActionEquiv (S.action.comp L.subtype) ρ :=
      ⟨q.groupEquiv.trans e.groupEquiv,q.linearEquiv.trans e.linearEquiv,
        fun g v => (congrArg e.linearEquiv (q.intertwines g v)).trans
          (e.intertwines (q.groupEquiv g) (q.linearEquiv v))⟩
    exact homogeneous_natural_coordinates ρ (ExtensionConsequences.actionSymm t) hh N
      BinaryField.two (by omega) hn
  · right
    obtain ⟨a⟩ := hn
    obtain ⟨b⟩ := hn'
    have heq : d' = d := binary_degree_eq hd' hd
      (b.groupEquiv.symm.trans (e.groupEquiv.trans a.groupEquiv))
    subst d'
    let t := ExtensionConsequences.actionSymm e
    refine ⟨⟨t.groupEquiv.trans b.groupEquiv,t.linearEquiv.trans b.linearEquiv,?_⟩⟩
    intro g v
    exact (congrArg b.linearEquiv (t.intertwines g v)).trans
      (b.intertwines (t.groupEquiv g) (t.linearEquiv v))


/-- Every actual nonzero proper binary chief-flag term has positive repeated
natural or natural-plus-dual coordinates under the original whole actor.
Its classifier application is precisely the strict dimension induction. -/
theorem binary_source_flag_coordinates [Finite G] [FiniteDimensional (ZMod 2) V]
    {K : CFSG.Quasithin.GroupClass.{u}} (hK : IrreducibleBranch.ContainsSimpleTwoGroups K)
    (earlier : SourceInduction.ProjectiveLine.IrreducibleClassificationInput.{u,v} K)
    (ih : SmallerDimensionInput.{u,v} K (Module.finrank (ZMod 2) V))
    [IsQuasisimple (generalizedFitting G)] (hsq : IsSQTK K (generalizedFitting G))
    (hwhole : generalizedFitting G = ⊤)
    (hf : Function.Injective ρ) (hcore : pCore 2 G = ⊥)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (mark : generalizedFitting G ≃* SL(d,ZMod 2))
    (f : ReducibleChiefFlag ρ (generalizedFitting G))
    (A : Subgroup G) (hA : IsMinimalBestOffender ρ A)
    (hm : Coinvariants.ker (ρ.comp (generalizedFitting G).subtype) = ⊤)
    {i : ℕ} (hi0 : 0 < i) (hi : i < f.length) :
    (∃ r : ℕ, 0 < r ∧ IsRepeatedLinearNatural (f.chain i).toRepresentation BinaryField.two d r) ∨
      IsNaturalPlusDual (f.chain i).toRepresentation d := by
  have hgen : generalizedFitting G ⊔ A = ⊤ := by rw [hwhole,top_sup_eq]
  obtain ⟨hfi,hmi,hzi,_⟩ := binary_source_flag_recursion ρ hK earlier ih hsq hf hcore
    hd mark f A hA hgen hm hi0 hi
  obtain ⟨hindices,_⟩ := binary_source_flag_pure ρ hK earlier hsq hf hcore hd mark f A hA hgen hm
  have hzero : 0 ∈ f.noncentral := by rw [hindices]; exact Finset.mem_range.mpr (by omega)
  have hnfirst := first_chief_natural ρ (generalizedFitting G) f
    (binary_flag_natural ρ hK earlier hsq hf hcore hd mark f A hA hgen 0 hzero).2
  obtain ⟨a⟩ := hnfirst
  let eG := ((MulEquiv.subgroupCongr hwhole).trans Subgroup.topEquiv).symm
  let a' : ActionEquiv (f.chain 1).toRepresentation (linearNatural BinaryField.two d) :=
    ⟨eG.trans a.groupEquiv,a.linearEquiv,fun g v => a.intertwines (eG g) v⟩
  let N := sectionLower ρ (f.chain 1) (f.chain i)
  let q := sectionLowerEquiv ρ (f.monotone (show 1 ≤ i by omega))
  have hnN : IsLinearNatural N.toRepresentation BinaryField.two d :=
    ⟨⟨a'.groupEquiv,q.trans a'.linearEquiv,fun g v => a'.intertwines g (q v)⟩⟩
  have hff : IsFFModule (f.chain i).toRepresentation :=
    ⟨A,(bestOffender_on_subrepresentation ρ (f.chain i) hA.1).isOffender _⟩
  have hs := whole_source_hypothesis (f.chain i).toRepresentation hsq hwhole hcore hfi hff
  have hlt : (f.chain i).toSubmodule < ⊤ := by
    have hh := lt_of_lt_of_le (f.chief i hi).lt (f.monotone (show i+1 ≤ f.length by omega))
    rw [f.top] at hh
    exact hh
  have hdim : Module.finrank (ZMod 2) (f.chain i).toSubmodule < Module.finrank (ZMod 2) V := by
    simpa only [finrank_top] using Submodule.finrank_lt_finrank_of_lt hlt
  obtain ⟨c⟩ := ih G (f.chain i).toSubmodule (f.chain i).toRepresentation (generalizedFitting G) hdim hs
  exact binary_coordinates_of_source_conclusion _ c hwhole
    ((coinvariants_eq_moved (f.chain i).toRepresentation (generalizedFitting G)).symm.trans hmi)
    hzi N hd hnN

end CFSG.Quasithin.ChapterB.QuasisimpleSource.SourceCompletion
