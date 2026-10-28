module

public import Theory.SpecificGroups.ReeF4.LocalBlockInput.OuterOddSubgroups.RootPair

/-!
# The four signed simple blocks for Ree pair rigidity

The exceptional node orbits are `{0,3}` and `{1,2}`. For each orbit we take
all roots supported on those nodes, of one specified sign, generate their
split root subgroup, and intersect with the supplied twist-fixed group.
Thus the positive blocks use the A₁ × A₁ and B₂ positive subsystems,
respectively; the negative blocks use their opposites. They are the simple
relative root groups in the construction of GLS3, 2.3.6 and Table 2.4,
types VI and V. In particular the B₂ block includes its nonsimple roots.

The proofs here give containment in the specified unipotent pair, Frobenius
invariance, and an extensionality lemma conditional on generation. Generation
and preservation by an arbitrary pair-preserving automorphism are not assumed
as properties of the construction and remain separate geometric theorems.

Source: GLS3, §§2.3–2.5, especially 2.3.6–8, 2.4.1, and 2.5.1.
-/

@[expose] public section
namespace ReeF4.LocalBlockInput.PairRigidity

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem Subgroup
open LargeLocalSeeds
variable {m : ℕ}

/-- Roots in a signed simple Levi block. `true` denotes the positive sign. -/
def IsSimpleBlockRoot (s : Side) (positive : Bool) (r : F4Chevalley.Root) : Prop :=
  (∀ i, i ∉ leviNodes s → typeF4SimpleCoefficient r.val i = 0) ∧
    (if positive then typeF4RootPairing_base.IsPos r
      else ¬ typeF4RootPairing_base.IsPos r)

/-- The split root subgroup of a signed simple Levi block. -/
noncomputable def splitSimpleBlock (m : ℕ) (s : Side) (positive : Bool) :
    Subgroup (SplitGroup m) :=
  closure {x | ∃ (r : F4Chevalley.Root) (t : CoefficientField m),
    IsSimpleBlockRoot s positive r ∧ x = rootGeneratorInGroup m r t}

/-- The actual twist-fixed intersection of a signed simple block. -/
noncomputable def simpleBlock (d : LocalBlockInput m) (s : Side) (positive : Bool) :
    Subgroup d.fixedGroup := (splitSimpleBlock m s positive).subgroupOf d.fixedGroup

/-- Each of the four specified subgroups is preserved individually. -/
def PreservesSimpleBlocks (d : LocalBlockInput m) (a : MulAut d.fixedGroup) : Prop :=
  ∀ s positive, (simpleBlock d s positive).map a.toMonoidHom = simpleBlock d s positive

theorem simpleBlock_positive_le (d : LocalBlockInput m) (s : Side) :
    simpleBlock d s true ≤ standardUnipotent d := by
  have h : splitSimpleBlock m s true ≤ splitUnipotent m := by
    apply Subgroup.closure_mono
    rintro x ⟨r, t, hr, rfl⟩
    exact ⟨r, t, hr.2, rfl⟩
  exact fun _ hx => h hx

theorem simpleBlock_negative_le (d : LocalBlockInput m) (s : Side) :
    simpleBlock d s false ≤ oppositeUnipotent d := by
  have h : splitSimpleBlock m s false ≤ splitNegativeUnipotent m := by
    apply Subgroup.closure_mono
    rintro x ⟨r, t, hr, rfl⟩
    exact ⟨r, t, hr.2, rfl⟩
  exact fun _ hx => h hx

private theorem map_eq_self_of_mem {G : Type*} [Group G] [Finite G]
    (a : MulAut G) (H : Subgroup G) (h : ∀ x ∈ H, a x ∈ H) :
    H.map a.toMonoidHom = H := by
  let f : H →* H := (a.toMonoidHom.comp H.subtype).codRestrict H
    (fun x => h x x.property)
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (a.injective (congrArg Subtype.val hxy))
  have hs := (Finite.injective_iff_bijective.mp hf).surjective
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    exact h y hy
  · intro x hx
    obtain ⟨y, hy⟩ := hs ⟨x, hx⟩
    exact ⟨y, y.property, congrArg Subtype.val hy⟩

/-- Frobenius preserves each simple block by its root-parameter formula. -/
theorem fieldAutomorphism_preservesSimpleBlocks (d : LocalBlockInput m) :
    PreservesSimpleBlocks d d.fieldAutomorphism := by
  intro s positive
  apply map_eq_self_of_mem
  intro x hx
  have h : splitSimpleBlock m s positive ≤
      (splitSimpleBlock m s positive).comap (splitFrobenius m) := by
    apply (closure_le _).mpr
    rintro y ⟨r, t, hr, rfl⟩
    change splitFrobenius m (rootGeneratorInGroup m r t) ∈ splitSimpleBlock m s positive
    rw [splitFrobenius_rootGenerator]
    exact subset_closure ⟨r, t ^ 2, hr, rfl⟩
  exact h hx

/-- Once the four fixed blocks generate, agreement there determines a homomorphism.
The generation premise concerns the fixed group, not the split group. -/
theorem hom_ext_of_simpleBlocks_generate (d : LocalBlockInput m)
    (hgen : (⨆ s, ⨆ positive, simpleBlock d s positive) = ⊤)
    {H : Type*} [Monoid H] (f g : d.fixedGroup →* H)
    (h : ∀ s positive, ∀ x ∈ simpleBlock d s positive, f x = g x) : f = g := by
  have hle : (⨆ s, ⨆ positive, simpleBlock d s positive) ≤ f.eqLocus g :=
    iSup_le fun s => iSup_le fun positive => h s positive
  rw [hgen] at hle
  exact MonoidHom.ext fun x => hle (mem_top x)

end ReeF4.LocalBlockInput.PairRigidity
end
