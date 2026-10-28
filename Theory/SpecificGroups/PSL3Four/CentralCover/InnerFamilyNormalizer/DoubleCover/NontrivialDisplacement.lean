module

public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.RootPairs
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.SourceData
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.RootLifting
public import Theory.SpecificGroups.PSL3Four.CentralCover.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement.UnitaryCoordinates
public import Theory.GroupTheory.Commutator.CentralSylowTransfer

/-!
# The Sylow-transfer route to nontrivial graph-field displacement

For a perfect cover with center C₂, central Sylow transfer places the covering
kernel in the derived subgroup of every Sylow two-subgroup. A compatible
swapped-root presentation makes trivial displacement imply injectivity on
that derived subgroup. These conclusions contradict its nontrivial central
kernel, proving surjectivity of both constructed displacement maps.

The final theorems construct the presentation from the concrete unitary Sylow
coordinates and the actual lifted graph-field action. Only the source
I.2.2(3b) involution-lifting clause remains explicit. No root presentation,
nontrivial displacement, or residual-model hypothesis is assumed.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
I.2.2(3) and its transfer observation (i), printed pp.409–410;
16.4.9(2), printed p.1191.
-/

@[expose] public section
open Subgroup
open scoped commutatorElement
namespace Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
variable {H : Type*} [Group H]

/-- Sylow transfer turns the local commutator calculation into surjectivity of
 the displacement of the original cover and the original automorphism. -/
theorem displacement_surjective_of_root_pair [Finite H]
    (c : PerfectCentralCovering.Cover H PSL) (a : MulAut H)
    (ha : ∀ x, c.toMonoidHom (a x) =
      ExtendedCentralizer.ProjectiveFixer.graphField (c.toMonoidHom x))
    (ha2 : a ^ 2 = 1) (hk : c.toMonoidHom.ker = center H)
    (hZ : Nat.card (center H) = 2) (d : LiftedRootPair c a) :
    Function.Surjective (displacement c a ha) := by
  classical
  let := c.isPerfect
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply (displacement_surjective_iff c a ha hZ).mpr
  by_contra hn
  have hfixed (x : fixedPreimage c) : a (x : H) = x := by
    by_contra h
    exact hn ⟨x, h⟩
  have hb : d.action ^ 2 = 1 := by
    ext x
    simpa only [pow_two, MulAut.mul_apply, MulAut.one_apply, d.compatible] using
      involutive_apply a ha2 (x : H)
  let f : d.sylow →* PSL := c.toMonoidHom.comp (d.sylow : Subgroup H).subtype
  have hbot : f.ker ⊓ _root_.commutator d.sylow = ⊥ :=
    d.roots.kernel_inf_derived_eq_bot f d.action hb (by
      intro x hx
      have hproj : c.toMonoidHom (a x) = c.toMonoidHom x := by
        simpa only [f, MonoidHom.comp_apply, Subgroup.subtype_apply, d.compatible] using hx
      have hm : (x : H) ∈ fixedPreimage c := by
        change c.toMonoidHom x ∈ ExtendedCentralizer.ProjectiveFixer.graphField.fixedSubgroup
        rw [MulAut.mem_fixedSubgroup]
        exact (ha x).symm.trans hproj
      apply Subtype.ext
      exact (d.compatible x).trans (hfixed ⟨x, hm⟩))
  obtain ⟨z, hz, _⟩ := (Nat.card_eq_two_iff' (1 : center H)).mp hZ
  have hp : IsPGroup 2 (center H) := IsPGroup.of_card (p := 2) (n := 1) (by simpa using hZ)
  have hzS : (z : H) ∈ (d.sylow : Subgroup H) := hp.le_sylow_of_normal d.sylow z.property
  have hzD : (z : H) ∈ ⁅(d.sylow : Subgroup H), (d.sylow : Subgroup H)⁆ :=
    center_inf_commutator_inf_sylow_le_commutator d.sylow
      ⟨⟨z.property, by rw [Group.IsPerfect.commutator_eq_top]; exact mem_top _⟩, hzS⟩
  rw [← map_subtype_commutator] at hzD
  obtain ⟨w, hw, hwz⟩ := hzD
  change (w : H) = z at hwz
  have hwker : w ∈ f.ker := by
    change c.toMonoidHom (w : H) = 1
    rw [hwz]
    exact (hk.symm ▸ z.property : (z : H) ∈ c.toMonoidHom.ker)
  have hwone : w = 1 := mem_bot.mp (hbot ▸ (show w ∈ f.ker ⊓ _root_.commutator d.sylow from ⟨hwker, hw⟩))
  apply hz
  apply Subtype.ext
  exact hwz.symm.trans (congrArg Subtype.val hwone)

/-- The same conclusion for the descended character on the projective fixed group. -/
theorem projectiveDisplacement_surjective_of_root_pair [Finite H]
    (c : PerfectCentralCovering.Cover H PSL) (a : MulAut H)
    (ha : ∀ x, c.toMonoidHom (a x) =
      ExtendedCentralizer.ProjectiveFixer.graphField (c.toMonoidHom x))
    (ha2 : a ^ 2 = 1) (hk : c.toMonoidHom.ker = center H)
    (hZ : Nat.card (center H) = 2) (d : LiftedRootPair c a) :
    Function.Surjective (projectiveDisplacement c a ha hk hZ) :=
  (projectiveDisplacement_surjective_iff c a ha hk hZ).mpr
    (displacement_surjective_of_root_pair c a ha ha2 hk hZ d)

/-- For a center-C₂ perfect cover, source involution lifting forces the actual
graph-field displacement onto the covering center. The unitary Sylow model
and its lifted root presentation are constructed, rather than assumed. -/
theorem displacement_surjective [Finite H]
    (c : PerfectCentralCovering.Cover H PSL) (a : MulAut H)
    (ha : ∀ x, c.toMonoidHom (a x) =
      ExtendedCentralizer.ProjectiveFixer.graphField (c.toMonoidHom x))
    (ha2 : a ^ 2 = 1) (hk : c.toMonoidHom.ker = center H)
    (hZ : Nat.card (center H) = 2) (hlift : InvolutionLifting c) :
    Function.Surjective (displacement c a ha) := by
  obtain ⟨d⟩ := nonempty_liftedRootPair c hk hZ a ha2 ha hlift unitarySylowModel
  exact displacement_surjective_of_root_pair c a ha ha2 hk hZ d

/-- The descended displacement on the concrete projective graph-field fixed
group is surjective, with only I.2.2(3b) involution lifting left explicit. -/
theorem projectiveDisplacement_surjective [Finite H]
    (c : PerfectCentralCovering.Cover H PSL) (a : MulAut H)
    (ha : ∀ x, c.toMonoidHom (a x) =
      ExtendedCentralizer.ProjectiveFixer.graphField (c.toMonoidHom x))
    (ha2 : a ^ 2 = 1) (hk : c.toMonoidHom.ker = center H)
    (hZ : Nat.card (center H) = 2) (hlift : InvolutionLifting c) :
    Function.Surjective (projectiveDisplacement c a ha hk hZ) :=
  (projectiveDisplacement_surjective_iff c a ha hk hZ).mpr
    (displacement_surjective c a ha ha2 hk hZ hlift)

end Matrix.PSL3Four.InnerFamilyNormalizer.DoubleCover.NontrivialDisplacement
