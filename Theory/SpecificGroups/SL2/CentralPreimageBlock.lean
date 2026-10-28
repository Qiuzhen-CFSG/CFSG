module

public import GorensteinWalter.PSL2SchurMultiplier
public import Theory.GroupTheory.CentralExtensionSections
public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# The literal SL₂ block above a central quotient

The derived subgroup of the full inverse image of an SL₂ block maps
isomorphically onto that block. Universality of the actual SL₂ projection
removes the entire central kernel, including its odd part. The subgroup
retains its original projection and every normalizer from the quotient.

Source application: Aschbacher--Smith 6.1.4, the odd ternary case on p.666.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace Theory.SpecificGroups.SL2

/-- Take the derived subgroup of the full central preimage. Its original
projection is an isomorphism onto the prescribed SL₂ block. -/
theorem central_preimage_block
    {E C F : Type*} [Group E] [Finite E] [Group C] [Finite C]
    [Field F] [Finite F] [Fact (3 < Nat.card F)]
    (f : E →* C) (hf : Function.Surjective f) (hk : f.ker ≤ center E)
    (B : Subgroup C) (e : B ≃* SL(2,F))
    (ho : Odd (Nat.card F)) (h9 : Nat.card F ≠ 9) :
    let R := (commutator (B.comap f)).map (B.comap f).subtype
    Group.IsPerfect R ∧ Nonempty (R ≃* SL(2,F)) ∧ R.map f = B ∧
      (normalizer (B : Set C)).comap f ≤ normalizer (R : Set E) := by
  let A := B.comap f
  let g : A →* SL(2,F) := e.toMonoidHom.comp (f.subgroupComap B)
  have hg : Function.Surjective g := e.surjective.comp
    (f.subgroupComap_surjective_of_surjective B hf)
  have hgk : g.ker ≤ center A := by
    intro a ha
    have hfa : f a = 1 := by
      have hh : e ((f.subgroupComap B) a) = 1 := ha
      have he := e.injective (hh.trans e.map_one.symm)
      exact congrArg Subtype.val he
    apply mem_center_iff.mpr
    intro b
    exact Subtype.ext (mem_center_iff.mp (hk hfa) b)
  let d := CentralExtension.derivedCover g hg hgk
  let : Group.IsPerfect (commutator A) := d.isPerfect
  let : IsQuasisimple (commutator A) := d.isQuasisimple
  let c := GorensteinWalter.PSL2Cover.cover F
  let hu := GorensteinWalter.PSL2Cover.isUniversal_of_odd F ho h9
  let a := hu.lift (c.comp d.toCovering)
  have he : d.toMonoidHom.comp a.toMonoidHom = MonoidHom.id SL(2,F) := by
    apply PerfectCentralCovering.monoidHom_eq_of_isPerfect_of_comp_eq
      c.toMonoidHom c.ker_le_center
    have hh := congrArg Covering.toMonoidHom (hu.lift_fac (c.comp d.toCovering))
    ext x
    exact DFunLike.congr_fun hh x
  have hdi : Function.Injective d.toMonoidHom := by
    intro x y hxy
    obtain ⟨u,rfl⟩ := a.surjective x
    obtain ⟨v,rfl⟩ := a.surjective y
    have hu := DFunLike.congr_fun he u
    have hv := DFunLike.congr_fun he v
    change d.toMonoidHom (a u) = u at hu
    change d.toMonoidHom (a v) = v at hv
    exact congrArg a (hu.symm.trans (hxy.trans hv))
  let R := (commutator A).map A.subtype
  let er : commutator A ≃* R :=
    (commutator A).equivMapOfInjective A.subtype A.subtype_injective
  have hp : Group.IsPerfect R := Group.IsPerfect.map A.subtype
  let := hp
  have hmap : R.map f = B := by
    apply le_antisymm
    · rintro x ⟨y,⟨z,hz,rfl⟩,rfl⟩
      exact z.property
    · intro b hb
      obtain ⟨z,hz⟩ := d.surjective (e ⟨b,hb⟩)
      have hh : f ((z : A) : E) = b :=
        congrArg Subtype.val (e.injective hz)
      exact ⟨z,mem_map_of_mem A.subtype z.property,hh⟩
  refine ⟨hp,⟨er.symm.trans (MulEquiv.ofBijective d.toMonoidHom ⟨hdi,d.surjective⟩)⟩,
    hmap,?_⟩
  change (normalizer (B : Set C)).comap f ≤ normalizer (R : Set E)
  exact (congrArg (fun W : Subgroup C => (normalizer (W : Set C)).comap f)
    hmap.symm).le.trans (comap_normalizer_map_eq_of_perfect f hk R).le

end Theory.SpecificGroups.SL2
