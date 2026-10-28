module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.Plane
public import Theory.Representation.PSL3Two.NaturalPlaneStabilizer
public import Theory.Representation.BinaryConjugationSection.QuadraticPair

/-!
# The original second Ru parabolic in natural coordinates

The faithful natural coordinates identify the original Sylow-invariant
four-group with a binary plane. Equivariance identifies its normalizer in L
with the inverse image of the plane stabilizer. An adapted basis then gives
the actual conjugate line parabolic, with the original quotient map retained.

Source: Aschbacher–Smith, J.4, opening notation, printed p.440.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open BinaryLinearThree
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The literal plane in the original natural coordinates. -/
def Plane.naturalSpace : Submodule (ZMod 2) Vector :=
  d.ru1.natural.imageSpace p.group

private theorem coordinates_injective : Function.Injective d.ru1.natural.coordinates := by
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [d.ru1.natural.kernel_eq, bot_subgroupOf]

/-- The faithful coordinates recover membership in the original plane. -/
theorem Plane.mem_naturalSpace (v : d.V) :
    (d.ru1.natural.coordinates v).toAdd ∈ p.naturalSpace ↔ (v : G) ∈ p.group := by
  rw [Plane.naturalSpace, d.ru1.natural.mem_imageSpace_iff]
  constructor
  · rintro ⟨a,ha,he⟩
    have h : a = v := coordinates_injective (Multiplicative.toAdd.injective he)
    exact h ▸ ha
  · intro hv; exact ⟨v,hv,rfl⟩

/-- The natural plane has precisely the original four elements. -/
theorem Plane.card_naturalSpace : Nat.card p.naturalSpace = 4 := by
  let f : p.group → p.naturalSpace := fun v =>
    ⟨(d.ru1.natural.coordinates ⟨v,p.le_seed v.property⟩).toAdd,
      (p.mem_naturalSpace _).mpr v.property⟩
  have hi : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun v : d.V => (v : G)) (coordinates_injective
      (Multiplicative.toAdd.injective (congrArg Subtype.val h)))
  have hs : Function.Surjective f := by
    rintro ⟨v,hv⟩
    obtain ⟨a,ha,he⟩ := (d.ru1.natural.mem_imageSpace_iff p.group v).mp hv
    exact ⟨⟨a,ha⟩,Subtype.ext he⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm.trans p.card

/-- The actual plane is two-dimensional. -/
theorem Plane.finrank_naturalSpace : Module.finrank (ZMod 2) p.naturalSpace = 2 := by
  apply Nat.pow_right_injective (by decide : 1 < 2)
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := p.naturalSpace)
  rw [Nat.card_zmod,p.card_naturalSpace] at h
  exact h.symm

/-- The original normalizer and the literal quotient stabilizer agree. -/
theorem Plane.mem_parabolic_iff (l : d.L) :
    (l : G) ∈ p.parabolic ↔
      d.ru1.quotientMap l ∈ NaturalPlaneStabilizer.stabilizer p.naturalSpace := by
  rw [p.mem_parabolic, NaturalPlaneStabilizer.mem_stabilizer]
  constructor
  · intro hl v
    obtain ⟨a,ha⟩ := d.ru1.natural.onto (Multiplicative.ofAdd v)
    have hact := d.ru1.natural.equivariant l a
    change (d.ru1.natural.coordinates _).toAdd = W (d.ru1.quotientMap l)
      (d.ru1.natural.coordinates a).toAdd at hact
    rw [ha] at hact
    simp only [toAdd_ofAdd] at hact
    rw [← hact,p.mem_naturalSpace]
    have hm := (mem_normalizer_iff.mp hl.2 (a : G)).symm
    rw [← p.mem_naturalSpace a,ha] at hm
    exact hm
  · intro hl
    refine ⟨l.property,mem_normalizer_iff.mpr (fun a => ?_)⟩
    have hV := mem_normalizer_iff.mp (d.ru1.natural.normalized l.property) a
    by_cases ha : a ∈ d.V
    · let v : d.V := ⟨a,ha⟩
      have hact := d.ru1.natural.equivariant l v
      change (d.ru1.natural.coordinates _).toAdd = W (d.ru1.quotientMap l)
        (d.ru1.natural.coordinates v).toAdd at hact
      have hm := hl (d.ru1.natural.coordinates v).toAdd
      rw [← hact,p.mem_naturalSpace,p.mem_naturalSpace] at hm
      exact hm.symm
    · have hn : a ∉ p.group := fun h => ha (p.le_seed h)
      have hn' : (l : G) * a * (l : G)⁻¹ ∉ p.group :=
        fun h => ha (hV.mpr (p.le_seed h))
      exact iff_of_false hn hn'

/-- The quotient of the source normalizer is an actual conjugate line parabolic. -/
theorem Plane.parabolic_image : ∃ g : Group,
    (p.parabolic.subgroupOf d.L).map d.ru1.quotientMap =
      Matrix.PSL3Two.lineParabolicSL.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g,hg⟩ := NaturalPlaneStabilizer.exists_stabilizer_eq p.naturalSpace
    p.finrank_naturalSpace
  refine ⟨g,?_⟩
  rw [← hg]
  ext a
  constructor
  · rintro ⟨l,hl,rfl⟩
    exact (p.mem_parabolic_iff l).mp hl
  · intro ha
    obtain ⟨l,rfl⟩ := d.ru1.quotient_surjective a
    exact ⟨l,(p.mem_parabolic_iff l).mpr ha,rfl⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
