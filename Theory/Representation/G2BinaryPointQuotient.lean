module
public import Theory.Representation.G2BinaryPointMarking
public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.FullSquareQuotient

/-!
# Actual point-parabolic quotients of full binary G₂ actions

Conjugate a specified nonzero natural vector to the first coordinate,
changing the group map by the same element. Its literal stabilizer then
surjects onto the native point parabolic, with the original action kernel.
Composing with the marked C₄² quotient gives D₁₂; for a stabilizer of order
12288 the kernel has order 1024.

The original Rudvalis point centralizer applies these maps in Chapter13's
OriginalOddNormalizer.RudvalisPointParabolic. The constructed kernel is not
identified here with an ambient involution-centralizer core intersection.
Source: Aschbacher--Smith 4.2.13, printed pp.611--612, using B.4.6.
The imported root model retains the ATLAS attribution in LICENSES/ATLAS.txt.
-/

public section
namespace Atlas.G2.Natural.BinaryPointFlag
open Subgroup
variable {D : Type*} [Group D]

/-- A full natural actor maps its literal point stabilizer onto the marked
point parabolic, retaining its original action kernel. -/
theorem exists_point_parabolic_map
    (a : D →* Model F) (ha : Function.Surjective a)
    (P : Subgroup D) (v : Natural.Space F) (hv : v ≠ 0)
    (hP : ∀ x, x ∈ P ↔ Natural.action F (a x) v = v) :
    ∃ (g : Model F) (b : P →* BinaryCore.secondParabolic),
      Function.Surjective b ∧ b.ker = a.ker.subgroupOf P ∧
      ∀ x : P, (b x : Model F) = g * a x * g⁻¹ := by
  let E := Restricted.NaturalCoordinates.equiv F
  let z : Natural.Space F := E.symm (Pi.single 0 1)
  have hz : z ≠ 0 := by
    intro h
    have hh : (Pi.single 0 1 : Fin 6 → F) = 0 := by
      simpa only [z,E.apply_symm_apply,map_zero] using congrArg E h
    have hh0 := congrFun hh 0
    simp at hh0
  obtain ⟨g,hg⟩ := Natural.derivedAction_transitive F v z hv hz
  let t : Model F := g
  let a' : D →* Model F := (MulAut.conj t).toMonoidHom.comp a
  have ha' : Function.Surjective a' := (MulAut.conj t).surjective.comp ha
  have ht : Natural.action F t v = z := hg
  have hi : Function.Injective (Natural.action F t) := by
    apply Function.HasLeftInverse.injective
    refine ⟨Natural.action F t⁻¹,?_⟩
    intro w
    simp only [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one,
      Module.End.one_apply]
  have hP' (x) : x ∈ P ↔
      Restricted.NaturalCoordinates.action F (a' x) (Pi.single 0 1) = Pi.single 0 1 := by
    have he : E z = Pi.single 0 1 := E.apply_symm_apply _
    rw [←he]
    have hcoord := LinearMap.congr_fun
      ((Restricted.NaturalCoordinates.repEquiv F).isIntertwining' (a' x)) z
    change E (Natural.action F (a' x) z) =
      Restricted.NaturalCoordinates.action F (a' x) (E z) at hcoord
    rw [←hcoord,E.injective.eq_iff,←ht,hP]
    have hc : Natural.action F (a' x) (Natural.action F t v) =
        Natural.action F t (Natural.action F (a x) v) := by
      change Natural.action F (t*a x*t⁻¹) (Natural.action F t v) = _
      simp only [←Module.End.mul_apply,←map_mul]
      congr 2
      group
    rw [hc,hi.eq_iff]
  have hmap : P.map a' = BinaryCore.secondParabolic := by
    rw [marked_point_image a' P hP',MonoidHom.range_eq_top.mpr ha',inf_top_eq]
  let b : P →* BinaryCore.secondParabolic := (a'.comp P.subtype).codRestrict _
    (fun x => hmap ▸ mem_map_of_mem a' x.property)
  have hb : Function.Surjective b := by
    intro y
    have hy : (y : Model F) ∈ P.map a' := hmap.symm ▸ y.property
    obtain ⟨x,hx,he⟩ := hy
    exact ⟨⟨x,hx⟩,Subtype.ext he⟩
  refine ⟨t,b,hb,?_,fun _ => rfl⟩
  ext x
  change b x = 1 ↔ a x = 1
  constructor
  · intro hx
    apply (MulAut.conj t).injective
    exact (congrArg Subtype.val hx).trans (map_one (MulAut.conj t)).symm
  · intro hx
    apply Subtype.ext
    change (MulAut.conj t) (a x) = 1
    rw [hx,map_one]

/-- The original point stabilizer of order 12288 has a dihedral quotient
with kernel 1024, the preimage of the marked C₄² radical. -/
theorem exists_point_dihedral_quotient [Finite D]
    (a : D →* Model F) (ha : Function.Surjective a)
    (P : Subgroup D) (v : Natural.Space F) (hv : v ≠ 0)
    (hP : ∀ x, x ∈ P ↔ Natural.action F (a x) v = v)
    (hcard : Nat.card P = 12288) :
    ∃ (g : Model F) (b : P →* BinaryCore.secondParabolic),
      Function.Surjective b ∧ b.ker = a.ker.subgroupOf P ∧
      (∀ x : P, (b x : Model F) = g * a x * g⁻¹) ∧
      let r := BinaryParabolicPair.FullSquare.quotientEquiv.toMonoidHom.comp
        (BinaryParabolicPair.FullSquare.project.comp b)
      Function.Surjective r ∧ Nat.card r.ker = 1024 ∧
        r.ker = BinaryParabolicPair.FullSquare.radical.comap b := by
  obtain ⟨g,b,hb,hker,hmark⟩ := exists_point_parabolic_map a ha P v hv hP
  let r := BinaryParabolicPair.FullSquare.quotientEquiv.toMonoidHom.comp
    (BinaryParabolicPair.FullSquare.project.comp b)
  have hr : Function.Surjective r :=
    BinaryParabolicPair.FullSquare.quotientEquiv.surjective.comp
      ((QuotientGroup.mk'_surjective _).comp hb)
  refine ⟨g,b,hb,hker,hmark,hr,?_,?_⟩
  · change Nat.card r.ker = 1024
    have hindex : r.ker.index = 12 := by
      change Nat.card (P ⧸ r.ker) = 12
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective r hr).toEquiv]
      rw [Nat.card_eq_fintype_card,DihedralGroup.card]
    have hh := r.ker.card_mul_index
    rw [hindex,hcard] at hh
    omega
  · ext x
    change BinaryParabolicPair.FullSquare.quotientEquiv
      (BinaryParabolicPair.FullSquare.project (b x)) = 1 ↔ _
    rw [←map_one BinaryParabolicPair.FullSquare.quotientEquiv,
      BinaryParabolicPair.FullSquare.quotientEquiv.injective.eq_iff]
    exact QuotientGroup.eq_one_iff (b x)

end Atlas.G2.Natural.BinaryPointFlag
