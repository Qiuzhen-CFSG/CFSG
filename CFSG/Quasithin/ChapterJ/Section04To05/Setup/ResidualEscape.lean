module

public import CFSG.Quasithin.ChapterJ.Section04To05.Setup.Parabolic
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# The source choice outside H in the second Ru residual

A cubic in the natural plane stabilizer moves the marked central involution.
Surjective residual transport lifts it to the actual two-residual of N_L(V₂).
Its lift cannot centralize the original Z(T), so it lies outside H. This
constructs the element chosen at the start of J.4 from the original Ru data.

Source: Aschbacher–Smith, J.4, opening notation, printed p.440.
-/

public section
noncomputable section
open Subgroup Representation
namespace CFSG.Quasithin.ChapterJ.RuSubgroup
open BinaryLinearThree
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G} (p : Plane d)

/-- The actual second two-residual, inside the original ambient group. -/
def Plane.L₂ : Subgroup G := (pResidual 2 p.parabolic).map p.parabolic.subtype

/-- The literal quotient map onto the natural plane stabilizer. -/
def Plane.quotient : p.parabolic →* NaturalPlaneStabilizer.stabilizer p.naturalSpace :=
  (d.ru1.quotientMap.comp (inclusion (fun _ h => (p.mem_parabolic _).mp h |>.1))).codRestrict
    (NaturalPlaneStabilizer.stabilizer p.naturalSpace)
    (fun l => (p.mem_parabolic_iff ⟨l,(p.mem_parabolic _).mp l.property |>.1⟩).mp l.property)

/-- The stabilizer quotient retains the original Ru1 map on every element. -/
theorem Plane.quotient_apply (l : p.parabolic) :
    (p.quotient l : Group) =
      d.ru1.quotientMap ⟨l,((p.mem_parabolic _).mp l.property).1⟩ := by rfl

/-- The second parabolic maps onto its full natural stabilizer. -/
theorem Plane.quotient_surjective : Function.Surjective p.quotient := by
  rintro ⟨a,ha⟩
  obtain ⟨l,rfl⟩ := d.ru1.quotient_surjective a
  exact ⟨⟨l,(p.mem_parabolic_iff l).mpr ha⟩,Subtype.ext rfl⟩

/-- The two-residual remains in the actual plane normalizer. -/
theorem Plane.L₂_le_parabolic : p.L₂ ≤ p.parabolic := map_subtype_le _

/-- The original second residual is normal in its parabolic. -/
theorem Plane.L₂_normalized : p.parabolic ≤ normalizer (p.L₂ : Set G) :=
  le_normalizer_embedded_pResidual 2 p.parabolic

/-- The source residual lies in L. -/
theorem Plane.L₂_le_L : p.L₂ ≤ d.L := by
  rintro x ⟨l,hl,rfl⟩
  exact ((p.mem_parabolic _).mp l.property).1

/-- The original Sylow supplements the second two-residual. -/
theorem Plane.residual_sup_sylow : p.L₂ ⊔ (d.T : Subgroup G) = p.parabolic := by
  have hh := congrArg (fun A : Subgroup p.parabolic => A.map p.parabolic.subtype)
    (pResidual_sup_sylow_eq_top (d.T.subtype p.sylow_le_parabolic))
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype] at hh
  change p.L₂ ⊔ ((d.T : Subgroup G).subgroupOf p.parabolic).map p.parabolic.subtype = _ at hh
  rwa [map_subgroupOf_eq_of_le p.sylow_le_parabolic] at hh

/-- The original marked point is moved by an actual element of the second residual. -/
theorem Plane.exists_residual_moves (z : d.toTypeRuSetup.Z) (hz : z ≠ 1) :
    ∃ g : G, g ∈ p.L₂ ∧ g * (z : G) * g⁻¹ ≠ (z : G) := by
  let v : d.V := ⟨z,p.le_seed (p.point_le z.property)⟩
  have hv : (d.ru1.natural.coordinates v).toAdd ∈ p.naturalSpace :=
    (p.mem_naturalSpace v).mpr (p.point_le z.property)
  have hv0 : (d.ru1.natural.coordinates v).toAdd ≠ 0 := by
    intro h
    have hm : d.ru1.natural.coordinates v = 1 := h
    have hh := (d.ru1.natural.coordinates_eq_one_iff v).mp hm
    exact hz (Subtype.ext (show (z : G) = 1 from hh))
  obtain ⟨a,ha3,ham⟩ := NaturalPlaneStabilizer.exists_cubic_moving p.naturalSpace
    p.finrank_naturalSpace _ hv hv0
  have har : a ∈ pResidual 2 (NaturalPlaneStabilizer.stabilizer p.naturalSpace) :=
    mem_pResidual_of_orderOf_coprime
      (Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one ha3) (by decide))
  rw [← map_pResidual_of_surjective 2 p.quotient p.quotient_surjective] at har
  obtain ⟨g,hgr,hga⟩ := har
  refine ⟨g,⟨g,hgr,rfl⟩,?_⟩
  intro hfix
  have he := d.ru1.natural.equivariant
    (⟨g,((p.mem_parabolic _).mp g.property).1⟩ : d.L) v
  have hgcoords : d.ru1.quotientMap ⟨g,((p.mem_parabolic _).mp g.property).1⟩ = a :=
    congrArg Subtype.val hga
  change (d.ru1.natural.coordinates _).toAdd =
    W (d.ru1.quotientMap ⟨g,((p.mem_parabolic _).mp g.property).1⟩)
      (d.ru1.natural.coordinates v).toAdd at he
  rw [hgcoords] at he
  apply ham
  exact he.symm.trans (congrArg (fun x : d.V => (d.ru1.natural.coordinates x).toAdd)
    (Subtype.ext hfix))

/-- The element g ∈ L₂ − H required in the original J.4 setup exists. -/
theorem Plane.exists_residual_outside_H : ∃ g : G, g ∈ p.L₂ ∧ g ∉ d.toTypeRuSetup.H := by
  let : Nontrivial d.toTypeRuSetup.Z := Finite.one_lt_card_iff_nontrivial.mp
    (by rw [d.card_Z]; decide)
  obtain ⟨z,hz⟩ := exists_ne (1 : d.toTypeRuSetup.Z)
  obtain ⟨g,hg,hmove⟩ := p.exists_residual_moves z hz
  refine ⟨g,hg,fun hH => hmove ?_⟩
  have hc : (z : G) * g = g * (z : G) := hH (z : G) z.property
  rw [← hc,mul_inv_cancel_right]

/-- The actual source J.4 choice, with all plane and escape premises discharged. -/
theorem source_second_parabolic (h : IsTypeRu G) :
    ∃ (d : LocalSetup G) (p : Plane d) (g : G), g ∈ p.L₂ ∧ g ∉ d.toTypeRuSetup.H := by
  obtain ⟨d,hp⟩ := source_plane h
  obtain ⟨p⟩ := hp
  obtain ⟨g,hg,hn⟩ := p.exists_residual_outside_H
  exact ⟨d,p,g,hg,hn⟩

end CFSG.Quasithin.ChapterJ.RuSubgroup
