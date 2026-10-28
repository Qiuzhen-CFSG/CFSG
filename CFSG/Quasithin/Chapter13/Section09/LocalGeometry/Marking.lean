module

public import CFSG.Quasithin.Chapter13.Section09.Elementary
public import Theory.SpecificGroups.SymmetricFourWreath.Planes

/-!
# Wreath coordinates compatible with the original Sylow subgroup

Sylow conjugacy adjusts the supplied local isomorphism so that it sends the
original T to the fixed dihedral wreath Sylow. Its inverse, followed by the
actual inclusion M → G, transports every later coordinate subgroup without
losing the ambient embedding.

Source: Aschbacher–Smith, setup for 13.9.2, printed p.969 (PDF p.986).
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter13.Section09
open Subgroup
open SymmetricFourWreath

variable {G : Type*} [Group G]

/-- A choice of coordinates, with compatibility with the supplied T. -/
structure Marking (d : Configuration G) where
  equiv : d.M ≃* W
  sylow_eq : ((d.T.subtype d.sylow_le : Sylow 2 d.M) : Subgroup d.M).map
    equiv.toMonoidHom = (standardSylow : Subgroup W)

theorem Configuration.exists_marking [Finite G] (d : Configuration G) : Nonempty (Marking d) := by
  let P := (d.T.subtype d.sylow_le).mapSurjective
    (f := d.model.toMonoidHom) d.model.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W P standardSylow
  refine ⟨⟨d.model.trans (MulAut.conj g), ?_⟩⟩
  have h := congrArg (fun S : Sylow 2 W => (S : Subgroup W)) hg
  change (((d.T.subtype d.sylow_le : Sylow 2 d.M) : Subgroup d.M).map
    d.model.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      (standardSylow : Subgroup W) at h
  rw [Subgroup.map_map] at h
  exact h

namespace Marking
variable {d : Configuration G} (m : Marking d)

/-- The actual embedding into G, inverse to the marked coordinates on M. -/
def embedding : W →* G := d.M.subtype.comp m.equiv.symm.toMonoidHom

theorem embedding_injective : Function.Injective m.embedding :=
  d.M.subtype_injective.comp m.equiv.symm.injective

theorem range_embedding : m.embedding.range = d.M := by
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    exact (m.equiv.symm w).property
  · intro hx
    exact ⟨m.equiv ⟨x, hx⟩, congrArg Subtype.val (m.equiv.symm_apply_apply ⟨x, hx⟩)⟩

/-- Transport a coordinate subgroup into the original ambient group. -/
def image (H : Subgroup W) : Subgroup G := H.map m.embedding

theorem image_le_local (H : Subgroup W) : m.image H ≤ d.M := by
  rw [← m.range_embedding]
  exact Subgroup.map_le_range m.embedding H

/-- Exact compatibility with the original Sylow subgroup. -/
theorem image_standardSylow : m.image (standardSylow : Subgroup W) =
    (d.T : Subgroup G) := by
  rw [image, ← m.sylow_eq]
  ext x
  constructor
  · rintro ⟨w, ⟨a, ha, rfl⟩, hax⟩
    have h : m.embedding (m.equiv a) = (a : G) :=
      congrArg Subtype.val (m.equiv.symm_apply_apply a)
    change m.embedding (m.equiv a) = x at hax
    rw [h] at hax
    exact hax ▸ ha
  · intro hx
    let a : d.M := ⟨x, d.sylow_le hx⟩
    exact ⟨m.equiv a, ⟨a, hx, rfl⟩,
      congrArg Subtype.val (m.equiv.symm_apply_apply a)⟩

/-- Coordinate subgroups retain their actual group structure under transport. -/
noncomputable def imageEquiv (H : Subgroup W) : H ≃* m.image H :=
  Subgroup.equivMapOfInjective H m.embedding m.embedding_injective

theorem card_image (H : Subgroup W) : Nat.card (m.image H) = Nat.card H :=
  Subgroup.card_map_of_injective m.embedding_injective

/-- The two actual S₄ factors inside M. -/
def factor (i : C2) : Subgroup G := m.image (SymmetricFourWreath.factor i).range

/-- Each actual factor is isomorphic to S₄ through its marked inclusion. -/
noncomputable def factorEquiv (i : C2) : m.factor i ≃* S4 :=
  ((MonoidHom.ofInjective (SymmetricFourWreath.factor_injective i)).trans
    (m.imageEquiv (SymmetricFourWreath.factor i).range)).symm

theorem factorEquiv_symm_coe (i : C2) (a : S4) :
    ((m.factorEquiv i).symm a : G) = m.embedding (SymmetricFourWreath.factor i a) := rfl

/-- Their intersections with the original T. -/
def factorSylow (i : C2) : Subgroup G := (d.T : Subgroup G) ⊓ m.factor i

def s : G := m.embedding swap
def t : G := m.embedding SymmetricFourWreath.t
def z : G := m.embedding SymmetricFourWreath.z

theorem s_mem_sylow : m.s ∈ (d.T : Subgroup G) := by
  rw [← m.image_standardSylow]
  exact ⟨swap, swap_mem_standardSylow, rfl⟩

theorem t_mem_sylow : m.t ∈ (d.T : Subgroup G) := by
  rw [← m.image_standardSylow]
  exact ⟨SymmetricFourWreath.t, t_mem_standardSylow, rfl⟩

theorem z_mem_sylow : m.z ∈ (d.T : Subgroup G) := by
  rw [← m.image_standardSylow]
  exact ⟨SymmetricFourWreath.z, z_mem_standardSylow, rfl⟩

theorem s_sq : m.s * m.s = 1 := by
  rw [s, ← map_mul, swap_sq, map_one]

theorem s_ne_one : m.s ≠ 1 := by
  intro h
  exact swap_ne_one (m.embedding_injective (h.trans (map_one m.embedding).symm))

theorem t_sq : m.t * m.t = 1 := by
  rw [t, ← map_mul, SymmetricFourWreath.t_sq, map_one]

theorem t_ne_one : m.t ≠ 1 := by
  intro h
  exact SymmetricFourWreath.t_ne_one
    (m.embedding_injective (h.trans (map_one m.embedding).symm))

theorem z_eq : m.z = m.t * (m.s * m.t * m.s⁻¹) := by
  simp only [z, t, s, SymmetricFourWreath.z, map_mul, map_inv]

/-- The marked swap interchanges the two embedded S₄ factors elementwise. -/
theorem s_conjugates_factor (i : C2) (a : S4) :
    m.s * m.embedding (SymmetricFourWreath.factor i a) * m.s⁻¹ =
      m.embedding (SymmetricFourWreath.factor (turn * i) a) := by
  rw [s, ← map_inv, ← map_mul, ← map_mul, SymmetricFourWreath.swap_factor]

/-- The four embedded elementary groups; their exhaustive maximality is proved separately. -/
def elementaryGroup (b c : Bool) : Subgroup G := m.image (SymmetricFourWreath.elementary b c)

instance elementaryGroup_elementary (b c : Bool) :
    IsElementaryAbelian 2 (m.elementaryGroup b c) := IsElementaryAbelian.map m.embedding

theorem card_elementaryGroup (b c : Bool) : Nat.card (m.elementaryGroup b c) = 16 :=
  (m.card_image (SymmetricFourWreath.elementary b c)).trans
    (SymmetricFourWreath.card_elementary b c)

theorem elementaryGroup_le_sylow (b c : Bool) :
    m.elementaryGroup b c ≤ (d.T : Subgroup G) := by
  rw [← m.image_standardSylow]
  exact Subgroup.map_mono (elementary_le_standardSylow b c)

/-- The second coordinate elementary group in the original T. -/
abbrev B : Subgroup G := m.elementaryGroup false false

/-- The dihedral base in the original T, to be identified with J(T). -/
def dihedralBase : Subgroup G := m.image SymmetricFourWreath.J

end Marking
end CFSG.Quasithin.Chapter13.Section09
