module
public import Theory.SpecificGroups.SymplecticSix.FanoCore
public import CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable.Symplectic.InvolutionRepresentatives
/-!
# The four orbits on the original plane two-core

The marked three-space embeds the binary Fano core by sums of rank-one
transvection displacements. Every image fixes the original seven plane
points. The pointwise-fixer equality puts it in the literal plane two-core;
injectivity and the known order 64 make the map an isomorphism.

Restriction of the original plane action has kernel exactly that two-core.
Its quotient has order 168, so its image is all of SL₃(2). The explicit
equivariant map therefore transports H.5.3's four orbits, their cardinalities
7, 7, 21, 28, their disjointness and their union to the original subgroup.
The point-complement orbit consists of the marked transvections. These
are plane-vertex orbits; their separation into four classes in the whole
recognized group is a further statement, not an assumption here.

Source: Aschbacher–Smith H.5.3(3–4) and 13.4.9, printed pp.385–386,906.
-/

@[expose] public noncomputable section
namespace Quasithin.I5.C3Recognition.SymplecticMark
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
open CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open BinaryLinearThree.FanoTransvection
variable {G : Type*} [Group G] {S : DSystem .C3 G}
variable (m : SymplecticMark S)

noncomputable def fanoFullEquiv : G ≃* Sp (ZMod 2) := by
  let : Finite G := Nat.finite_of_card_ne_zero (by rw [C3Recognition.card_eq S]; decide)
  exact MulEquiv.ofBijective m.hom (m.hom_injective.bijective_of_nat_card_le (by
    rw [C3Recognition.card_eq S,card_sp_of_card_two (by simp)]))

variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace S.basePlane)

noncomputable def fanoEmbedding : BinaryLinearThree.Vector →ₗ[ZMod 2] Vector (ZMod 2) :=
  (m.planeSpace S.basePlane).subtype.comp b.toLinearMap

theorem fanoEmbedding_injective : Function.Injective (m.fanoEmbedding b) :=
  Subtype.val_injective.comp b.injective

theorem fanoEmbedding_isotropic (v w : BinaryLinearThree.Vector) :
    form (ZMod 2) (m.fanoEmbedding b v) (m.fanoEmbedding b w) = 0 :=
  m.planeSpace_isotropic _ _ (b v).property _ (b w).property

noncomputable def fanoLift : Multiplicative BinaryLinearThree.Core →* G :=
  m.fanoFullEquiv.symm.toMonoidHom.comp
    (shear (m.fanoEmbedding b) (m.fanoEmbedding_isotropic b))

theorem fanoLift_injective : Function.Injective (m.fanoLift b) :=
  m.fanoFullEquiv.symm.injective.comp
    (shear_injective (m.fanoEmbedding b) (m.fanoEmbedding_isotropic b)
      (m.fanoEmbedding_injective b))

theorem fanoLift_mem_core (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T)
    (a : Multiplicative BinaryLinearThree.Core) : m.fanoLift b a ∈ S.Q 2 := by
  rw [← m.plane_fixer_eq_core P hP,mem_fixingSubgroup_iff]
  intro x hx
  apply m.point_injective
  rw [← m.equivariant]
  change m.fanoFullEquiv (m.fanoFullEquiv.symm
    (shear (m.fanoEmbedding b) (m.fanoEmbedding_isotropic b) a)) • m.point x = m.point x
  rw [MulEquiv.apply_symm_apply]
  obtain ⟨v,hv⟩ := b.surjective ⟨m.point x,m.point_mem_planeSpace hx⟩
  have hve : m.fanoEmbedding b v = m.point x := congrArg Subtype.val hv
  rw [← hve]
  change shearElement (m.fanoEmbedding b) (m.fanoEmbedding_isotropic b) a.toAdd • _ = _
  rw [shearElement_apply,displacement_on_range _ _ (m.fanoEmbedding_isotropic b),add_zero]

noncomputable def planeFanoHom (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T) :
    Multiplicative BinaryLinearThree.Core →* S.Q 2 :=
  (m.fanoLift b).codRestrict (S.Q 2) (m.fanoLift_mem_core b P hP)

theorem planeFanoHom_injective (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T) :
    Function.Injective (m.planeFanoHom b P hP) := by
  intro a c hac
  exact m.fanoLift_injective b (congrArg Subtype.val hac)

noncomputable def planeFanoEquiv (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T) :
    Multiplicative BinaryLinearThree.Core ≃* S.Q 2 := by
  let : Finite G := Nat.finite_of_card_ne_zero (by rw [C3Recognition.card_eq S]; decide)
  apply MulEquiv.ofBijective (m.planeFanoHom b P hP)
  apply (m.planeFanoHom_injective b P hP).bijective_of_nat_card_le
  have hsource : Nat.card (Multiplicative BinaryLinearThree.Core) = 64 := by
    let : Nonempty BinaryLinearThree.Point := ⟨Matrix.PSL3Two.flagPoint⟩
    change Nat.card BinaryLinearThree.Core = 64
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,
      BinaryPermutation.finrank_core,Matrix.PSL3Two.Fano.card_point]
    rfl
  have htarget : Nat.card (S.Q 2) = 64 := by
    change Nat.card ((pCore 2 (S.family 2)).map (S.family 2).subtype) = 64
    rw [card_map_of_injective (S.family 2).subtype_injective,plane_core_card S]
  omega

theorem fanoLift_marking (a : Multiplicative BinaryLinearThree.Core) :
    m.hom (m.fanoLift b a) =
      shear (m.fanoEmbedding b) (m.fanoEmbedding_isotropic b) a :=
  m.fanoFullEquiv.apply_symm_apply _

theorem fanoLift_pointSpike (p : BinaryLinearThree.Point) :
    m.hom (m.fanoLift b (Multiplicative.ofAdd (BinaryLinearThree.FanoDecomposition.pointSpike p))) =
      Matrix.PSp4Three.transvection (m.fanoEmbedding b p.val) 1 := by
  rw [fanoLift_marking,shear_pointSpike]

end Quasithin.I5.C3Recognition.SymplecticMark
namespace Quasithin.I5.C3Recognition.SymplecticMark
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
open BinaryLinearThree.FanoTransvection
variable {G : Type*} [Group G] {S : DSystem .C3 G}
variable (m : SymplecticMark S)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace S.basePlane)

noncomputable def fanoSpaceActor (g : S.family 2) :
    m.planeSpace S.basePlane ≃ₗ[ZMod 2] m.planeSpace S.basePlane :=
  (toLinear (m.hom g.val)).ofSubmodules _ _ (by
    apply le_antisymm
    · rintro _ ⟨v,hv,rfl⟩
      exact m.plane_vertex_preserves_space g v hv
    · intro v hv
      refine ⟨toLinear (m.hom g.val⁻¹) v,
        m.plane_vertex_preserves_space g⁻¹ v hv,?_⟩
      simp only [map_inv,LinearEquiv.coe_coe,LinearEquiv.coe_inv,LinearEquiv.apply_symm_apply])

noncomputable def fanoCoordinateActor : S.family 2 →*
    (BinaryLinearThree.Vector ≃ₗ[ZMod 2] BinaryLinearThree.Vector) where
  toFun g := b.trans ((m.fanoSpaceActor g).trans b.symm)
  map_one' := by
    ext v : 1
    apply b.injective
    apply Subtype.ext
    simp [fanoSpaceActor]
  map_mul' g h := by
    ext v : 1
    apply b.injective
    apply Subtype.ext
    simp [fanoSpaceActor]

noncomputable def fanoModelEquiv : BinaryLinearThree.Group ≃*
    (BinaryLinearThree.Vector ≃ₗ[ZMod 2] BinaryLinearThree.Vector) :=
  (Matrix.PSL3Two.equivGL.trans Matrix.GeneralLinearGroup.toLin).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) BinaryLinearThree.Vector)

theorem fanoModelEquiv_apply (g : BinaryLinearThree.Group) (v : BinaryLinearThree.Vector) :
    fanoModelEquiv g v = g • v := by
  simp only [fanoModelEquiv,MulEquiv.trans_apply,Matrix.PSL3Two.equivGL_apply]
  rfl

noncomputable def fanoActor : S.family 2 →* BinaryLinearThree.Group :=
  fanoModelEquiv.symm.toMonoidHom.comp (m.fanoCoordinateActor b)

theorem fanoActor_action (g : S.family 2) (v : BinaryLinearThree.Vector) :
    m.hom g.val • m.fanoEmbedding b v = m.fanoEmbedding b (m.fanoActor b g • v) := by
  have he : fanoModelEquiv (m.fanoActor b g) = m.fanoCoordinateActor b g :=
    fanoModelEquiv.apply_symm_apply _
  rw [← fanoModelEquiv_apply,he]
  change _ = (b (b.symm (m.fanoSpaceActor g (b v)))).val
  rw [LinearEquiv.apply_symm_apply]
  rfl

end Quasithin.I5.C3Recognition.SymplecticMark
namespace Quasithin.I5.C3Recognition.SymplecticMark
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
open CFSG.Quasithin.Chapter13.Section04.FixedCoreSource.Solvable
open BinaryLinearThree.FanoTransvection
variable {G : Type*} [Group G] {S : DSystem .C3 G}
variable (m : SymplecticMark S)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace S.basePlane)
variable (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T)

include P hP in
theorem fanoActor_ker : (m.fanoActor b).ker = pCore 2 (S.family 2) := by
  ext g
  change m.fanoActor b g = 1 ↔ g ∈ pCore 2 (S.family 2)
  constructor
  · intro hg
    have hq : g.val ∈ S.Q 2 := by
      rw [← m.plane_fixer_eq_core P hP,mem_fixingSubgroup_iff]
      intro x hx
      apply m.point_injective
      rw [←m.equivariant]
      obtain ⟨v,hv⟩ := b.surjective ⟨m.point x,m.point_mem_planeSpace hx⟩
      have he : m.fanoEmbedding b v = m.point x := congrArg Subtype.val hv
      change m.hom g.val • m.point x = m.point x
      rw [←he,m.fanoActor_action,hg,one_smul]
    obtain ⟨a,ha,he⟩ := hq
    exact (show a = g from Subtype.ext he) ▸ ha
  · intro hg
    apply fanoModelEquiv.injective
    apply LinearEquiv.ext
    intro v
    rw [map_one]
    change fanoModelEquiv (m.fanoActor b g) v = v
    rw [fanoModelEquiv_apply]
    apply m.fanoEmbedding_injective b
    rw [←m.fanoActor_action]
    exact marked_plane_core_fixes m hg _ (b v).property

include P hP in
theorem fanoActor_surjective : Function.Surjective (m.fanoActor b) := by
  have hcard : Nat.card (m.fanoActor b).range = Nat.card BinaryLinearThree.Group := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange (m.fanoActor b)).toEquiv,
      m.fanoActor_ker b P hP]
    obtain ⟨e⟩ := S.plane_quotient
    exact Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv
  apply MonoidHom.range_eq_top.mp
  exact Subgroup.eq_top_of_card_eq _ hcard

theorem fanoLift_conjugate (g : S.family 2) (a : BinaryLinearThree.Core) :
    m.fanoLift b (Multiplicative.ofAdd (BinaryLinearThree.U₂ (m.fanoActor b g) a)) =
      MulAut.conj g.val (m.fanoLift b (Multiplicative.ofAdd a)) := by
  apply m.hom_injective
  rw [m.fanoLift_marking]
  change _ = m.hom (g.val * m.fanoLift b (Multiplicative.ofAdd a) * g.val⁻¹)
  simp only [map_mul,map_inv,m.fanoLift_marking]
  exact shear_equivariant _ _ (m.hom g.val) (m.fanoActor b g) (m.fanoActor_action b g) a

include P hP in
/-- Conjugation in the original plane vertex is precisely the Fano-core action. -/
theorem fanoLift_orbit_iff (a c : BinaryLinearThree.Core) :
    (∃ g : S.family 2, MulAut.conj g.val (m.fanoLift b (Multiplicative.ofAdd a)) =
      m.fanoLift b (Multiplicative.ofAdd c)) ↔ c ∈ BinaryLinearThree.FanoLocalStructure.orbit a := by
  constructor
  · rintro ⟨g,hg⟩
    refine ⟨m.fanoActor b g,?_⟩
    have he := m.fanoLift_injective b ((m.fanoLift_conjugate b g a).trans hg)
    exact congrArg Multiplicative.toAdd he
  · rintro ⟨k,hk⟩
    obtain ⟨g,rfl⟩ := m.fanoActor_surjective b P hP k
    refine ⟨g,?_⟩
    rw [←m.fanoLift_conjugate,hk]

end Quasithin.I5.C3Recognition.SymplecticMark
namespace Quasithin.I5.C3Recognition.SymplecticMark
open Subgroup Matrix Theory.SpecificGroups.SymplecticSix
open BinaryLinearThree.FanoLocalStructure
variable {G : Type*} [Group G] {S : DSystem .C3 G}
variable (m : SymplecticMark S)
variable (b : BinaryLinearThree.Vector ≃ₗ[ZMod 2] m.planeSpace S.basePlane)
variable (P : Sylow 2 G) (hP : (P : Subgroup G) = S.T)

def planeFanoFamily (A : Set BinaryLinearThree.Core) : Set G :=
  (fun a => m.fanoLift b (Multiplicative.ofAdd a)) '' A

def planeConjugacyOrbit (a : G) : Set G :=
  {c | ∃ g : S.family 2, MulAut.conj g.val a = c}

include P hP in
theorem planeConjugacyOrbit_eq (a : BinaryLinearThree.Core) :
    planeConjugacyOrbit (S := S) (m.fanoLift b (Multiplicative.ofAdd a)) =
      m.planeFanoFamily b (orbit a) := by
  ext c
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨BinaryLinearThree.U₂ (m.fanoActor b g) a,⟨m.fanoActor b g,rfl⟩,
      m.fanoLift_conjugate b g a⟩
  · rintro ⟨d,hd,rfl⟩
    exact (m.fanoLift_orbit_iff b P hP a d).mpr hd

theorem planeFanoFamily_card (A : Set BinaryLinearThree.Core) :
    Nat.card (m.planeFanoFamily b A) = Nat.card A := by
  exact (Nat.card_congr (Equiv.Set.image
    (fun a => m.fanoLift b (Multiplicative.ofAdd a)) A
    (fun _ _ h => congrArg Multiplicative.toAdd (m.fanoLift_injective b h)))).symm

/-- All four original plane-vertex orbit sizes on the literal two-core. -/
theorem planeFanoFamily_cards :
    Nat.card (m.planeFanoFamily b pointComplements) = 7 ∧
    Nat.card (m.planeFanoFamily b lineComplements) = 7 ∧
    Nat.card (m.planeFanoFamily b weightTwo) = 21 ∧
    Nat.card (m.planeFanoFamily b basisComplements) = 28 := by
  simp only [planeFanoFamily_card]
  exact four_families_card

include P hP in
/-- The four families are actual conjugacy orbits under the retained plane vertex. -/
theorem planeFanoFamily_orbits :
    (∀ a ∈ m.planeFanoFamily b pointComplements,
      planeConjugacyOrbit (S := S) a = m.planeFanoFamily b pointComplements) ∧
    (∀ a ∈ m.planeFanoFamily b lineComplements,
      planeConjugacyOrbit (S := S) a = m.planeFanoFamily b lineComplements) ∧
    (∀ a ∈ m.planeFanoFamily b weightTwo,
      planeConjugacyOrbit (S := S) a = m.planeFanoFamily b weightTwo) ∧
    (∀ a ∈ m.planeFanoFamily b basisComplements,
      planeConjugacyOrbit (S := S) a = m.planeFanoFamily b basisComplements) := by
  have hfamily (A : Set BinaryLinearThree.Core) (r : BinaryLinearThree.Core)
      (hA : A = orbit r) : ∀ a ∈ m.planeFanoFamily b A,
        planeConjugacyOrbit (S := S) a = m.planeFanoFamily b A := by
    rintro _ ⟨a,ha,rfl⟩
    have ho : orbit a = A := (orbit_eq_of_mem (a := r) (b := a) (hA ▸ ha)).trans hA.symm
    rw [m.planeConjugacyOrbit_eq b P hP,ho]
  exact ⟨hfamily _ _ pointComplements_eq_orbit,hfamily _ _ lineComplements_eq_orbit,
    hfamily _ _ weightTwo_eq_orbit,hfamily _ _ basisComplements_eq_orbit⟩

include P hP in
/-- Their union is exactly the nonidentity part of the original plane core. -/
theorem planeFanoFamily_union :
    m.planeFanoFamily b pointComplements ∪ m.planeFanoFamily b lineComplements ∪
      m.planeFanoFamily b weightTwo ∪ m.planeFanoFamily b basisComplements =
        {a : G | a ∈ S.Q 2 ∧ a ≠ 1} := by
  simp only [planeFanoFamily,←Set.image_union,four_families_union]
  ext a
  constructor
  · rintro ⟨c,hc,rfl⟩
    refine ⟨m.fanoLift_mem_core b P hP _,?_⟩
    intro he
    have hh := m.fanoLift_injective b (he.trans (map_one _).symm)
    exact hc (congrArg Multiplicative.toAdd hh)
  · rintro ⟨ha,ha1⟩
    obtain ⟨c,hc⟩ := (m.planeFanoEquiv b P hP).surjective ⟨a,ha⟩
    have he : m.fanoLift b c = a := congrArg Subtype.val hc
    refine ⟨c.toAdd,?_,he⟩
    intro hz
    have hc1 : c = 1 := congrArg Multiplicative.ofAdd hz
    exact ha1 (he.symm.trans (hc1 ▸ map_one _))

/-- The six disjointness clauses retain the actual marked families. -/
theorem planeFanoFamily_disjoint :
    Disjoint (m.planeFanoFamily b pointComplements) (m.planeFanoFamily b lineComplements) ∧
    Disjoint (m.planeFanoFamily b pointComplements) (m.planeFanoFamily b weightTwo) ∧
    Disjoint (m.planeFanoFamily b pointComplements) (m.planeFanoFamily b basisComplements) ∧
    Disjoint (m.planeFanoFamily b lineComplements) (m.planeFanoFamily b weightTwo) ∧
    Disjoint (m.planeFanoFamily b lineComplements) (m.planeFanoFamily b basisComplements) ∧
    Disjoint (m.planeFanoFamily b weightTwo) (m.planeFanoFamily b basisComplements) := by
  have hdis {A B : Set BinaryLinearThree.Core} (h : Disjoint A B) :
      Disjoint (m.planeFanoFamily b A) (m.planeFanoFamily b B) := by
    rw [Set.disjoint_left] at h ⊢
    rintro a ⟨x,hx,rfl⟩ ⟨y,hy,he⟩
    have he' := congrArg Multiplicative.toAdd (m.fanoLift_injective b he)
    change y = x at he'
    exact h hx (he' ▸ hy)
  obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := four_families_disjoint
  exact ⟨hdis h₁,hdis h₂,hdis h₃,hdis h₄,hdis h₅,hdis h₆⟩

end Quasithin.I5.C3Recognition.SymplecticMark
