module

public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Model.Points
public import CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour.Chapter15
public import Theory.Representation.OrthogonalFourPlusMatrix.PrimeFieldTwo.ModuleGeometry
/-!
# Natural-module and marked-hyperplane geometry for G.2.6

The supplied coordinates transport the irreducible determinant module to the
literal LU-action on V_L. Starred generation then gives I-irreducibility and
centrality of V_L in O₂(I), using the proved normal-layer argument.

The polar form alone gives |V|=8, V_L=V∨Vᵍ, disjointness of the marked point
from Vᵍ, and an explicit multiplicative equivalence from V∩Vᵍ to the binary
two-space. The stabilizer's actual displacements give [V_L,U]=V. The derived
bound [U,U]≤V₁ then proves V_L∩U=V, and conjugation supplies the opposite
intersection. Singularity and the stabilizer equality are preceding geometry
premises only for these displacement/intersection conclusions.

The Chapter 15 application uses its literal Z, Z-perpendicular, Y and closure U.
Identifying U∩Uᵍ with the E₄ hyperplane intersection still retains the separate
coprime-action containment U∩Uᵍ≤V; it is not assumed in the geometric results.

Source: Aschbacher–Smith, G.2.6, printed p.336/PDF p.347, and 15.3.53–54,
printed p.1146/PDF p.1163. This is the conditional geometry helper, not the
assembly or the quotient-module decomposition of the full source theorem.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
open Setup ClassicalOrthogonal.FourPlusMatrix
namespace Hypothesis
namespace Geometry
abbrev M := PrimeFieldTwo.ModuleGeometry.V
abbrev Actors := PrimeFieldTwo.ModuleGeometry.Actors
end Geometry
open Geometry
variable {G : Type*} [Group G] [Finite G] {D : Setup G} {g : G} (d : Hypothesis D g)
include d

def vectorMap : Multiplicative M →* G := D.VL.subtype.comp d.coordinates.symm.toMonoidHom

theorem vectorMap_injective : Function.Injective d.vectorMap :=
  D.VL.subtype_injective.comp d.coordinates.symm.injective

@[simp] theorem vectorMap_coordinates (x : D.VL) : d.vectorMap (d.coordinates x) = x := by
  simp [vectorMap]

theorem vectorMap_range : d.vectorMap.range = D.VL := by
  rw [vectorMap, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr d.coordinates.symm.surjective,
    ← MonoidHom.range_eq_map, range_subtype]

theorem vectorMap_action (a : (D.L ⊔ D.U : Subgroup G)) (x : M) :
    d.vectorMap (Multiplicative.ofAdd (matrixAction (d.matrixProjection a) x)) =
      (a : G) * d.vectorMap (Multiplicative.ofAdd x) * (a : G)⁻¹ := by
  simpa [vectorMap, matrixProjection] using
    d.equivariant a (d.coordinates.symm (Multiplicative.ofAdd x))

/-- The actual inverse image under the supplied coordinates, regarded as an F₂-subspace. -/
def matrixSubspace (A : Subgroup G) : Submodule (ZMod 2) M :=
  AddSubgroup.toZModSubmodule 2 ((A.comap d.vectorMap).toAddSubgroup')

@[simp] theorem mem_matrixSubspace (A : Subgroup G) (x : M) :
    x ∈ d.matrixSubspace A ↔ d.vectorMap (Multiplicative.ofAdd x) ∈ A := Iff.rfl

theorem matrixSubspace_mono {A B : Subgroup G} (h : A ≤ B) :
    d.matrixSubspace A ≤ d.matrixSubspace B := fun _ hx => h hx

theorem matrixSubspace_le_iff {A B : Subgroup G} (hA : A ≤ D.VL) :
    d.matrixSubspace A ≤ d.matrixSubspace B ↔ A ≤ B := by
  refine ⟨?_, d.matrixSubspace_mono⟩
  intro h a ha
  let x : D.VL := ⟨a,hA ha⟩
  have hm : (d.coordinates x).toAdd ∈ d.matrixSubspace A := by
    change d.vectorMap (d.coordinates x) ∈ A
    simpa only [d.vectorMap_coordinates] using ha
  have hh := h hm
  change d.vectorMap (d.coordinates x) ∈ B at hh
  simpa only [d.vectorMap_coordinates] using hh

theorem matrixSubspace_eq_iff {A B : Subgroup G} (hA : A ≤ D.VL) (hB : B ≤ D.VL) :
    d.matrixSubspace A = d.matrixSubspace B ↔ A = B := by
  constructor
  · intro h
    exact le_antisymm ((d.matrixSubspace_le_iff hA).mp h.le)
      ((d.matrixSubspace_le_iff hB).mp h.ge)
  · rintro rfl; rfl

@[simp] theorem matrixSubspace_VL : d.matrixSubspace D.VL = ⊤ := by
  apply top_unique
  intro x _
  exact (d.coordinates.symm (Multiplicative.ofAdd x)).property

@[simp] theorem matrixSubspace_bot : d.matrixSubspace ⊥ = ⊥ := by
  ext x
  change d.vectorMap (Multiplicative.ofAdd x) = 1 ↔ x = 0
  rw [← d.vectorMap.map_one, d.vectorMap_injective.eq_iff]
  rfl

@[simp] theorem matrixSubspace_inf (A B : Subgroup G) :
    d.matrixSubspace (A ⊓ B) = d.matrixSubspace A ⊓ d.matrixSubspace B := rfl

def matrixSubspaceMap (A : Subgroup G) : Multiplicative (d.matrixSubspace A) →* A where
  toFun x := ⟨d.vectorMap (Multiplicative.ofAdd x.toAdd.val), x.toAdd.property⟩
  map_one' := Subtype.ext d.vectorMap.map_one
  map_mul' _ _ := Subtype.ext (d.vectorMap.map_mul _ _)

noncomputable def matrixSubspaceEquiv (A : Subgroup G) (hA : A ≤ D.VL) :
    A ≃* Multiplicative (d.matrixSubspace A) :=
  (MulEquiv.ofBijective (d.matrixSubspaceMap A) (by
    constructor
    · intro x y he
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      have hh : d.vectorMap (Multiplicative.ofAdd x.toAdd.val) =
          d.vectorMap (Multiplicative.ofAdd y.toAdd.val) := congrArg (fun a : A => (a : G)) he
      exact congrArg Multiplicative.toAdd (d.vectorMap_injective hh)
    · intro a
      let x : D.VL := ⟨a,hA a.property⟩
      have hm : (d.coordinates x).toAdd ∈ d.matrixSubspace A := by
        change d.vectorMap (d.coordinates x) ∈ A
        simpa only [d.vectorMap_coordinates] using a.property
      refine ⟨Multiplicative.ofAdd ⟨(d.coordinates x).toAdd,hm⟩, ?_⟩
      apply Subtype.ext
      exact d.vectorMap_coordinates x)).symm

/-- Irreducibility for the ambient LU-action, with literal subgroup normalizers. -/
theorem LU_irreducible (A : Subgroup G) (hA : A ≤ D.VL)
    (hN : D.L ⊔ D.U ≤ normalizer (A : Set G)) : A = ⊥ ∨ A = D.VL := by
  have hi : ∀ a : Geometry.Actors, ∀ x ∈ d.matrixSubspace A,
      matrixAction a x ∈ d.matrixSubspace A := by
    intro a x hx
    obtain ⟨u,rfl⟩ := d.matrixProjection_surjective a
    rw [d.mem_matrixSubspace, d.vectorMap_action]
    exact (le_normalizer_iff.mp hN) u u.property _ hx
  rcases PrimeFieldTwo.ModuleGeometry.irreducible (d.matrixSubspace A) hi with h | h
  · exact Or.inl ((d.matrixSubspace_eq_iff hA bot_le).mp (by simpa using h))
  · exact Or.inr ((d.matrixSubspace_eq_iff hA le_rfl).mp (by simpa using h))

theorem I_irreducible (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U))
    (A : Subgroup G) (hA : A ≤ D.VL) (hN : D.I g ≤ normalizer (A : Set G)) :
    A = ⊥ ∨ A = D.VL :=
  d.LU_irreducible A hA ((d.I_eq_LU_of_star hstar) ▸ hN)

theorem central_first_layer_of_star (hstar : D.star (D.I g) = D.star (D.L ⊔ D.U)) :
    D.VL ≤ D.S g ⊓ centralizer (D.S g : Set G) := by
  let := d.VL_elementary
  exact central_first_layer (IsElementaryAbelian.isPGroup 2 D.VL)
    ((d.I_eq_LU_of_star hstar).symm ▸ d.VL_le_LU) d.I_normalizes_VL
    (d.I_irreducible hstar)

/-- The nonidentity point is unique, so perpendicularity can be tested against one vector. -/
theorem pointVector_zero_or_eq (z : D.V₁) (hz : d.pointVector z ≠ 0) (w : D.V₁) :
    d.pointVector w = 0 ∨ d.pointVector w = d.pointVector z := by
  by_cases hw : w = 1
  · exact Or.inl ((d.pointVector_eq_zero_iff w).mpr hw)
  · right
    obtain ⟨u,_,hu⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp d.point_card
    have hz' : z ≠ 1 := fun he => hz ((d.pointVector_eq_zero_iff z).mpr he)
    exact congrArg d.pointVector ((hu w hw).trans (hu z hz').symm)

theorem matrixSubspace_V (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    d.matrixSubspace D.V = PrimeFieldTwo.ModuleGeometry.perp (d.pointVector z) := by
  ext x
  rw [d.mem_matrixSubspace, PrimeFieldTwo.ModuleGeometry.mem_perp]
  change (d.coordinates.symm (Multiplicative.ofAdd x) : G) ∈ D.V ↔ _
  rw [d.perpendicular]
  simp only [MulEquiv.apply_symm_apply]
  change (∀ w : D.V₁, PrimeFieldTwo.ModuleGeometry.pairing x (d.pointVector w) = 0) ↔ _
  constructor
  · intro h
    rw [PrimeFieldTwo.ModuleGeometry.pairing_symm]
    exact h z
  · intro h w
    rcases d.pointVector_zero_or_eq z hz w with hw | hw
    · rw [hw, map_zero]
    · rw [hw, PrimeFieldTwo.ModuleGeometry.pairing_symm]
      exact h

theorem V_card : Nat.card D.V = 8 := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  rw [Nat.card_congr (d.matrixSubspaceEquiv D.V d.V_le_VL).toEquiv]
  change Nat.card (d.matrixSubspace D.V) = 8
  rw [d.matrixSubspace_V z hz]
  exact PrimeFieldTwo.ModuleGeometry.card_perp hz


@[simp] theorem vectorMap_point (z : D.V₁) :
    d.vectorMap (Multiplicative.ofAdd (d.pointVector z)) = z :=
  d.vectorMap_coordinates (inclusion (point_le_VL D) z)

/-- The actor induced by the given element g, with its original LU inclusion. -/
def conjugatingActor : Geometry.Actors := d.matrixProjection ⟨g,mem_sup_left d.g_mem⟩

theorem vectorMap_right (x : M) :
    d.vectorMap (Multiplicative.ofAdd (matrixAction d.conjugatingActor⁻¹ x)) =
      g⁻¹ * d.vectorMap (Multiplicative.ofAdd x) * g := by
  have hh := d.vectorMap_action (⟨g,mem_sup_left d.g_mem⟩ : (D.L ⊔ D.U : Subgroup G))⁻¹ x
  simpa only [conjugatingActor, map_inv, Subgroup.coe_inv, inv_inv] using hh

theorem matrixSubspace_conjugate (A : Subgroup G) :
    d.matrixSubspace (conjugate A g) =
      (d.matrixSubspace A).comap (matrixAction d.conjugatingActor).toLinearMap := by
  ext x
  rw [d.mem_matrixSubspace, conjugate, mem_map_equiv]
  change (MulAut.conj g⁻¹).symm (d.vectorMap (Multiplicative.ofAdd x)) ∈ A ↔
    d.vectorMap (Multiplicative.ofAdd (matrixAction d.conjugatingActor x)) ∈ A
  rw [MulAut.conj_symm_apply, inv_inv]
  exact (congrArg (· ∈ A) (d.vectorMap_action ⟨g,mem_sup_left d.g_mem⟩ x)).symm.to_iff

theorem conjugate_VL_eq : conjugate D.VL g = D.VL :=
  mem_normalizer_iff_map_conj_eq.mp
    ((normalizer (D.VL : Set G)).inv_mem (L_normalizes_VL D d.g_mem))

theorem conjugate_V_le_VL : conjugate D.V g ≤ D.VL := by
  have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) d.V_le_VL
  exact h.trans d.conjugate_VL_eq.le

theorem matrixSubspace_conjugate_V (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    d.matrixSubspace (conjugate D.V g) =
      PrimeFieldTwo.ModuleGeometry.perp (matrixAction d.conjugatingActor⁻¹ (d.pointVector z)) := by
  rw [d.matrixSubspace_conjugate, d.matrixSubspace_V z hz]
  ext x
  change PrimeFieldTwo.ModuleGeometry.pairing (d.pointVector z)
      (matrixAction d.conjugatingActor x) = 0 ↔
    PrimeFieldTwo.ModuleGeometry.pairing (matrixAction d.conjugatingActor⁻¹ (d.pointVector z)) x = 0
  have he := PrimeFieldTwo.ModuleGeometry.pairing_action d.conjugatingActor
    (matrixAction d.conjugatingActor⁻¹ (d.pointVector z)) x
  rw [PrimeFieldTwo.ModuleGeometry.action_cancel_inv] at he
  rw [he]

theorem marked_pair_nonorthogonal (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    PrimeFieldTwo.ModuleGeometry.pairing (d.pointVector z)
      (matrixAction d.conjugatingActor⁻¹ (d.pointVector z)) ≠ 0 := by
  intro h
  apply d.nonorthogonal
  rintro _ ⟨w,hw,rfl⟩
  have hm : matrixAction d.conjugatingActor⁻¹ (d.pointVector ⟨w,hw⟩) ∈ d.matrixSubspace D.V := by
    rw [d.matrixSubspace_V z hz, PrimeFieldTwo.ModuleGeometry.mem_perp]
    rcases d.pointVector_zero_or_eq z hz ⟨w,hw⟩ with hh | hh
    · rw [hh, map_zero, map_zero]
    · rw [hh]; exact h
  rw [d.mem_matrixSubspace, d.vectorMap_right, d.vectorMap_point] at hm
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using hm

/-- The two actual marked hyperplanes span the given natural module. -/
theorem VL_eq_sup_conjugate_V : D.VL = D.V ⊔ conjugate D.V g := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  have hs : d.matrixSubspace D.V ⊔ d.matrixSubspace (conjugate D.V g) = ⊤ := by
    rw [d.matrixSubspace_V z hz, d.matrixSubspace_conjugate_V z hz]
    exact PrimeFieldTwo.ModuleGeometry.perp_sup_eq_top (d.marked_pair_nonorthogonal z hz)
  apply ((d.matrixSubspace_eq_iff le_rfl (sup_le d.V_le_VL d.conjugate_V_le_VL)).mp)
  rw [d.matrixSubspace_VL]
  apply le_antisymm _ le_top
  rw [← hs]
  exact sup_le (d.matrixSubspace_mono le_sup_left) (d.matrixSubspace_mono le_sup_right)

/-- The original marked point misses the opposite marked hyperplane. -/
theorem point_inf_conjugate_V : D.V₁ ⊓ conjugate D.V g = ⊥ := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  apply eq_bot_iff.mpr
  intro w hw
  change w = 1
  rcases d.pointVector_zero_or_eq z hz ⟨w,hw.1⟩ with he | he
  · exact congrArg Subtype.val ((d.pointVector_eq_zero_iff ⟨w,hw.1⟩).mp he)
  · have hm : d.pointVector ⟨w,hw.1⟩ ∈ d.matrixSubspace (conjugate D.V g) := by
      rw [d.mem_matrixSubspace, d.vectorMap_point]
      exact hw.2
    rw [he, d.matrixSubspace_conjugate_V z hz, PrimeFieldTwo.ModuleGeometry.mem_perp,
      PrimeFieldTwo.ModuleGeometry.pairing_symm] at hm
    exact False.elim (d.marked_pair_nonorthogonal z hz hm)

/-- Coordinates on the literal hyperplane intersection, followed by an F₂-basis
of the two-dimensional simultaneous polar kernel. -/
noncomputable def hyperplaneIntersectionEquiv (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    (D.V ⊓ conjugate D.V g : Subgroup G) ≃* Multiplicative (Fin 2 → ZMod 2) :=
  (d.matrixSubspaceEquiv _ (inf_le_left.trans d.V_le_VL)).trans
    (((LinearEquiv.ofEq (d.matrixSubspace (D.V ⊓ conjugate D.V g)) _
      (by rw [d.matrixSubspace_inf, d.matrixSubspace_V z hz,
        d.matrixSubspace_conjugate_V z hz])).trans
      (PrimeFieldTwo.ModuleGeometry.perpInfEquiv (d.marked_pair_nonorthogonal z hz))).toAddEquiv).toMultiplicative

theorem hyperplane_intersection_card : Nat.card (D.V ⊓ conjugate D.V g : Subgroup G) = 4 := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  rw [Nat.card_congr (d.hyperplaneIntersectionEquiv z hz).toEquiv]
  change Nat.card (Fin 2 → ZMod 2) = 4
  simp

theorem hyperplane_intersection_elementary :
    IsElementaryAbelian 2 (D.V ⊓ conjugate D.V g : Subgroup G) := by
  let := d.VL_elementary
  exact IsElementaryAbelian.of_le (inf_le_left.trans d.V_le_VL)


/-- A stabilizer element is recognized by fixing the unique nonzero marked vector. -/
theorem mem_pointStabilizer_iff_fix (z : D.V₁) (hz : d.pointVector z ≠ 0)
    (a : Geometry.Actors) : a ∈ d.pointStabilizer ↔ matrixAction a (d.pointVector z) = d.pointVector z := by
  rw [d.mem_pointStabilizer]
  refine ⟨fun h => h z, ?_⟩
  intro h w
  rcases d.pointVector_zero_or_eq z hz w with hw | hw
  · rw [hw, map_zero]
  · rw [hw]; exact h

theorem matrixSubspace_point_le_span (z : D.V₁) (hz : d.pointVector z ≠ 0) :
    d.matrixSubspace D.V₁ ≤ Submodule.span (ZMod 2) {d.pointVector z} := by
  intro x hx
  let w : D.V₁ := ⟨d.vectorMap (Multiplicative.ofAdd x), hx⟩
  have he : d.pointVector w = x := by
    apply Multiplicative.ofAdd.injective
    apply d.vectorMap_injective
    exact d.vectorMap_point w
  rcases d.pointVector_zero_or_eq z hz w with hw | hw
  · rw [← he, hw]; exact Submodule.zero_mem _
  · rw [← he, hw]; exact Submodule.mem_span_singleton_self _

theorem vectorMap_displacement (a : (D.L ⊔ D.U : Subgroup G)) (x : M) :
    d.vectorMap (Multiplicative.ofAdd (matrixAction (d.matrixProjection a) x - x)) =
      ⁅(a : G), d.vectorMap (Multiplicative.ofAdd x)⁆ := by
  rw [sub_eq_add_neg, ofAdd_add, ofAdd_neg,
    map_mul, map_inv, d.vectorMap_action, commutatorElement_def]

/-- The actual U-image fixes the point, so every displacement is in its hyperplane. -/
theorem commutator_VL_U_le_V : ⁅D.VL, D.U⁆ ≤ D.V := by
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  rw [commutator_comm]
  apply commutator_le.mpr
  intro u hu v hv
  let a : (D.L ⊔ D.U : Subgroup G) := ⟨u,mem_sup_right hu⟩
  let x : M := (d.coordinates ⟨v,hv⟩).toAdd
  have ha : d.matrixProjection a ∈ d.pointStabilizer :=
    d.modelImage_U_le_pointStabilizer ⟨a,hu,rfl⟩
  have hm := PrimeFieldTwo.ModuleGeometry.displacement_mem_perp (d.matrixProjection a)
    ((d.mem_pointStabilizer _).mp ha z) x
  rw [← d.matrixSubspace_V z hz, d.mem_matrixSubspace, d.vectorMap_displacement] at hm
  simpa only [x, ofAdd_toAdd, d.vectorMap_coordinates] using hm

/-- The whole singular-point stabilizer generates the marked hyperplane by displacement. -/
theorem commutator_VL_U_eq_V
    (hsing : ∀ z : D.V₁, (d.pointVector z).det = 0)
    (hstab : d.modelImage D.U = d.pointStabilizer) : ⁅D.VL, D.U⁆ = D.V := by
  apply le_antisymm d.commutator_VL_U_le_V
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  apply (d.matrixSubspace_le_iff d.V_le_VL).mp
  rw [d.matrixSubspace_V z hz]
  apply PrimeFieldTwo.ModuleGeometry.perp_le_of_displacements hz (hsing z)
  intro a ha x
  have hm : a ∈ d.modelImage D.U := hstab.symm ▸ (d.mem_pointStabilizer_iff_fix z hz a).mpr ha
  obtain ⟨u,hu,rfl⟩ := hm
  rw [d.mem_matrixSubspace, d.vectorMap_displacement, commutator_comm D.VL D.U]
  apply commutator_mem_commutator (show (u : G) ∈ D.U from hu)
  exact (d.coordinates.symm (Multiplicative.ofAdd x)).property

/-- The Frattini/derived bound forces the module intersection into the marked
hyperplane; no intersection hypothesis is used. -/
theorem VL_inf_U_eq_V
    (hsing : ∀ z : D.V₁, (d.pointVector z).det = 0)
    (hstab : d.modelImage D.U = d.pointStabilizer) : D.VL ⊓ D.U = D.V := by
  apply le_antisymm _ (le_inf d.V_le_VL (le_conjugateSpanBy _ _))
  obtain ⟨z,hz⟩ := d.exists_pointVector_ne_zero
  apply (d.matrixSubspace_le_iff inf_le_left).mp
  rw [d.matrixSubspace_V z hz]
  intro x hx
  apply PrimeFieldTwo.ModuleGeometry.mem_perp_of_displacements_in_line hz (hsing z)
  intro a ha
  have hm : a ∈ d.modelImage D.U := hstab.symm ▸ (d.mem_pointStabilizer_iff_fix z hz a).mpr ha
  obtain ⟨u,hu,rfl⟩ := hm
  apply d.matrixSubspace_point_le_span z hz
  rw [d.mem_matrixSubspace, d.vectorMap_displacement]
  apply derived_le_point d.base d.closure
  exact commutator_mem_commutator (show (u : G) ∈ D.U from hu) (show d.vectorMap (Multiplicative.ofAdd x) ∈ D.U from hx.2)

/-- Conjugating the derived intersection keeps the source right-conjugation convention. -/
theorem VL_inf_conjugate_U_eq_conjugate_V
    (hsing : ∀ z : D.V₁, (d.pointVector z).det = 0)
    (hstab : d.modelImage D.U = d.pointStabilizer) :
    D.VL ⊓ conjugate D.U g = conjugate D.V g := by
  have he := congrArg (fun A : Subgroup G => conjugate A g) (d.VL_inf_U_eq_V hsing hstab)
  change (D.VL ⊓ D.U).map (MulAut.conj g⁻¹).toMonoidHom = _ at he
  rw [map_inf _ _ _ (MulAut.conj g⁻¹).injective] at he
  change conjugate D.VL g ⊓ conjugate D.U g = conjugate D.V g at he
  rwa [d.conjugate_VL_eq] at he

/-- The literal intersection used by the quotient-image directness argument. -/
theorem VL_inf_U_inf_conjugate_U
    (hsing : ∀ z : D.V₁, (d.pointVector z).det = 0)
    (hstab : d.modelImage D.U = d.pointStabilizer) :
    D.VL ⊓ (D.U ⊓ conjugate D.U g) = D.V ⊓ conjugate D.V g := by
  calc
    D.VL ⊓ (D.U ⊓ conjugate D.U g) = (D.VL ⊓ D.U) ⊓ (D.VL ⊓ conjugate D.U g) :=
      inf_inf_distrib_left _ _ _
    _ = D.V ⊓ conjugate D.V g := by
      rw [d.VL_inf_U_eq_V hsing hstab, d.VL_inf_conjugate_U_eq_conjugate_V hsing hstab]

end Hypothesis

namespace Chapter15
open CFSG.Quasithin.Chapter15.Section03
open CFSG.Quasithin.Chapter15.Section03.Nonabelian
variable {G : Type*} [Group G] [Finite G]
variable {Z ZS Zperp V Y T : Subgroup G} {g : G}

/-- The unconditional marked geometry in the literal substitution of 15.3.54.
Here Zperp is the source Z-perpendicular subgroup and V is its four-space. -/
theorem marked_hyperplane_geometry
    (d : Hypothesis (setup Z Zperp Y T) g) (hspan : localSpan Z Y = V) :
    V = Zperp ⊔ rightConjugate Zperp g ∧ Nat.card Zperp = 8 ∧
      Z ⊓ rightConjugate Zperp g = ⊥ ∧
      IsElementaryAbelian 2 (Zperp ⊓ rightConjugate Zperp g : Subgroup G) ∧
      Nat.card (Zperp ⊓ rightConjugate Zperp g : Subgroup G) = 4 := by
  have hv := VL_eq (Zperp := Zperp) (T := T) hspan
  have hs := d.VL_eq_sup_conjugate_V
  rw [hv] at hs
  exact ⟨hs, d.V_card, d.point_inf_conjugate_V,
    d.hyperplane_intersection_elementary, d.hyperplane_intersection_card⟩

/-- An actual isomorphism on the two marked Chapter 15 hyperplanes. -/
noncomputable def markedHyperplaneIntersectionEquiv
    (d : Hypothesis (setup Z Zperp Y T) g) (z : Z) (hz : d.pointVector z ≠ 0) :
    (Zperp ⊓ rightConjugate Zperp g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2) :=
  d.hyperplaneIntersectionEquiv z hz

/-- The later Chapter 15 coprime-action step supplies the containment premise.
Once supplied, the intersection is the literal E₄ already computed here. -/
theorem closure_intersection_eq_of_le
    (d : Hypothesis (setup Z Zperp Y T) g)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y = V)
    (hsing : ∀ z : Z, (d.pointVector z).det = 0)
    (hstab : d.modelImage (setup Z Zperp Y T).U = d.pointStabilizer)
    (hcontained : closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ≤ V) :
    closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g =
      Zperp ⊓ rightConjugate Zperp g := by
  have h := d.VL_inf_U_inf_conjugate_U hsing hstab
  rw [VL_eq hspan, closure_eq hZS hperp] at h
  change V ⊓ (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g) =
    Zperp ⊓ rightConjugate Zperp g at h
  rwa [inf_eq_right.mpr hcontained] at h

/-- This comparison is on the actual closure intersection, after the independent
coprime-action containment has been established. -/
noncomputable def closureIntersectionEquiv
    (d : Hypothesis (setup Z Zperp Y T) g)
    (hZS : ZS ≤ Zperp) (hperp : Zperp ≤ closureU Z ZS) (hspan : localSpan Z Y = V)
    (hsing : ∀ z : Z, (d.pointVector z).det = 0)
    (hstab : d.modelImage (setup Z Zperp Y T).U = d.pointStabilizer)
    (hcontained : closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g ≤ V)
    (z : Z) (hz : d.pointVector z ≠ 0) :
    (closureU Z ZS ⊓ rightConjugate (closureU Z ZS) g : Subgroup G) ≃*
      Multiplicative (Fin 2 → ZMod 2) :=
  (MulEquiv.subgroupCongr (closure_intersection_eq_of_le d hZS hperp hspan hsing hstab hcontained)).trans
    (markedHyperplaneIntersectionEquiv d z hz)

end Chapter15

end CFSG.Quasithin.ChapterG.Section02.OrthogonalPlusFour
