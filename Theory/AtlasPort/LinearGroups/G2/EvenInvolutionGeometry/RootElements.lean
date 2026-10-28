module

public import Theory.AtlasPort.LinearGroups.G2.SylowParabolicInvariance.Binary

/-!
# Actual root elements and central involutions of G₂

Root elements are defined by conjugacy to the explicit octonion root maps A
(long) and C (short). The standard Sylow-center calculations imply that every
nonidentity central involution of a Sylow subgroup is a long-root element.
The binary statement uses the Sylow subgroup of the actual commutator group,
with conjugation and the root representative embedded in the full G₂(2).
These statements do not assert exhaustive conjugacy of all involutions.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, 16.1.4(1), 16.1.6 and 16.5.13, printed pp.1171–1172
and 1201–1202. Coordinates are from the licensed ATLAS port; see
LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup
namespace Atlas.G2.EvenInvolutionGeometry
open LieParabolicSetup SylowParabolicInvariance BinaryParabolicPair
variable {F : Type*} [Field F]

/-- A nonidentity element in a conjugate of the actual highest long-root group. -/
def IsLongRootElement (x : Model F) : Prop :=
  ∃ (g : Model F) (a : F), a ≠ 0 ∧ x = MulAut.conj g (rootA a)

/-- A nonidentity element in a conjugate of the actual highest short-root group. -/
def IsShortRootElement (x : Model F) : Prop :=
  ∃ (g : Model F) (a : F), a ≠ 0 ∧ x = MulAut.conj g (rootC a)

/-- Either root length, defined through actual octonion automorphisms. -/
def IsRootElement (x : Model F) : Prop := IsLongRootElement x ∨ IsShortRootElement x

/-- One of the two standard root-defined parabolic families. -/
def IsRootParabolic (P : Subgroup (Model F)) : Prop :=
  ∃ g : Model F, P = parabolic₁.map (MulAut.conj g).toMonoidHom ∨
    P = parabolic₂.map (MulAut.conj g).toMonoidHom

theorem rootA_isLongRootElement {a : F} (ha : a ≠ 0) : IsLongRootElement (rootA a) :=
  ⟨1,a,ha,by simp⟩

theorem rootC_isShortRootElement {a : F} (ha : a ≠ 0) : IsShortRootElement (rootC a) :=
  ⟨1,a,ha,by simp⟩

variable [CharP F 2]

theorem central_involution_isLongRoot [Finite F]
    (S : Sylow 2 (Model F)) {x : Model F} (hx : x ∈ S) (hsq : x ^ 2 = 1)
    (hc : ∀ y ∈ S, Commute x y) (hne : x ≠ 1) : IsLongRootElement x := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (Model F) (sylow (F := F)) S
  have hm : unipotent.map (MulAut.conj g).toMonoidHom = (S : Subgroup (Model F)) :=
    congrArg Sylow.toSubgroup hg
  have hx' : x ∈ unipotent.map (MulAut.conj g).toMonoidHom := hm.symm ▸ hx
  obtain ⟨y,hy,rfl⟩ := hx'
  have hcent : CentralInvolution unipotent y := by
    apply (centralInvolution_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      unipotent y).mp
    rw [hm]
    exact ⟨hm ▸ mem_map_of_mem _ hy,hsq,hc⟩
  obtain ⟨a,ha⟩ := (highestRoot_iff_centralInvolution y).mpr hcent
  refine ⟨g,a.toAdd,?_,?_⟩
  · intro hzero
    apply hne
    change MulAut.conj g y = 1
    rw [← ha]
    change MulAut.conj g (rootA a.toAdd) = 1
    rw [hzero,rootA_zero,map_one]
  · exact congrArg (MulAut.conj g) ha.symm

omit [CharP F 2] in
theorem binary_central_involution_isLongRoot
    (S : Sylow 2 DerivedModel) {x : DerivedModel} (hx : x ∈ S) (hsq : x ^ 2 = 1)
    (hc : ∀ y ∈ S, Commute x y) (hne : x ≠ 1) : IsLongRootElement x.val := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq DerivedModel derivedSylow S
  have hm : (derivedSylow : Subgroup DerivedModel).map (MulAut.conj g).toMonoidHom =
      (S : Subgroup DerivedModel) := congrArg Sylow.toSubgroup hg
  have hx' : x ∈ (derivedSylow : Subgroup DerivedModel).map
      (MulAut.conj g).toMonoidHom := hm.symm ▸ hx
  obtain ⟨y,hy,rfl⟩ := hx'
  have hcent : CentralInvolution (derivedSylow : Subgroup DerivedModel) y := by
    apply (centralInvolution_map_iff (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
      (derivedSylow : Subgroup DerivedModel) y).mp
    rw [hm]
    exact ⟨hm ▸ mem_map_of_mem _ hy,hsq,hc⟩
  have hamb : CentralInvolution derivedSylowAmbient y.val := by
    rw [← derivedSylow_map_subtype]
    exact (centralInvolution_map_iff DerivedModel.subtype DerivedModel.subtype_injective
      (derivedSylow : Subgroup DerivedModel) y).mpr hcent
  obtain ⟨a,ha⟩ := (binary_highestRoot_iff y.val).mpr hamb
  refine ⟨g.val,a.toAdd,?_,?_⟩
  · intro hzero
    apply hne
    apply Subtype.ext
    change MulAut.conj g.val y.val = 1
    rw [← ha]
    change MulAut.conj g.val (rootA a.toAdd) = 1
    rw [hzero,rootA_zero,map_one]
  · exact congrArg (MulAut.conj g.val) ha.symm

end Atlas.G2.EvenInvolutionGeometry
