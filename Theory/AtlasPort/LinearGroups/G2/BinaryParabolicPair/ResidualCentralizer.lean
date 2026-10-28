module

public import Theory.AtlasPort.LinearGroups.G2.BinaryParabolicPair.SevenSylowOvergroups.Basic
public import Theory.AtlasPort.LinearGroups.G2.LieAutomorphismExtensions.BinaryAutomorphismGroup
public import Theory.AtlasPort.LinearGroups.G2.DerivedNormalizerSolvable.Binary
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# Fixers of the second derived binary parabolic residual

The three-residual of the second parabolic contains its displayed cubic and
the conjugate of that cubic by C(1)E(1)F(1). Five matrix entries, checked on
the 64 positive-root coordinates, show that their common centralizer in the
full unipotent group is trivial. Checking only the original cubic would be
insufficient: the outer root element C(1) centralizes it.

Every automorphism of G₂(2)′ is already proved to come from conjugation in
G₂(2). If it preserves the derived Sylow subgroup, its inducing element
belongs to the full unipotent group. The two-cubic calculation therefore
proves triviality of the residual's pointwise fixer even when outer
automorphisms are allowed.

Source: Aschbacher--Smith, 15.3.43, printed p.1140. Root coordinates and the
automorphism identification use the licensed ATLAS port through the imports;
see LICENSES/ATLAS.txt and LICENSES/ATLAS-CITATION.cff.
-/

@[expose] public section

open Subgroup
namespace Atlas.G2.BinaryParabolicPair
open Atlas.SplitOctonion BinaryCore LieAutomorphismExtensions SevenSylowOvergroups

/-- The actual O^{3′} of the second parabolic, included in G₂(2)′. -/
def secondResidual : Subgroup DerivedModel :=
  (primeToResidual 3 derivedSecond).map derivedSecond.subtype

private def conjugateMovingActor : Model (ZMod 2) :=
  sylowGenerator * movingActor * sylowGenerator⁻¹

set_option maxRecDepth 100000 in
private theorem centralizing_coordinates : ∀ t : Fin 6 → ZMod 2,
    (unipotentProduct t * movingActor).val (basisVector 1) 0 =
      (movingActor * unipotentProduct t).val (basisVector 1) 0 →
    (unipotentProduct t * conjugateMovingActor).val (basisVector 3) 1 =
      (conjugateMovingActor * unipotentProduct t).val (basisVector 3) 1 →
    (unipotentProduct t * movingActor).val (basisVector 5) 0 =
      (movingActor * unipotentProduct t).val (basisVector 5) 0 →
    (unipotentProduct t * movingActor).val (basisVector 6) 0 =
      (movingActor * unipotentProduct t).val (basisVector 6) 0 →
    (unipotentProduct t * conjugateMovingActor).val (basisVector 6) 0 =
      (conjugateMovingActor * unipotentProduct t).val (basisVector 6) 0 → t = 0 := by
  decide +kernel

private theorem unipotent_two_cubic_fixer {g : Model (ZMod 2)}
    (hg : g ∈ unipotent) (ha : g * movingActor = movingActor * g)
    (hb : g * conjugateMovingActor = conjugateMovingActor * g) : g = 1 := by
  rw [unipotent_eq_range] at hg
  obtain ⟨t, rfl⟩ := hg
  have ht := centralizing_coordinates t
    (congrArg (fun x : Model (ZMod 2) => x.val (basisVector 1) 0) ha)
    (congrArg (fun x : Model (ZMod 2) => x.val (basisVector 3) 1) hb)
    (congrArg (fun x : Model (ZMod 2) => x.val (basisVector 5) 0) ha)
    (congrArg (fun x : Model (ZMod 2) => x.val (basisVector 6) 0) ha)
    (congrArg (fun x : Model (ZMod 2) => x.val (basisVector 6) 0) hb)
  rw [ht, unipotentProduct_zero]

private theorem movingActor_mem_secondResidual :
    (⟨movingActor, movingActor_mem_derived⟩ : DerivedModel) ∈ secondResidual := by
  refine ⟨⟨⟨movingActor, movingActor_mem_derived⟩, movingActor_mem_derivedSecond⟩, ?_, rfl⟩
  apply mem_primeToResidual_of_pow (n := 1)
  exact Subtype.ext (Subtype.ext (by simpa using movingActor_cube))

private theorem conjugateMovingActor_mem_derived : conjugateMovingActor ∈ DerivedModel :=
  (inferInstance : DerivedModel.Normal).conj_mem _ movingActor_mem_derived _

private theorem conjugateMovingActor_mem_secondResidual :
    (⟨conjugateMovingActor, conjugateMovingActor_mem_derived⟩ : DerivedModel) ∈
      secondResidual := by
  let u : derivedSecond :=
    ⟨⟨sylowGenerator, sylowGenerator_mem.2⟩, unipotent_le_parabolic sylowGenerator_mem.1⟩
  let a : derivedSecond :=
    ⟨⟨movingActor, movingActor_mem_derived⟩, movingActor_mem_derivedSecond⟩
  have ha : a ∈ primeToResidual 3 derivedSecond := by
    apply mem_primeToResidual_of_pow (n := 1)
    exact Subtype.ext (Subtype.ext (by simpa using movingActor_cube))
  exact ⟨u * a * u⁻¹, (inferInstance : (primeToResidual 3 derivedSecond).Normal).conj_mem
    a ha u, rfl⟩

/-- The full unipotent group has no nonidentity element centralizing the actual
second derived parabolic's three-residual. -/
theorem unipotent_centralizer_secondResidual :
    unipotent ⊓ centralizer
      (secondResidual.map DerivedModel.subtype : Set (Model (ZMod 2))) = ⊥ := by
  apply bot_unique
  rintro g ⟨hg, hc⟩
  apply mem_bot.mpr
  apply unipotent_two_cubic_fixer hg
  · exact (hc _ (mem_map_of_mem DerivedModel.subtype movingActor_mem_secondResidual)).symm
  · exact (hc _ (mem_map_of_mem DerivedModel.subtype
      conjugateMovingActor_mem_secondResidual)).symm

/-- The corresponding centralizer inside the actual derived Sylow is trivial. -/
theorem derivedSylow_centralizer_secondResidual :
    (derivedSylow : Subgroup DerivedModel) ⊓
      centralizer (secondResidual : Set DerivedModel) = ⊥ := by
  apply bot_unique
  rintro g ⟨hg, hc⟩
  apply mem_bot.mpr
  apply Subtype.ext
  have h : g.val ∈ unipotent ⊓ centralizer
      (secondResidual.map DerivedModel.subtype : Set (Model (ZMod 2))) := by
    refine ⟨derivedSylow_eq.le hg, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    exact congrArg Subtype.val (hc x hx)
  rw [unipotent_centralizer_secondResidual] at h
  exact h

/-- Sylow-preserving automorphisms fixing the second three-residual pointwise
are trivial, including automorphisms induced outside the derived group. -/
theorem automorphism_eq_one_of_secondResidual (β : MulAut DerivedModel)
    (hS : (derivedSylow : Subgroup DerivedModel).map β.toMonoidHom = derivedSylow)
    (hfix : ∀ x ∈ secondResidual, β x = x) : β = 1 := by
  obtain ⟨g, rfl⟩ := binaryConjugation_surjective β
  have hn : g ∈ normalizer (derivedSylowAmbient : Set (Model (ZMod 2))) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have h := congrArg (Subgroup.map DerivedModel.subtype) hS
    rw [map_map, derivedSylow_map_subtype] at h
    conv_lhs => rw [← derivedSylow_map_subtype, map_map]
    convert h using 1
    ext x
    rfl
  have hg : g ∈ unipotent := by
    rwa [DerivedNormalizerSolvable.binary_normalizer_derivedSylowAmbient] at hn
  have hc : g ∈ centralizer
      (secondResidual.map DerivedModel.subtype : Set (Model (ZMod 2))) := by
    rintro _ ⟨x, hx, rfl⟩
    have h := congrArg Subtype.val (hfix x hx)
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  have he : g = 1 := by
    have h := (show g ∈ unipotent ⊓ centralizer
      (secondResidual.map DerivedModel.subtype : Set (Model (ZMod 2))) from ⟨hg, hc⟩)
    rwa [unipotent_centralizer_secondResidual] at h
  rw [he, map_one]

end Atlas.G2.BinaryParabolicPair
