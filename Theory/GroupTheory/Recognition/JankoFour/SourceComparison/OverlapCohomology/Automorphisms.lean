module
public import Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology.Twists
public import Theory.Representation.SymplecticFourBinaryNormalizer
public import Theory.GroupTheory.CentralCharacteristicAutomorphisms

/-!
# All automorphisms of the native hexad quotient

An automorphism preserves the intrinsic two-core and acts linearly on its
natural four-space. This linear map intertwines the induced automorphism
of the full Sp4(2) quotient. The proved binary symplectic normalizer theorem
realizes it by a symplectic element, which lifts to the same native hexad
group. Removing that inner automorphism leaves a pointwise radical fixer;
the explicit cocycle classification then gives the quadratic twist.

Source: Aschbacher–Segev, Invent. Math. 105 (1991), (8.2), p.606.
This proves the full quotient automorphism calculation, without a
pointwise-fixation hypothesis, for the later lift to the original overlap.
-/

public section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
open Subgroup Representation Representation.OneCohomology
open Sporadic.Mathieu.M22ChapterH.Hexad.Action

private noncomputable def radicalAut (α : MulAut Outer) : MulAut (pCore 2 Outer) :=
  MulAut.characteristic (pCore 2 Outer) α

private noncomputable def vectorAddAut (α : MulAut Outer) : V ≃+ V where
  toFun v := (nativeCoordinates (radicalAut α (nativeCoordinates.symm (Multiplicative.ofAdd v)))).toAdd
  invFun v := (nativeCoordinates ((radicalAut α).symm (nativeCoordinates.symm (Multiplicative.ofAdd v)))).toAdd
  left_inv v := by simp only [ofAdd_toAdd,MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply,toAdd_ofAdd]
  right_inv v := by simp only [ofAdd_toAdd,MulEquiv.symm_apply_apply,MulEquiv.apply_symm_apply,toAdd_ofAdd]
  map_add' v w := by
    change (nativeCoordinates (radicalAut α (nativeCoordinates.symm
      (Multiplicative.ofAdd v * Multiplicative.ofAdd w)))).toAdd = _
    rw [map_mul,map_mul,map_mul]
    rfl

private noncomputable def vectorAut (α : MulAut Outer) : V ≃ₗ[ZMod 2] V :=
  (vectorAddAut α).toLinearEquiv (ZMod.map_smul (vectorAddAut α))

private theorem vectorAut_coordinates (α : MulAut Outer) (n : pCore 2 Outer) :
    vectorAut α (nativeCoordinates n).toAdd = (nativeCoordinates (radicalAut α n)).toAdd := by
  change (nativeCoordinates (radicalAut α (nativeCoordinates.symm
    (Multiplicative.ofAdd (nativeCoordinates n).toAdd)))).toAdd = _
  rw [ofAdd_toAdd,MulEquiv.symm_apply_apply]

private noncomputable def actorAut (α : MulAut Outer) : MulAut Sp :=
  nativeQuotient.symm.trans ((quotientAut (pCore 2 Outer) α).trans nativeQuotient)

private theorem actorAut_actor (α : MulAut Outer) (g : Outer) :
    actorAut α (nativeActor g) = nativeActor (α g) := by
  change nativeQuotient (quotientAut (pCore 2 Outer) α
    (nativeQuotient.symm (nativeQuotient (QuotientGroup.mk' _ g)))) = _
  rw [MulEquiv.symm_apply_apply,quotientAut_apply_mk]
  rfl

private theorem vectorAut_intertwines (α : MulAut Outer) (s : Sp) (v : V) :
    vectorAut α (natural s v) = natural (actorAut α s) (vectorAut α v) := by
  obtain ⟨g,rfl⟩ := nativeActor_surjective s
  obtain ⟨n,hn⟩ := nativeCoordinates.surjective (Multiplicative.ofAdd v)
  have hv : v = (nativeCoordinates n).toAdd := (congrArg Multiplicative.toAdd hn).symm
  rw [hv,←nativeCoordinates_conjugation,vectorAut_coordinates,actorAut_actor,
    vectorAut_coordinates,←nativeCoordinates_conjugation]
  congr 2
  apply Subtype.ext
  change α (g*n.val*g⁻¹) = α g * α n.val * (α g)⁻¹
  simp only [map_mul,map_inv]

/-- Every automorphism of the native hexad group has its radical action
induced by an actual element of that same group. -/
theorem native_automorphism_radical_inner (α : MulAut Outer) :
    ∃ x : Outer, ∀ n : pCore 2 Outer, α n.val = x*n.val*x⁻¹ := by
  obtain ⟨s,hs⟩ := SymplecticFourBinaryNormalizer.normalizer
    (vectorAut α) (actorAut α) (vectorAut_intertwines α)
  obtain ⟨x,hx⟩ := nativeActor_surjective s
  refine ⟨x,fun n => ?_⟩
  have he := hs (nativeCoordinates n).toAdd
  rw [vectorAut_coordinates,←hx,←nativeCoordinates_conjugation] at he
  exact congrArg Subtype.val (nativeCoordinates.injective (Multiplicative.toAdd.injective he))

/-- All automorphisms of the genuine native hexad group are inner, optionally
followed by the explicitly constructed quadratic correction. -/
theorem native_all_automorphisms (α : MulAut Outer) :
    ∃ x : Outer, α = MulAut.conj x ∨ α = MulAut.conj x * nativeQuadraticTwist := by
  obtain ⟨x,hx⟩ := native_automorphism_radical_inner α
  let β : MulAut Outer := (MulAut.conj x)⁻¹ * α
  have hb : ∀ n ∈ pCore 2 Outer, β n = n := by
    intro n hn
    change (MulAut.conj x)⁻¹ (α n) = n
    rw [←map_inv,MulAut.conj_apply,hx ⟨n,hn⟩]
    group
  obtain ⟨n,hn⟩ := native_automorphism_factorization β hb
  have he : α = MulAut.conj x * β := by dsimp [β]; group
  refine ⟨x*n.val,?_⟩
  rcases hn with hn | hn
  · left
    rw [he,hn,map_mul]
  · right
    rw [he,hn,map_mul,mul_assoc]

end Theory.GroupTheory.Recognition.JankoFour.SourceComparison.OverlapCohomology
