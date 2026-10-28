module
public import Theory.SpecificGroups.SL2.Affine.Core
public import Theory.SpecificGroups.SL2.NaturalStabilizer
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Centralizers of translations in affine plane extensions

A nonidentity translation has a two-group centralizer in ASL₂(F): its linear
image fixes a nonzero natural vector and its kernel consists of translations.
If that translation is central in a Sylow subgroup S, its centralizer in the
affine group is exactly S. Consequently its centralizer in the full affine
normalizer normalizes S. This needs no realization of that normalizer as a
PSL₃ automorphism group, and includes F₄.

Source: the local intersection bound in Aschbacher–Smith §5.3.7, printed
p.660 (`refs/quasithin.pdf`), via the elementary natural SL₂ stabilizer calculation.
-/

public noncomputable section
open Subgroup Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearAmbientGeometry
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
/-- A nonzero translation has a two-group centralizer. -/
theorem affine_translation_centralizer_isPGroup
    (z : SL2.Affine F) (hz : z ∈ SL2.translations F) (hne : z ≠ 1) :
    IsPGroup 2 (centralizer ({z} : Set (SL2.Affine F))) := by
  rw [← SL2.range_inl_eq_translations] at hz
  obtain ⟨v,rfl⟩ := hz
  have hv : v.toAdd ≠ 0 := by
    intro h
    apply hne
    have hv : v = 1 := Multiplicative.toAdd.injective h
    rw [hv,map_one]
  let f : SL2.Affine F →* SL(2,F) := SemidirectProduct.rightHom
  apply ((SL2.stabilizer_nonzero_isPGroup v.toAdd hv).comap_of_ker_isPGroup
    f (SL2.translations_isPGroup F)).to_le
  intro g hg
  have hc := mem_centralizer_singleton_iff.mp hg
  have he : SL2.naturalAction F g.right v = v := by
    apply SemidirectProduct.inl_injective (φ := SL2.naturalAction F)
    rw [← SL2.conjugate_inl, mul_inv_eq_iff_eq_mul]
    exact hc
  exact congrArg Multiplicative.toAdd he

variable {G : Type*} [Group G]

/-- Transport the translation centralizer to the literal core of an affine subgroup. -/
theorem affine_core_centralizer_isPGroup
    (X : Subgroup G) (e : X ≃* SL2.Affine F)
    (z : G) (hz : z ∈ X.pCoreIn 2) (hne : z ≠ 1) :
    IsPGroup 2 (X ⊓ centralizer ({z} : Set G) : Subgroup G) := by
  let z' : X := ⟨z,pCoreIn_le 2 X hz⟩
  have hz' : z' ∈ pCore 2 X := (mem_map_iff_mem X.subtype_injective).mp hz
  have hez : e z' ∈ SL2.translations F := by
    rw [← SL2.affine_twoCore_eq,← pCore_map_iso 2 e]
    exact mem_map_of_mem e.toMonoidHom hz'
  have hn : e z' ≠ 1 := by
    intro h
    apply hne
    exact congrArg X.subtype (e.injective (h.trans (map_one e).symm))
  have hp := (affine_translation_centralizer_isPGroup (e z') hez hn).comap_of_injective
    e.toMonoidHom e.injective
  have heq : ((centralizer ({e z'} : Set (SL2.Affine F))).comap e.toMonoidHom).map
      X.subtype = X ⊓ centralizer ({z} : Set G) := by
    ext x
    constructor
    · rintro ⟨x,hx,rfl⟩
      refine ⟨x.property,mem_centralizer_singleton_iff.mpr ?_⟩
      have hc := mem_centralizer_singleton_iff.mp hx
      have hc' : x * z' = z' * x := e.injective (by
        simpa only [map_mul,MulEquiv.coe_toMonoidHom] using hc)
      exact congrArg X.subtype hc'
    · intro hx
      refine ⟨⟨x,hx.1⟩,?_,rfl⟩
      apply mem_centralizer_singleton_iff.mpr
      have hc' : (⟨x,hx.1⟩ : X) * z' = z' * (⟨x,hx.1⟩ : X) :=
        Subtype.ext (mem_centralizer_singleton_iff.mp hx.2)
      simpa only [map_mul,MulEquiv.coe_toMonoidHom] using congrArg e hc'
  exact heq ▸ hp.map X.subtype

/-- A central core element recovers the embedded Sylow from its affine centralizer. -/
theorem affine_sylow_centralizer
    (X S : Subgroup G) (e : X ≃* SL2.Affine F)
    (P : Sylow 2 X) (hP : (P : Subgroup X).map X.subtype = S)
    (z : G) (hz : z ∈ X.pCoreIn 2) (hne : z ≠ 1)
    (hzc : S ≤ centralizer ({z} : Set G)) :
    X ⊓ centralizer ({z} : Set G) = S := by
  have hp := (affine_core_centralizer_isPGroup X e z hz hne).comap_subtype (K := X)
  have he : (X ⊓ centralizer ({z} : Set G)).subgroupOf X = (P : Subgroup X) :=
    P.is_maximal' hp (fun x hx => ⟨x.property,hzc (hP ▸ mem_map_of_mem X.subtype hx)⟩)
  have hm := congrArg (fun Y : Subgroup X => Y.map X.subtype) he
  simpa only [subgroupOf_map_subtype,inf_le_left,inf_of_le_left,hP] using hm

end Matrix.PSL3.LinearAmbientGeometry
