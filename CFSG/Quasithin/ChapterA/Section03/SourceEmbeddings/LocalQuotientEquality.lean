module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BinaryIntrinsicQuotients
public import Theory.GroupTheory.CComponent.LocalImageEquality
public import Theory.GroupTheory.PerfectNormalizerLift

/-!
# Equality of comparable local components through quotient maps

Restrict the original full Sylow to the larger local component. Equality
of images through a two-group kernel lifts by local C-component minimality.
For a further central kernel, perfectness first lifts equality to the
intrinsic two-core quotient. Both maps remain the given homomorphisms.

The actual consumer is the proper A₇ containing projection in
LocalConfigurationRigidityHigherSevenCatalogue. Source: Aschbacher–Smith,
A.3.11–12 and original 12.2.25, printed pp.46–48,805.
-/

public noncomputable section
namespace CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
open Subgroup Theory.GroupTheory

/-- Comparable local components are separated by any homomorphism with two-group kernel. -/
theorem local_eq_of_two_kernel_map_eq {X Q : Type*} [Group X] [Finite X] [Group Q]
    (T : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ localCComponents T) (hK : K ∈ localCComponents T) (hBK : B ≤ K)
    (f : X →* Q) (hk : IsPGroup 2 f.ker) (he : B.map f = K.map f) : B = K := by
  obtain ⟨S,_,hlocal⟩ := BinaryIntrinsic.local_in_local_overgroup T hB hK hBK
  have htop : (⊤ : Subgroup K).IsCComponent := by
    simpa only [subgroupOf_self] using
      hK.subgroupOf_of_le (show K ≤ K from le_rfl) (show K ≤ K ⊔ T from le_sup_left)
  let g := f.comp K.subtype
  have hg : IsPGroup 2 g.ker := hk.comap_subtype
  have he' : (B.subgroupOf K).map g = (⊤ : Subgroup K).map g := by
    calc
      _ = B.map f := by rw [← map_map,map_subgroupOf_eq_of_le hBK]
      _ = K.map f := he
      _ = (⊤ : Subgroup K).map g := by
        change K.map f = (⊤ : Subgroup K).map (f.comp K.subtype)
        rw [← MonoidHom.range_eq_map,MonoidHom.range_comp,range_subtype]
  have ht := local_cComponent_eq_of_map_eq hlocal htop le_top g
    (hg.le_sylow_of_normal S) he'
  exact le_antisymm hBK (subgroupOf_eq_top.mp ht)

/-- Equality after a central quotient of the intrinsic two-core quotient lifts
through both original maps to equality of the local components. -/
theorem local_eq_of_central_twoCore_map_eq {X Q : Type*} [Group X] [Finite X] [Group Q]
    (T : Sylow 2 X) {B K : Subgroup X}
    (hB : B ∈ localCComponents T) (hK : K ∈ localCComponents T) (hBK : B ≤ K)
    (f : (X ⧸ pCore 2 X) →* Q) (hk : f.ker ≤ center (X ⧸ pCore 2 X))
    (he : B.map (f.comp (QuotientGroup.mk' (pCore 2 X))) =
      K.map (f.comp (QuotientGroup.mk' (pCore 2 X)))) : B = K := by
  let q := QuotientGroup.mk' (pCore 2 X)
  have perfect {J : Subgroup X} (hJ : J ∈ localCComponents T) : Group.IsPerfect J := by
    let := hJ.perfect
    exact Group.IsPerfect.ofSurjective
      (f := (subgroupOfEquivOfLe (show J ≤ J ⊔ T from le_sup_left)).toMonoidHom)
      (subgroupOfEquivOfLe le_sup_left).surjective
  let := perfect hB
  let := perfect hK
  let : Group.IsPerfect (B.map q) := Group.IsPerfect.map q
  let : Group.IsPerfect (K.map q) := Group.IsPerfect.map q
  have he' : (B.map q).map f = (K.map q).map f := by simpa only [map_map] using he
  have hmaps : B.map q = K.map q := le_antisymm (map_mono hBK)
    (le_of_map_le_of_perfect f hk _ _ he'.ge)
  exact local_eq_of_two_kernel_map_eq T hB hK hBK q
    (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) hmaps

end CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings
