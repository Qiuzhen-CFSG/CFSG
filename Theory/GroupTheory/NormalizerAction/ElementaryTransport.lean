module
public import Theory.GroupTheory.NormalizerAction.Simple
public import Theory.ElementaryAbelian.Basic

/-!
# Original elementary subgroups in a component automizer

Normalization passes through the literal normalizer quotient. Membership
of its component image lifts to the component times its centralizer.
For commuting factor coordinates, the automizer image of the original
subgroup is exactly the injective image of its first projection.

These identities retain the maps needed in the paired cases of
Aschbacher–Smith E.2.7, printed p.219.
-/

public section
open Subgroup
namespace Subgroup.NormalizerAction
variable {H : Type*} [Group H] (K : Subgroup H)

theorem normalized_image (T V : Subgroup H)
    (hTV : T ≤ normalizer (V : Set H)) :
    (T.subgroupOf (normalizer (K : Set H))).map (quotient K) ≤
      normalizer ((V.subgroupOf (normalizer (K : Set H))).map (quotient K) : Set (Star K)) := by
  apply le_trans (map_mono (le_trans (comap_mono hTV) (le_normalizer_comap _)))
  exact le_normalizer_map _

theorem le_component_centralizer_of_image_le (V : Subgroup H)
    (hVN : V ≤ normalizer (K : Set H))
    (hV : (V.subgroupOf (normalizer (K : Set H))).map (quotient K) ≤ componentImage K) :
    V ≤ K ⊔ centralizer (K : Set H) := by
  intro v hv
  let vn : normalizer (K : Set H) := ⟨v,hVN hv⟩
  obtain ⟨k,hk,he⟩ := hV (mem_map_of_mem (quotient K) (show vn ∈ V.subgroupOf _ from hv))
  have hz : (k : H)⁻¹ * v ∈ centralizer (K : Set H) := by
    apply (quotient_eq_one_iff K (k⁻¹ * vn)).mp
    rw [map_mul,map_inv,he,inv_mul_cancel]
  have hh := (K ⊔ centralizer (K : Set H)).mul_mem (mem_sup_left hk) (mem_sup_right hz)
  change (k:H) * ((k:H)⁻¹ * v) ∈ K ⊔ centralizer (K : Set H) at hh
  simpa only [mul_inv_cancel_left] using hh

theorem componentMap_projection_eq (D V : Subgroup H)
    (hD : D ≤ centralizer (K : Set H))
    (f : K × D →* H) (hmul : ∀ k d, f (k,d) = (k:H)*(d:H))
    (himage : (V.comap f).map f = V) :
    ((V.comap f).map (MonoidHom.fst K D)).map (componentMap K) =
      (V.subgroupOf (normalizer (K : Set H))).map (quotient K) := by
  have hn (k : K) (d : D) : f (k,d) ∈ normalizer (K : Set H) := by
    rw [hmul]
    exact (normalizer (K : Set H)).mul_mem (K.le_normalizer k.property)
      (centralizer_le_normalizer _ (hD d.property))
  have he (k : K) (d : D) :
      quotient K ⟨f (k,d),hn k d⟩ = componentMap K k := by
    let dn : normalizer (K : Set H) := ⟨d,centralizer_le_normalizer _ (hD d.property)⟩
    have hh : (⟨f (k,d),hn k d⟩ : normalizer (K : Set H)) = inclusion K.le_normalizer k * dn :=
      Subtype.ext (hmul k d)
    rw [hh,map_mul,(quotient_eq_one_iff K dn).mpr (hD d.property),mul_one]
    rfl
  apply le_antisymm
  · rintro _ ⟨k,⟨⟨k',d⟩,hkd,hk⟩,rfl⟩
    change k' = k at hk
    subst k
    exact ⟨⟨f (k',d),hn k' d⟩,hkd,he k' d⟩
  · rintro _ ⟨v,hv,rfl⟩
    have hm : (v:H) ∈ (V.comap f).map f := by rw [himage]; exact hv
    obtain ⟨⟨k,d⟩,hkd,hv'⟩ := hm
    refine ⟨k,⟨(k,d),hkd,rfl⟩,?_⟩
    rw [← he k d]
    congr 1
    exact Subtype.ext hv'

end Subgroup.NormalizerAction
