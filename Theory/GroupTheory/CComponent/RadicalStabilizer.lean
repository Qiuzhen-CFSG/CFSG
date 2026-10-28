module
public import Theory.GroupTheory.ComponentRadicalStabilizer
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.PCoreImage
public import Theory.GroupTheory.QuotientIntersection
/-!
# Radical stabilizers of constrained-component images

Pass through the actual quotient by O₂(G). A C-component with quasisimple
two-core quotient gives an ordinary component there. Radical saturation
descends because the kernel lies in the original radical. The component
normalizer pulls back exactly, and prime cores commute with the quotient.
Thus the ordinary stabilizer equation lifts to the original component and
radical, without assuming that the radical normalizes the component.

Source: Aschbacher, Math. Z. 177 (1981), 8.2(5); Aschbacher–Smith C.2.2(3),
printed p.144, in the quasisimple-quotient case used by C.2.4(2).
-/
public section
open Subgroup Theory.GroupTheory
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem IsCComponent.stabilizer_radical
    {L Q : Subgroup G} (hL : L.IsCComponent)
    [IsQuasisimple (L ⧸ pCore 2 L)] (hq : IsPRadical 2 Q) :
    let R := Q ⊓ normalizer (L : Set G)
    ((L ⊔ R) ⊓ normalizer (R : Set G)).pCoreIn 2 = R := by
  let : Group.IsNilpotent (pCore 2 G) := (pCore_isPGroup (p := 2) (G := G)).isNilpotent
  let q := QuotientGroup.mk' (pCore 2 G)
  have hqs : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkQ : q.ker ≤ Q := by
    rw [QuotientGroup.ker_mk']
    exact pCore_le_of_pCore_normalizer_le Q hq.isPGroup hq.2.le
  have hs : ∀ P : Subgroup G, IsPGroup 2 P →
      normalizer (Q : Set G) ≤ normalizer (P : Set G) → P ≤ Q :=
    fun P hp hn => le_of_normalizer_le_normalizer_of_pCore_normalizer_le Q P
      hq.isPGroup hp hq.2.le hn
  have hsn : (normalizer (Q.map q : Set (G ⧸ pCore 2 G))).comap q =
      normalizer (Q : Set G) := by
    rw [comap_normalizer_eq_of_surjective _ hqs, comap_map_eq_self hkQ]
  have hsl : (normalizer (L.map q : Set (G ⧸ pCore 2 G))).comap q =
      normalizer (L : Set G) := normalizer_cComponent_quotient hL _
  have hsat : ∀ P : Subgroup (G ⧸ pCore 2 G), IsPGroup 2 P →
      normalizer (Q.map q : Set (G ⧸ pCore 2 G)) ≤ normalizer (P : Set (G ⧸ pCore 2 G)) →
      P ≤ Q.map q := by
    intro P hp hn
    have hh : P.comap q ≤ Q := hs _ (hp.comap_of_ker_isPGroup q hk) (by
      rw [← hsn, ← comap_normalizer_eq_of_surjective _ hqs]
      exact comap_mono hn)
    have hm := map_mono (f := q) hh
    rwa [map_comap_eq_self_of_surjective hqs] at hm
  have hLq : Theory.GroupTheory.IsComponent (G ⧸ pCore 2 G) (L.map q) :=
    ⟨hL.subnormal.map hqs,
      Theory.GroupTheory.IsQuasisimple.of_mulEquiv (cComponentTwoCoreQuotientEquiv hL)⟩
  let R := Q ⊓ normalizer (L : Set G)
  have hkR : q.ker ≤ R := le_inf hkQ (by
    rw [← hsl]
    intro x hx
    change q x ∈ normalizer (L.map q : Set (G ⧸ pCore 2 G))
    rw [MonoidHom.mem_ker.mp hx]
    exact one_mem _)
  have hRm : R.map q = Q.map q ⊓ normalizer (L.map q : Set (G ⧸ pCore 2 G)) := by
    rw [show R = Q ⊓ normalizer (L : Set G) from rfl, ← hsl,
      map_inf_of_ker_le q Q _ (by
        rw [hsl]; exact hkR.trans inf_le_right),
      map_comap_eq_self_of_surjective hqs]
  have hRn : (normalizer (R : Set G)).map q = normalizer (R.map q : Set (G ⧸ pCore 2 G)) := by
    have hh : (normalizer (R.map q : Set (G ⧸ pCore 2 G))).comap q =
        normalizer (R : Set G) := by
      rw [comap_normalizer_eq_of_surjective _ hqs, comap_map_eq_self hkR]
    rw [← hh, map_comap_eq_self_of_surjective hqs]
  have hm : (((L ⊔ R) ⊓ normalizer (R : Set G)).pCoreIn 2).map q = R.map q := by
    rw [map_pCoreIn_of_ker_isPGroup q hk,
      map_inf_of_ker_le q (L ⊔ R) _ (hkR.trans R.le_normalizer),
      Subgroup.map_sup, hRn, hRm]
    exact hLq.stabilizer_radical_of_saturation (hq.isPGroup.map q) le_rfl hsat
  apply le_antisymm
  · have hh := map_le_iff_le_comap.mp hm.le
    rwa [comap_map_eq_self hkR] at hh
  · exact le_pCoreIn_of_normalizes (hq.isPGroup.to_le inf_le_left)
      (le_inf le_sup_right R.le_normalizer) inf_le_right
end Subgroup
