module
public import Theory.GroupTheory.PResidual.SylowSupplement
/-!
# A residual image and the original Sylow recover a subgroup preimage

If a surjection has p-group kernel, that kernel lies in the original Sylow
p-subgroup. A subgroup mapping onto the full p-residual of a target subgroup
therefore generates its entire preimage with that Sylow, provided the Sylow
image is contained in the target. This is the exact lifting used for K0T in
Aschbacher–Smith, 13.7.6(1), printed p.940.
-/
public section
namespace Subgroup
variable {G B : Type*} [Group G] [Finite G] [Group B]
/-- The residual image and the original Sylow recover the whole target preimage. -/
theorem sup_sylow_eq_comap_of_residual_image
    (p : ℕ) [Fact p.Prime] (q : G →* B) (hq : Function.Surjective q)
    (hk : IsPGroup p q.ker) (T : Sylow p G) (J : Subgroup G) (P : Subgroup B)
    (hT : (T : Subgroup G).map q ≤ P)
    (hJ : J.map q = (pResidual p P).map P.subtype) :
    J ⊔ (T : Subgroup G) = P.comap q := by
  let : Finite B := Finite.of_surjective q hq
  let S := T.mapSurjective hq
  have hSP : (S : Subgroup B) ≤ P := hT
  let R := S.subtype hSP
  have hs := congrArg (map P.subtype) (pResidual_sup_sylow_eq_top R)
  rw [map_sup,← MonoidHom.range_eq_map,range_subtype] at hs
  have hr : (R : Subgroup P).map P.subtype = (T : Subgroup G).map q := by
    change (S.subtype hSP : Subgroup P).map P.subtype = _
    rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hSP]
    rfl
  rw [hr] at hs
  have hker : q.ker ≤ J ⊔ (T : Subgroup G) :=
    (hk.le_sylow_of_normal T).trans le_sup_right
  calc
    J ⊔ (T : Subgroup G) = ((J ⊔ (T : Subgroup G)).map q).comap q := by
      rw [comap_map_eq,sup_eq_left.mpr hker]
    _ = P.comap q := by rw [map_sup,hJ,hs]
end Subgroup
