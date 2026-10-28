module
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.GroupTheory.PResidual.SylowSupplement
public import Theory.GroupTheory.PCoreImage
/-!
# Odd subgroups above a normal alternating-five section

If a normal subgroup has two-core quotient A₅ and is supplemented by the
original Sylow two-subgroup, each proper overgroup of that Sylow is a
{2,3}-group. Its intersection with the normal section maps into the actual
A₅ Sylow normalizer, and the Sylow supplements this intersection. Odd
subgroups are consequently three-groups. All two-cores and intersections
are intrinsic to their original carriers.

Source application: Aschbacher–Smith 10.2.3, printed pp.745–746, the single
comparison K = O²(H). This direct bound bypasses the larger embedding's
geometry when the comparison itself has A₅ quotient.
-/

public noncomputable section
open Subgroup
open scoped Pointwise
namespace Theory.SpecificGroups.Alternating.FiveSylowMaximal
variable {G : Type*} [Group G] [Finite G]

private theorem marked_proper_overgroup_six
    (S : Sylow 2 G) (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤)
    (e : (G ⧸ pCore 2 G) ≃* alternatingGroup (Fin 5)) : IsPGroup 6 V := by
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 G))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hk : f.ker = pCore 2 G := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkV : f.ker ≤ V := by
    rw [hk]
    exact (pCore_isPGroup.le_sylow_of_normal S).trans hSV
  have hproper : V.map f ≠ ⊤ := by
    intro he
    apply hV
    have hh := congrArg (comap f) he
    rwa [comap_map_eq_self hkV,comap_top] at hh
  let R := S.mapSurjective hf
  have hn := overgroup_le_sylow_normalizer R (V.map f) (map_mono hSV) hproper
  have h6 : IsPGroup 6 (normalizer (R : Set (alternatingGroup (Fin 5)))) := by
    obtain ⟨i,hi⟩ := FiveBorelOvergroups.sylow_normalizer_eq_stabilizer R
    rw [hi]
    have hc : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) i) = 12 := by
      rw [Nat.card_eq_fintype_card]
      clear hi hn R S hf hk hkV hproper f e hSV hV V
      revert i
      decide +kernel
    exact IsPGroup.of_card_dvd_pow (n := 2) (by rw [hc]; decide)
  have hker : IsPGroup 6 f.ker := hk.symm ▸ pCore_isPGroup.mono (by decide : 2 ∣ 6)
  have hh := (h6.to_le hn).comap_of_ker_isPGroup f hker
  rwa [comap_map_eq_self hkV] at hh

/-- An A₅ normal section with a Sylow two-supplement has only two and
three in every proper overgroup of that Sylow. The full two-core is retained. -/
theorem normal_section_proper_overgroup_six
    (S : Sylow 2 G) (A : Subgroup G) [A.Normal]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤) : IsPGroup 6 V := by
  obtain ⟨R,hR⟩ := S.exists_subgroupOf_eq_of_normal A
  have hRV : (R : Subgroup A) ≤ V.subgroupOf A := by
    rw [hR]
    exact comap_mono hSV
  have hnV : V.subgroupOf A ≠ ⊤ := by
    intro ht
    exact hV (top_unique (hgen ▸ sup_le (subgroupOf_eq_top.mp ht) hSV))
  have h6 := marked_proper_overgroup_six R (V.subgroupOf A) hRV hnV e
  have hm : (V.subgroupOf A).map A.subtype = V ⊓ A := subgroupOf_map_subtype V A
  have hi : IsPGroup 6 (V ⊓ A : Subgroup G) := hm ▸ h6.map A.subtype
  have hn : (S : Subgroup G) ≤ normalizer ((V ⊓ A : Subgroup G) : Set G) :=
    (le_inf (hSV.trans V.le_normalizer) le_normalizer_of_normal).trans
      inf_normalizer_le_normalizer_inf
  have he : (V ⊓ A) ⊔ (S : Subgroup G) = V := by
    apply le_antisymm (sup_le inf_le_left hSV)
    intro v hv
    have hx : v ∈ (A : Set G) * ((S : Subgroup G) : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left A (S : Subgroup G) le_normalizer_of_normal,hgen]
      exact mem_top v
    obtain ⟨a,ha,s,hs,rfl⟩ := hx
    have hav : a ∈ V := by
      simpa only [mul_inv_cancel_right] using V.mul_mem hv (V.inv_mem (hSV hs))
    exact mul_mem_sup ⟨hav,ha⟩ hs
  rw [←he]
  exact hi.to_sup_of_normal_left' (S.isPGroup'.mono (by decide : 2 ∣ 6)) hn

/-- Odd subgroups of those proper Sylow overgroups are three-groups. -/
theorem normal_section_odd_subgroup_isThreeGroup
    (S : Sylow 2 G) (A : Subgroup G) [A.Normal]
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5))
    (hgen : A ⊔ (S : Subgroup G) = ⊤)
    (V B : Subgroup G) (hSV : (S : Subgroup G) ≤ V) (hV : V ≠ ⊤)
    (hBV : B ≤ V) (hodd : Odd (Nat.card B)) : IsPGroup 3 B := by
  have h6 := (normal_section_proper_overgroup_six S A e hgen V hSV hV).to_le hBV
  obtain ⟨n,hn⟩ := h6.exists_card_dvd_pow
  have hd : Nat.card B ∣ 2^n * 3^n := by
    simpa only [←mul_pow,show 2*3 = 6 by decide] using hn
  exact IsPGroup.of_card_dvd_pow ((hodd.coprime_two_right.pow_right n).dvd_of_dvd_mul_left hd)
end Theory.SpecificGroups.Alternating.FiveSylowMaximal
