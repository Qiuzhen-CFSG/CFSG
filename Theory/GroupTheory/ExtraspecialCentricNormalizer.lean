module

public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.NormalCentralQuotientAction
public import Theory.GroupTheory.CentricRadicalCoreComparison

/-!
# The faithful central quotient action of a centric extraspecial subgroup

A normal extraspecial two-subgroup with a centric Sylow intersection has
centralizer equal to its center once the ambient odd core is trivial.
Its center is also the whole ambient center. Innerness of automorphisms
trivial on the central quotient then identifies the full action kernel
with the original extraspecial subgroup.
-/

public noncomputable section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory

public theorem extraspecial_centric_central_quotient_kernel
    {H : Type*} [Group H] [Finite H] (S : Sylow 2 H)
    (P : Subgroup H) [P.Normal] [IsExtraspecial 2 P]
    (hodd : pPrimeCore 2 H=⊥)
    (hcent : (S : Subgroup H)⊓centralizer (P : Set H)≤P) :
    centralizer (P : Set H)=(center P).map P.subtype ∧
      (center P).map P.subtype=center H ∧
      (normalQuotientAction P (center P)).ker=P := by
  have hC : centralizer (P : Set H)≤P := by
    simpa only [hodd,bot_sup_eq] using AlperinGoldschmidt.normal_p_centralizer_le S P hcent
  have hCE : centralizer (P : Set H)=(center P).map P.subtype := by
    apply le_antisymm
    · intro x hx
      refine ⟨⟨x,hC hx⟩,?_,rfl⟩
      exact mem_center_iff.mpr (fun p => Subtype.ext (hx p.val p.property))
    · rintro x ⟨z,hz,rfl⟩ p hp
      exact congrArg Subtype.val (mem_center_iff.mp hz (⟨p,hp⟩:P))
  have hZ : (center P).map P.subtype≤center H := central_of_normal_card_two _ (by
    rw [card_map_of_injective P.subtype_injective,IsExtraspecial.center_order_p 2 P])
  refine ⟨hCE,le_antisymm hZ ((center_le_centralizer _).trans_eq hCE),?_⟩
  apply le_antisymm
  · intro x hx
    have ha : (MulAut.conjNormal x : MulAut P)∈(quotientAut (center P)).ker := by
      apply MulEquiv.ext
      intro q
      obtain ⟨p,rfl⟩ := QuotientGroup.mk'_surjective (center P) q
      have hxe : normalQuotientAction P (center P) x=1 := hx
      have hh := DFunLike.congr_fun hxe (QuotientGroup.mk' (center P) p)
      rw [normalQuotientAction_apply_mk] at hh
      rw [quotientAut_apply_mk]
      exact hh
    obtain ⟨r,hr⟩ := (IsExtraspecial.quotientAut_center_ker_eq_range_conj (p:=2)).le ha
    have hc : (r:H)⁻¹*x∈centralizer (P : Set H) := by
      intro p hp
      have he := congrArg (fun f : MulAut P => (f (⟨p,hp⟩:P) : H)) hr
      change (r:H)*p*(r:H)⁻¹=x*p*x⁻¹ at he
      calc
        p*((r:H)⁻¹*x) = (r:H)⁻¹*((r:H)*p*(r:H)⁻¹)*x := by group
        _ = (r:H)⁻¹*(x*p*x⁻¹)*x := by rw [he]
        _ = ((r:H)⁻¹*x)*p := by group
    have hh := P.mul_mem r.property (hC hc)
    simpa only [mul_inv_cancel_left] using hh
  · intro x hx
    rw [MonoidHom.mem_ker,normalQuotientAction_inner P (center P) (⟨x,hx⟩:P)]
    let : IsElementaryAbelian 2 (P⧸center P) := IsExtraspecial.quotient_elementary_abelian 2 P
    apply MulEquiv.ext
    intro q
    change _*q*_⁻¹=q
    rw [mul_comm _ q,mul_inv_cancel_right]

end Theory.GroupTheory
