module

public import Stellmacher.BaumannNormalClosureSupplement
public import Stellmacher.SectionsOneToFourDefs

/-!
# The Baumann closure is a Thompson closure supplement

Assume the Thompson and Baumann subgroups of S have equal images under a
homomorphism whose kernel is C_G(V), and O₂(G) = C_S(V). Then the normal
closure of the Baumann subgroup is the join of that subgroup and the normal
closure of J(S). This supplies L = EB in Stellmacher (2.3), Journal of
Algebra 190 (1997), p.20, from the image equality furnished by (2.2).

The elementary Thompson subgroup lies in the Baumann subgroup since it
centralizes its own central omega subgroup. For b in B, image equality
chooses j in J with the same image. Thus b j⁻¹ lies in S and in the kernel,
hence in O₂(G). The generic Baumann normal-closure supplement theorem now
applies. Neither surjectivity of the homomorphism nor the full Section 2
standing hypotheses are required for this transfer.
-/

namespace Stellmacher.SectionTwo

/-- Equal quotient images give the unbarred supplement L = E ∨ B. -/
public theorem normalClosure_baumann_eq_thompson_sup_of_image_eq
    {G X : Type*} [Group G] [Finite G] [Group X]
    (S : Sylow 2 G) (B : Subgroup G)
    (hB : B = (S : Subgroup G) ⊓ Subgroup.centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup G)) : Set G))
    (q : G →* X) (hker : q.ker = cSubgroup S)
    (hcore : pCore 2 G = (S : Subgroup G) ⊓
      Subgroup.centralizer (vSubgroup S : Set G))
    (himage : (elementaryAbelianMaxJ (S : Subgroup G)).map q = B.map q) :
    Subgroup.normalClosure (B : Set G) =
      Subgroup.normalClosure (elementaryAbelianMaxJ (S : Subgroup G) : Set G) ⊔ B := by
  let J := elementaryAbelianMaxJ (S : Subgroup G)
  let E := Subgroup.normalClosure (J : Set G)
  have hJS : J ≤ (S : Subgroup G) := sSup_le fun _ hA => hA.1
  have hJB : J ≤ B := by
    rw [hB]
    refine le_inf hJS ?_
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨wJ, hwJ, rfl⟩ := hw
    obtain ⟨wZ, _, rfl⟩ := hwJ
    exact congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp wZ.property) ⟨j, hj⟩).symm
  have hEL : E ≤ Subgroup.normalClosure (B : Set G) :=
    Subgroup.normalClosure_mono hJB
  have hNS : pCore 2 G ≤ (S : Subgroup G) := hcore ▸ inf_le_left
  have hBS : B ≤ (S : Subgroup G) := hB ▸ inf_le_left
  have hBEN : B ≤ E ⊔ pCore 2 G := by
    intro b hb
    have hqb : q b ∈ J.map q := by
      rw [show J.map q = B.map q from himage]
      exact Subgroup.mem_map_of_mem q hb
    obtain ⟨j, hj, heq⟩ := hqb
    have hbj : b * j⁻¹ ∈ pCore 2 G := by
      rw [hcore]
      refine ⟨S.toSubgroup.mul_mem (hBS hb) (S.toSubgroup.inv_mem (hJS hj)), ?_⟩
      have hk : b * j⁻¹ ∈ q.ker := by
        change q (b * j⁻¹) = 1
        rw [map_mul, map_inv, heq, mul_inv_cancel]
      rw [hker] at hk
      exact hk
    have hproduct : (b * j⁻¹) * j ∈ E ⊔ pCore 2 G :=
      (E ⊔ pCore 2 G).mul_mem
        ((show pCore 2 G ≤ E ⊔ pCore 2 G from le_sup_right) hbj)
        ((show E ≤ E ⊔ pCore 2 G from le_sup_left) (Subgroup.le_normalClosure hj))
    simpa only [inv_mul_cancel_right] using hproduct
  exact normalClosure_baumann_eq_sup S B E (pCore 2 G) hB hNS hEL hBEN

end Stellmacher.SectionTwo
