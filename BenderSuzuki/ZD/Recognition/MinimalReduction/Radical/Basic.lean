module

public import BenderSuzuki.ZD.Recognition.MinimalReduction.LocalBasic
public import Theory.GroupTheory.SylowCentralSolvableNormal

/-!
# Central subgroups in the ZD radical reduction

The center lies in the distinguished subgroup, but contains neither a
distinguished involution nor an involution that is a product of two of them.
In particular a central involution cannot translate the distinguished set
to itself. Once the odd core is trivial, any nontrivial solvable normal
subgroup contains a central subgroup of order two.

Source: GLS, Volume 4, Chapter 2, Lemma 4.5, printed pp. 34–35
(PDF pp. 51–52). The odd-core and central-extension lifting arguments
are separate obligations; these reductions do not assert Lemma 4.5.
-/

namespace BenderSuzuki.ZD
open Theory.GroupTheory PFAppendixIII
variable {G : Type*} [Group G] {Z : Set G} {M : Subgroup G}

/-- The center is contained in the distinguished subgroup. -/
public theorem center_le_of_productDisconnected (h : IsProductDisconnected Z M) :
    Subgroup.center G ≤ M := by
  obtain ⟨z, hz, hzM⟩ := h.nonempty
  exact (Subgroup.center_le_centralizer _).trans (h.centralizer_le hz hzM)

/-- A central element is never a distinguished involution. -/
public theorem not_mem_of_mem_center (h : IsProductDisconnected Z M)
    {v : G} (hv : v ∈ Subgroup.center G) : v ∉ Z := by
  intro hvZ
  apply h.proper
  apply top_unique
  intro g _
  exact mem_of_commute h hvZ (center_le_of_productDisconnected h hv)
    (Subgroup.mem_center_iff.mp hv g).symm

/-- A central involution is not a product of two distinguished involutions. -/
public theorem central_involution_ne_product (h : IsProductDisconnected Z M)
    {v : G} (hv : v ∈ Subgroup.center G) (hvinv : IsInvolution v)
    {x z : G} (hx : x ∈ Z) (hz : z ∈ Z) : x * z ≠ v := by
  intro he
  have hC := h.product_centralizer x hx z hz (he ▸ hvinv)
    (he ▸ center_le_of_productDisconnected h hv)
  apply h.proper
  apply top_unique
  intro g _
  apply hC
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  rw [he]
  exact Subgroup.mem_center_iff.mp hv g

/-- Multiplication by a central involution leaves the distinguished set. -/
public theorem central_involution_mul_not_mem (h : IsProductDisconnected Z M)
    {v : G} (hv : v ∈ Subgroup.center G) (hvinv : IsInvolution v)
    {z : G} (hz : z ∈ Z) : v * z ∉ Z := by
  intro hvz
  apply central_involution_ne_product h hv hvinv hvz hz
  have hzz : z * z = 1 := by simpa only [pow_two] using (h.involutions z hz).sq_eq_one
  rw [mul_assoc, hzz, mul_one]

/-- Reduction of a nontrivial solvable normal subgroup to a central subgroup
of order two, once the odd core has been eliminated. -/
public theorem central_two_subgroup_of_solvable_normal [Finite G]
    (hgen : Subgroup.closure Z = ⊤)
    (hcentral : ∀ z ∈ Z, ∃ S : Sylow 2 G, z ∈ S ∧ ∀ s : S, Commute z (s : G))
    (hodd : pPrimeCore 2 G = ⊥)
    (N : Subgroup G) [N.Normal] [Group.IsSolvable N] (hne : N ≠ ⊥) :
    ∃ A : Subgroup G, A.Normal ∧ A ≤ N ∧ A ≤ Subgroup.center G ∧ Nat.card A = 2 := by
  obtain ⟨v, hvN, hvc, hv⟩ :=
    exists_central_involution_of_solvable_normal_of_sylowCentral_generation hgen
      (fun z hz => let ⟨S, _, hS⟩ := hcentral z hz; ⟨S, hS⟩) hodd N hne
  have hAc : Subgroup.zpowers v ≤ Subgroup.center G := Subgroup.zpowers_le.mpr hvc
  refine ⟨Subgroup.zpowers v, ?_, Subgroup.zpowers_le.mpr hvN, hAc, ?_⟩
  · exact ⟨fun n hn g => by
      rw [Subgroup.mem_center_iff.mp (hAc hn) g, mul_inv_cancel_right]
      exact hn⟩
  · rw [Nat.card_zpowers, orderOf_eq_prime hv.sq_eq_one hv.ne_one]

end BenderSuzuki.ZD
