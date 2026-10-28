module
public import Theory.GroupTheory.PrimeResidualIntersection
public import CFSG.Quasithin.Chapter15.Section01.CaseI.ComponentData
/-!
# The Case-I residual intersection

Set K=C_M(Z₁), N=C_M(V), and H=M∩M_c∩C_G(Z₁). The actual module
normalization makes N normal in K. The marked local Sylow subgroup lies
in H, while M=⟨K,T⟩ and T≤M_c force H to be proper in K.
The marked source-row calculation that O²(K/N) has prime order then
identifies the embedded residual of H with that of N.

This leaf proves the literal residual identity in original 15.1.18(2).
The original marked-row Sylow and prime-order calculations, and the earlier
C_M(V)≤M_c containment, remain explicit input facts supplied by their source
owners. The component-data wrapper retains precisely Z₁, G₁ and S from the
actual Case-I datum; no new component or module is selected.

Source: Aschbacher–Smith 15.1.16--18, printed p.1092.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section01
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
/-- Module normalization supplies the normal kernel of the marked quotient. -/
theorem caseI_module_centralizer_normal {M V Z1 : Subgroup G}
    (hMV : M ≤ normalizer (V : Set G)) :
    ((M ⊓ centralizer (V : Set G)).subgroupOf
      (M ⊓ centralizer (Z1 : Set G))).Normal := by
  have hMN : M ≤ normalizer ((M ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
    (le_inf M.le_normalizer (hMV.trans (normalizer_le_normalizer_centralizer V))).trans
      inf_normalizer_le_normalizer_inf
  exact normal_subgroupOf_of_le_normalizer (inf_le_left.trans hMN)

/-- The literal residual identity in source 15.1.18(2), with its marked
Sylow and prime-order quotient geometry retained explicitly. -/
theorem caseI_residual_intersection
    (T : Sylow 2 G) (M Mc V Z1 : Subgroup G)
    (hMV : M ≤ normalizer (V : Set G)) (hZV : Z1 ≤ V)
    (hNMc : M ⊓ centralizer (V : Set G) ≤ Mc)
    (hTMc : (T : Subgroup G) ≤ Mc) (hMnot : ¬ M ≤ Mc)
    (hgen : M = (M ⊓ centralizer (Z1 : Set G)) ⊔ (T : Subgroup G))
    (hSyl : ∃ P : Sylow 2 (M ⊓ centralizer (Z1 : Set G) : Subgroup G),
      (P : Subgroup (M ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ centralizer (Z1 : Set G)).subtype =
          (T : Subgroup G) ⊓ centralizer (Z1 : Set G))
    (hprime : letI := caseI_module_centralizer_normal (Z1 := Z1) hMV
      (Nat.card (pResidual 2 ((M ⊓ centralizer (Z1 : Set G) : Subgroup G) ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ centralizer (Z1 : Set G))))).Prime) :
    (pResidual 2 (M ⊓ Mc ⊓ centralizer (Z1 : Set G) : Subgroup G)).map
        (M ⊓ Mc ⊓ centralizer (Z1 : Set G)).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype := by
  let K := M ⊓ centralizer (Z1 : Set G)
  let N := M ⊓ centralizer (V : Set G)
  let H := M ⊓ Mc ⊓ centralizer (Z1 : Set G)
  let : (N.subgroupOf K).Normal := caseI_module_centralizer_normal hMV
  have hNK : N ≤ K := inf_le_inf_left M (centralizer_le hZV)
  have hNH : N ≤ H := le_inf (le_inf inf_le_left hNMc) (hNK.trans inf_le_right)
  have hHK : H ≤ K := le_inf (inf_le_left.trans inf_le_left) inf_le_right
  have hKM : ¬ K ≤ Mc := by
    intro hk
    apply hMnot
    rw [hgen]
    exact sup_le hk hTMc
  have hHKne : H ≠ K := by
    intro he
    apply hKM
    rw [←he]
    exact inf_le_left.trans inf_le_right
  obtain ⟨P,hP⟩ := hSyl
  apply embedded_pResidual_intersection_of_prime_quotient_residual
    K N H hNK hNH hHK P ?_ hHKne hprime
  intro x hx
  have hxK : x ∈ K := map_subtype_le _ hx
  have hxT : x ∈ (T : Subgroup G) := (hP ▸ hx).1
  exact ⟨⟨hxK.1,hTMc hxT⟩,hxK.2⟩

namespace CaseIComponentData
variable {T : Sylow 2 G} {M Mc V : Subgroup G}
/-- Apply the residual identity to the original component datum and its
unchanged centralizer and Sylow subgroup. -/
theorem residual_intersection (d : CaseIComponentData T M Mc V)
    (hMV : M ≤ normalizer (V : Set G))
    (hNMc : M ⊓ centralizer (V : Set G) ≤ Mc)
    (hTMc : (T : Subgroup G) ≤ Mc) (hMnot : ¬ M ≤ Mc)
    (hSyl : ∃ P : Sylow 2 (M ⊓ d.G1 : Subgroup G),
      (P : Subgroup (M ⊓ d.G1 : Subgroup G)).map (M ⊓ d.G1).subtype = d.S)
    (hprime : letI : ((M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ d.G1)).Normal :=
        caseI_module_centralizer_normal (Z1 := d.Z1) hMV
      (Nat.card (pResidual 2 ((M ⊓ d.G1 : Subgroup G) ⧸
        (M ⊓ centralizer (V : Set G)).subgroupOf (M ⊓ d.G1)))).Prime) :
    (pResidual 2 (M ⊓ Mc ⊓ d.G1 : Subgroup G)).map (M ⊓ Mc ⊓ d.G1).subtype =
      (pResidual 2 (M ⊓ centralizer (V : Set G) : Subgroup G)).map
        (M ⊓ centralizer (V : Set G)).subtype :=
  caseI_residual_intersection T M Mc V d.Z1 hMV (d.Z1_le_fixed.trans inf_le_left)
    hNMc hTMc hMnot d.M_eq_centralizer_sup_sylow hSyl hprime
end CaseIComponentData
end CFSG.Quasithin.Chapter15.Section01
