module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.RecognizedAction
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.HLocal
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal

/-!
# The complete cubic witnesses for 15.3.60–61(1)

The M-local construction supplies the symmetric factor, the marked
involutions and D_M. Its dihedral Sylow two-group remains Sylow in C_G(D_M)
because its central involution v satisfies C_G(v) ≤ M. The recognized
H-action constructs D_H and its centralizer's Sylow two-group of order 16.
The orders 8 and 16 separate the two cubic conjugacy classes.

The separating involution swaps the genuine natural and dual summands of
U/Z. The coset calculation and cubic lifting therefore give an ambient
conjugate of D_H centralized by that same involution. Sylow conjugacy in
C_G(z) and C_G(v) gives both required involution nonfusion conclusions.

`source_cubic_witnesses` constructs every field of `Witnesses` from the
listed earlier source conclusions. These retain the actual orthogonal
geometry, the equivariant P/V decomposition with s = 1, all four clauses of
15.3.59, and the extraspecial/natural-dual recognition of 15.3.58. They are
the authorized earlier-theorem boundary, to be supplied by the Fusion
assembly; no conclusion of 15.3.60–61(1) occurs among the inputs.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
the setup and statements of 15.3.60 and 15.3.61(1), printed p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
variable {G : Type*} [Group G]

open scoped Pointwise in
/-- The common source witnesses in 15.3.60 and 15.3.61(1), including the
actual local products, Sylow embeddings and all three nonfusion conclusions. -/
def Witnesses (T : Sylow 2 G) (M : Subgroup G)
    (d : NaturalOrthogonalAction M (localModule T M)) (i : OrthogonalPlaneIndex) : Prop :=
    let Z := centralInvolutions T
    let V := localModule T M
    let V1 := d.plane i
    let ZS := fixedPlane V (planeStabilizer T V1)
    let H := centralizerH Z
    let U := closureU Z ZS
    ∃ (PM3 : Sylow 3 (M ⊓ centralizer (V1 : Set G) : Subgroup G))
      (PH : Sylow 3 H) (J : Subgroup G) (_ : J ≃* Equiv.Perm (Fin 4))
      (z v t : G),
      let DM := MLocal.planeCubic M V1 PM3
      let DH := (PH : Subgroup H).map H.subtype
      ∃ (P2 : Subgroup G) (PM : Sylow 2 (centralizer (DM : Set G)))
        (SH : Sylow 2 (centralizer ((PH : Subgroup H) : Set H))) (R : Subgroup G)
        (Pz : Sylow 3 (centralizer ({z} : Set G)))
        (Pv : Sylow 3 (centralizer ({v} : Set G))),
      Nat.card (ZS ⊓ V1 : Subgroup G) = 2 ∧
      orderOf z = 2 ∧ orderOf v = 2 ∧ zpowers z = Z ∧ zpowers v = ZS ⊓ V1 ∧
      centralizer ({v} : Set G) ≤ M ∧
      Nat.card DM = 3 ∧ Nat.card DH = 3 ∧ Nat.card PH = 3 ∧
      DM ≤ M ∧ J ≤ M ∧ Disjoint DM J ∧ DM ≤ centralizer (J : Set G) ∧
      M ⊓ centralizer (DM : Set G) = DM ⊔ J ∧
      V1 = Stellmacher.twoCoreAmbient J ∧
      t ∈ (T : Subgroup G) ⊓ J ∧ orderOf t = 2 ∧ t ∉ V1 ∧
      Nat.card (fixedPlane V (zpowers t)) = 8 ∧
      t ∉ U ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ∧
      t ∉ (U : Set G) * ((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) ∧
      DM ≤ centralizer ({t} : Set G) ∧
      P2 ≤ M ⊓ centralizer (DM : Set G) ∧ P2 ≤ (T : Subgroup G) ∧
      Nat.card P2 = 8 ∧ IsPGroup 2 P2 ∧
      ¬ 2 ∣ P2.relIndex (M ⊓ centralizer (DM : Set G)) ∧
      (center P2).map P2.subtype = zpowers v ∧ Nonempty (P2 ≃* DihedralGroup 4) ∧
      (PM : Subgroup (centralizer (DM : Set G))).map
        (centralizer (DM : Set G)).subtype = P2 ∧ Nat.card PM = 8 ∧
      Nat.card (centralizer ((PH : Subgroup H) : Set H)) = 48 ∧ Nat.card SH = 16 ∧
      R = ((SH : Subgroup _).map (centralizer ((PH : Subgroup H) : Set H)).subtype).map
        H.subtype ∧ IsPGroup 2 R ∧ Nat.card R = 16 ∧ R ≤ centralizer (DH : Set G) ∧
      (Pz : Subgroup (centralizer ({z} : Set G))).map
        (centralizer ({z} : Set G)).subtype = DH ∧
      (Pv : Subgroup (centralizer ({v} : Set G))).map
        (centralizer ({v} : Set G)).subtype = DM ∧
      (∃ g : G, DH.map (MulAut.conj g).toMonoidHom ≤ centralizer ({t} : Set G)) ∧
      ¬ SubgroupConjugate DM DH ∧ ¬ IsConj t z ∧ ¬ IsConj t v


/-- Construct the complete cubic configuration and prove 15.3.60–61(1)
from the actual earlier local conclusions. The four clauses of 15.3.59
are explicit inputs (the core equality is in `recognition`). The only
swap premise is precisely 15.3.58(3), on the literal U/Z action.
No local cubic centralizer, involution witness, or nonfusion is assumed. -/
theorem source_cubic_witnesses [Finite G] (T : Sylow 2 G) (M : Subgroup G)
    (hTM : (T : Subgroup G) ≤ M) (d : NaturalOrthogonalAction M (localModule T M))
    (i : OrthogonalPlaneIndex) (g : G) :
    let Z := centralInvolutions T
    let V := localModule T M
    let H := centralizerH Z
    let Y := residualY M H
    let V1 := d.plane i
    let ZS := fixedPlane V (planeStabilizer T V1)
    let U := closureU Z ZS
    let I := pairI Z ZS g
    let P := pairP Z ZS g
    let TK := residualSylow T Z
    ∀ (_hg : g ∈ Y) (_hmoving : ¬ rightConjugate Z g ≤ V ⊓ U)
      (hUT : U ≤ T) (hTH : (T : Subgroup G) ≤ H)
      (_hMY : M ≤ normalizer (Y : Set G))
      (_hCY : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
      (hI : I = Y ⊔ U) (hcenter : V = (center P).map P.subtype)
      (S : Sylow 2 I) (_hS : (S : Subgroup I).map I.subtype = TK)
      (_hidx : TK.relIndex T = 2) (_hM : M = Y ⊔ (T : Subgroup G)),
    let hIM : I ≤ M := hI.le.trans (sup_le (show Y ≤ M from map_subtype_le _) (hUT.trans hTM))
    letI := MLocal.Structure.normal_lower_of_center hcenter
    letI := denominator_normal ((ZS_le_closureU Z ZS).trans (hUT.trans hTH))
    ∀ (_r : MLocal.Structure.NaturalQuotientPair d I P hIM
          (MLocal.Structure.pairI_normalizes_pairP Z ZS g))
      (_hUelementary : IsElementaryAbelian 2 (d.image U))
      (_hUcard : Nat.card (d.image U) = 4)
      (_hUother : d.image U ≠ d.image (planeStabilizer T V1))
      (_hcontrol : centralizer (fixedPlane V1 (planeStabilizer T V1) : Set G) ≤ M)
      (recognition : HLocal.Recognition Z ZS)
      (_hswap : ∀ t : H, (t : G) ∈ (T : Subgroup G) →
        (t : G) ∉ U ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) →
        HLocal.Swaps Z ZS recognition t),
    Witnesses T M d i := by
  intro Z V H Y V1 ZS U I P TK hg hmoving hUT hTH hMY hCY hI hcenter
    S hS hidx hM hIM r hUelementary hUcard hUother hcontrol recognition hswap
  let := MLocal.Structure.normal_lower_of_center hcenter
  let := denominator_normal ((ZS_le_closureU Z ZS).trans (hUT.trans hTH))
  obtain ⟨PM3, J, e, z, v, t, P2, Pv, hmark, hz, hv, hzgen, hvgen,
      hvc, hDM, hDMM, hJM, hdisj, hcomm, hprod, hcore, ht, htorder, htout,
      htfix, htnot, htnotproduct, hDt, hP2, hP2T, hP2card, hP2group,
      hP2idx, hP2center, hP2dihedral, hPv⟩ :=
    MLocal.source_local_witnesses T M hTM d i g hg hmoving hUT hTH hMY hCY hI
      hcenter recognition.core_eq S hS hidx hM r hUelementary hUcard hUother hcontrol
  let DM := MLocal.planeCubic M V1 PM3
  let PH : Sylow 3 H := Classical.choice inferInstance
  let DH := (PH : Subgroup H).map H.subtype
  have hPH : Nat.card PH = 3 := HLocal.sylow_three_card Z ZS recognition PH
  have hDH : Nat.card DH = 3 := by
    rw [card_map_of_injective H.subtype_injective]
    exact hPH
  obtain ⟨Pz, hPz⟩ := sylow_of_marked_generator Z z hzgen PH
  obtain ⟨SH, hSH, R, hRimage, hR, hRcard, hRDH⟩ :=
    HLocal.sylow_centralizer Z ZS recognition PH
  obtain ⟨PM, hPMimage⟩ := centralizer_sylow_of_center_involution M DM P2 v hv
    hP2group (hP2.trans inf_le_right) hP2idx hP2center hvc
  have hPM : Nat.card PM = 8 := by
    rw [← hP2card, ← hPMimage, card_map_of_injective (centralizer (DM : Set G)).subtype_injective]
  let tH : H := ⟨t, hTH ht.1⟩
  have ht2 : (tH : G) ^ 2 = 1 := by
    change t ^ 2 = 1
    rw [← htorder]
    exact pow_orderOf_eq_one t
  have htH : ∃ a : G, DH.map (MulAut.conj a).toMonoidHom ≤
      centralizer ({t} : Set G) :=
    recognized_centralizes_conjugate Z ZS recognition tH ht2 (hswap tH ht.1 htnot) PH
  have hnf := nonfusion_of_local_centralizers DM DH R t z v PM hPM hR hRcard hRDH
    Pz hPz Pv hPv hDM hDH hDt htH
  exact ⟨PM3, PH, J, e, z, v, t, P2, PM, SH, R, Pz, Pv,
    hmark, hz, hv, hzgen, hvgen, hvc, hDM, hDH, hPH, hDMM, hJM, hdisj, hcomm,
    hprod, hcore, ht, htorder, htout, htfix, htnot, htnotproduct, hDt,
    hP2, hP2T, hP2card, hP2group, hP2idx, hP2center, hP2dihedral, hPMimage, hPM,
    HLocal.centralizer_card Z ZS recognition PH, hSH, hRimage, hR, hRcard, hRDH,
    hPz, hPv, htH, hnf⟩

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic
