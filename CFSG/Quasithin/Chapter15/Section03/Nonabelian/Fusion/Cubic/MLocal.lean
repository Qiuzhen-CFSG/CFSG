module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Marking
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.LocalSylow
public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal.Structure

/-!
# M-local witnesses for the cubic-centralizer argument

`source_local_witnesses` constructs the full M-local configuration in the
setup of 15.3.60. Its conclusion `LocalWitnesses` retains the actual generators
z and v, a Sylow three-subgroup of C_M(V₁) with ambient image D of order three,
and the internal product C_M(D) = D × J with J ≃ S₄ and V₁ = O₂(J).
It also constructs t in T ∩ J outside V₁ and U C_T(V), the local dihedral
Sylow two-group of order eight with center ⟨v⟩, and a Sylow three-subgroup
of C_G(v) with ambient image D.

The inputs are genuine earlier source conclusions: the prescribed natural
orthogonal action; the choice of g in 15.3.54; U ≤ T ≤ H; relative normality
of Y in M and C_Y(V) = O₂(Y); I = YU; V = Z(P); and the actual equivariant
two-constituent decomposition of P/V, specialized to s = 1. All four
15.3.59 clauses are retained: U = O₂(H), T_K Sylow in I, [T : T_K] = 2,
and M = YT. The earlier elementary-four U-image and centralizer control
C_G(C_{V₁}(S)) ≤ M complete the inputs. Here H = M_c = C_G(Z), as fixed
at the start of the nonabelian source branch. The normality of Y makes
the source joins YU and YT their respective group products.

The Structure calculation constructs J and arranges its Sylow subgroup in T.
The marked orthogonal action proves |Z_S ∩ V₁| = 2 and |Z| = 2, providing
z and v. The local three-part calculation then constructs the Sylow witness
in C_G(v). The symmetric factor supplies the dihedral group and t. Its actual
fixed hyperplane in V, together with the U-image calculation and the proved
product interpretation, excludes t from U C_T(V).

The older conditional helper `local_witnesses_of_symmetric_factor` is preserved;
its factor and action premises are discharged by the new source construction.
The earlier source inputs and final nonfusion assembly belong to the parent
Cubic task. No local centralizer, involution or nonfusion conclusion is assumed
by `source_local_witnesses`.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 15.3.53–55
on printed pp.1146–1147 and the setup of 15.3.60 on p.1150.
-/

@[expose] public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal
variable {G : Type*} [Group G] [Finite G] {M V : Subgroup G}

/-- Construct the remaining witnesses from a symmetric factor and its actual
action; the source derivation of these premises is a separate obligation. -/
theorem local_witnesses_of_symmetric_factor
    (d : NaturalOrthogonalAction M V) (T : Sylow 2 G) (i : OrthogonalPlaneIndex)
    (Z ZS : Subgroup G) (hZS : ZS = fixedPlane V (planeStabilizer T (d.plane i)))
    (hTH : (T : Subgroup G) ≤ centralizerH Z)
    (hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)))
    (P : Sylow 3 (M ⊓ centralizer (d.plane i : Set G) : Subgroup G))
    (J : Subgroup G) (e : J ≃* Equiv.Perm (Fin 4))
    (hd : Disjoint (planeCubic M (d.plane i) P) J)
    (hc : planeCubic M (d.plane i) P ≤ centralizer (J : Set G))
    (hprod : M ⊓ centralizer (planeCubic M (d.plane i) P : Set G) =
      planeCubic M (d.plane i) P ⊔ J)
    (hcore : d.plane i = Stellmacher.twoCoreAmbient J)
    (Q : Sylow 2 J) (hQT : factorSylow J Q ≤ (T : Subgroup G))
    (htrans : ∀ t ∈ J, orderOf t = 2 → t ∉ d.plane i →
      Nat.card (fixedPlane V (zpowers t)) = 8)
    (hUfixed : ∀ u ∈ closureU Z ZS, Nat.card (fixedPlane V (zpowers u)) ≠ 8)
    (v : G) (hv : orderOf v = 2) (hvgen : zpowers v = ZS ⊓ d.plane i)
    (hcontrol : centralizer ({v} : Set G) ≤ M) :
    ∃ (t : G) (P2 : Subgroup G) (Pv : Sylow 3 (centralizer ({v} : Set G))),
      t ∈ (T : Subgroup G) ⊓ J ∧ orderOf t = 2 ∧ t ∉ d.plane i ∧
      Nat.card (fixedPlane V (zpowers t)) = 8 ∧
      t ∉ closureU Z ZS ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ∧
      planeCubic M (d.plane i) P ≤ centralizer ({t} : Set G) ∧
      P2 ≤ M ⊓ centralizer (planeCubic M (d.plane i) P : Set G) ∧
      P2 ≤ (T : Subgroup G) ∧ Nat.card P2 = 8 ∧ IsPGroup 2 P2 ∧
      ¬ 2 ∣ P2.relIndex (M ⊓ centralizer (planeCubic M (d.plane i) P : Set G)) ∧
      (center P2).map P2.subtype = zpowers v ∧ Nonempty (P2 ≃* DihedralGroup 4) ∧
      Nat.card (planeCubic M (d.plane i) P) = 3 ∧
      (Pv : Subgroup (centralizer ({v} : Set G))).map
        (centralizer ({v} : Set G)).subtype = planeCubic M (d.plane i) P := by
  let _ := d.elementary_of_le (d.plane_le i)
  obtain ⟨f⟩ := factorSylow_dihedral J e Q
  obtain ⟨t, ht, htorder, htout⟩ :=
    dihedral_involution_outside_abelian (factorSylow J Q) (d.plane i) f
  have htJ : t ∈ J := factorSylow_le J Q ht
  have htfix := htrans t htJ htorder htout
  have hvmark : v ∈ fixedPlane V (planeStabilizer T (d.plane i)) ⊓ d.plane i := by
    have h := mem_zpowers v
    rwa [hvgen, hZS] at h
  have hvne : v ≠ 1 := by intro he; simp only [he, orderOf_one] at hv; omega
  obtain ⟨Pv, hPv⟩ := exists_sylow_involution_image d hcop i P v hvmark.2 hvne hcontrol
  have hcard := card_planeCubic d hcop i P
  have hP2 : factorSylow J Q ≤
      M ⊓ centralizer (planeCubic M (d.plane i) P : Set G) := by
    rw [hprod]
    exact (factorSylow_le J Q).trans le_sup_right
  refine ⟨t, factorSylow J Q, Pv, ⟨hQT ht, htJ⟩, htorder, htout, htfix,
    not_mem_source_product_of_fixed_card Z ZS V T hTH hUfixed t htfix,
    ?_, hP2, hQT, card_factorSylow J e Q, factorSylow_isPGroup J Q,
    factorSylow_local_index M _ J hcard e hd hc hprod Q,
    factorSylow_center J V (d.plane i) e T hcore Q hQT v hv hvmark,
    ⟨f⟩, hcard, hPv⟩
  intro x hx
  exact mem_centralizer_singleton_iff.mpr (hc hx t htJ).symm

open scoped Pointwise in
/-- The full conclusion of the M-local construction, including the actual
markings, symmetric factor, transvection and local Sylow groups. -/
def LocalWitnesses (T : Sylow 2 G) (M : Subgroup G)
    (d : NaturalOrthogonalAction M (localModule T M)) (i : OrthogonalPlaneIndex) : Prop :=
    let Z := centralInvolutions T
    let V := localModule T M
    let V1 := d.plane i
    let ZS := fixedPlane V (planeStabilizer T V1)
    let U := closureU Z ZS
    ∃ (PM3 : Sylow 3 (M ⊓ centralizer (V1 : Set G) : Subgroup G))
      (J : Subgroup G) (_ : J ≃* Equiv.Perm (Fin 4))
      (z v t : G) (P2 : Subgroup G) (Pv : Sylow 3 (centralizer ({v} : Set G))),
      let D := planeCubic M V1 PM3
      Nat.card (ZS ⊓ V1 : Subgroup G) = 2 ∧
      orderOf z = 2 ∧ orderOf v = 2 ∧ zpowers z = Z ∧ zpowers v = ZS ⊓ V1 ∧
      centralizer ({v} : Set G) ≤ M ∧
      Nat.card D = 3 ∧ D ≤ M ∧ J ≤ M ∧ Disjoint D J ∧
      D ≤ centralizer (J : Set G) ∧ M ⊓ centralizer (D : Set G) = D ⊔ J ∧
      V1 = Stellmacher.twoCoreAmbient J ∧
      t ∈ (T : Subgroup G) ⊓ J ∧ orderOf t = 2 ∧ t ∉ V1 ∧
      Nat.card (fixedPlane V (zpowers t)) = 8 ∧
      t ∉ U ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ∧
      t ∉ (U : Set G) * ((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) ∧
      D ≤ centralizer ({t} : Set G) ∧
      P2 ≤ M ⊓ centralizer (D : Set G) ∧ P2 ≤ (T : Subgroup G) ∧
      Nat.card P2 = 8 ∧ IsPGroup 2 P2 ∧
      ¬ 2 ∣ P2.relIndex (M ⊓ centralizer (D : Set G)) ∧
      (center P2).map P2.subtype = zpowers v ∧ Nonempty (P2 ≃* DihedralGroup 4) ∧
      (Pv : Subgroup (centralizer ({v} : Set G))).map
        (centralizer ({v} : Set G)).subtype = D

open scoped Pointwise in
/-- Construct all M-local cubic witnesses from genuine earlier source conclusions.
The quotient pair is the actual equivariant P/V decomposition with s = 1.
The four 15.3.59 clauses are retained, including U = O₂(H); no centralizer
splitting, local Sylow witness, or involution action conclusion is assumed. -/
theorem source_local_witnesses (T : Sylow 2 G) (M : Subgroup G)
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
      (hUT : U ≤ T) (_hTH : (T : Subgroup G) ≤ H)
      (_hMY : M ≤ normalizer (Y : Set G))
      (_hCY : Y ⊓ centralizer (V : Set G) = Stellmacher.twoCoreAmbient Y)
      (hI : I = Y ⊔ U) (hcenter : V = (center P).map P.subtype)
      (_hUcore : U = coreQ Z)
      (S : Sylow 2 I) (_hS : (S : Subgroup I).map I.subtype = TK)
      (_hidx : TK.relIndex T = 2) (_hM : M = Y ⊔ (T : Subgroup G)),
    let hIM : I ≤ M := hI.le.trans (sup_le (show Y ≤ M from map_subtype_le _) (hUT.trans hTM))
    letI := Structure.normal_lower_of_center hcenter
    ∀ (_r : Structure.NaturalQuotientPair d I P hIM (Structure.pairI_normalizes_pairP Z ZS g))
      (_hUelementary : IsElementaryAbelian 2 (d.image U))
      (_hUcard : Nat.card (d.image U) = 4)
      (_hUother : d.image U ≠ d.image (planeStabilizer T V1))
      (_hcontrol : centralizer (fixedPlane V1 (planeStabilizer T V1) : Set G) ≤ M),
    LocalWitnesses T M d i := by
  intro Z V H Y V1 ZS U I P TK hg hmoving hUT hTH hMY hCY hI hcenter _hUcore
    S hS hidx hM hIM r hUelementary hUcard hUother hcontrol
  let : (V.subgroupOf P).Normal := Structure.normal_lower_of_center hcenter
  obtain ⟨PM3, J, e, Q, hJM, hd, hc, hprod, hcore, hQT, htrans, hUfixed⟩ :=
    Structure.source_symmetric_factor T M hTM d i g hg hmoving hUT hTH hMY hCY
      hI hM hcenter S hS hidx r hUelementary hUcard hUother
  have hp := Structure.LocalKernel.action_kernel_isTwoGroup T hTM
    (show Y ≤ M from map_subtype_le _) hMY hM hCY d
  have hcop : Nat.Coprime 3 (Nat.card ((centralizer (V : Set G)).subgroupOf M)) := by
    rw [← d.ker_actor]
    obtain ⟨n, hn⟩ := hp.exists_card_eq
    rw [hn]
    exact (by decide : Nat.Coprime 3 2).pow_right n
  have hZ : Nat.card Z = 2 := by
    change Nat.card (centralInvolutions T) = 2
    rw [NaturalOrthogonalAction.centralInvolutions_eq_fixedPlane T hTM d,
      d.card_fixedPlane hTM]
    exact OrthogonalGeometry.sylow_fixedVectors_card (d.sylowImage T hTM)
  obtain ⟨z, v, hz, hv, hzgen, hvgen⟩ := source_marked_involutions d T hTM i Z hZ
  have hvc : centralizer ({v} : Set G) ≤ M := by
    rw [show centralizer ({v} : Set G) = centralizer (zpowers v : Set G) by
      rw [zpowers_eq_closure, centralizer_closure], hvgen, marked_intersection_eq_fixedPlane]
    exact hcontrol
  obtain ⟨t, P2, Pv, ht, htorder, htout, htfix, htnot, hDt, hP2, hP2T,
      hP2card, hP2group, hP2idx, hP2center, hP2dihedral, hDcard, hPv⟩ :=
    local_witnesses_of_symmetric_factor d T i Z ZS rfl hTH hcop PM3 J e hd hc
      hprod hcore Q hQT htrans hUfixed v hv hvgen hvc
  have htnotproduct : t ∉ (U : Set G) *
      ((T : Subgroup G) ⊓ centralizer (V : Set G) : Subgroup G) := by
    rw [← closureU_sup_centralizer_eq_product Z ZS V T hTH]
    exact htnot
  exact ⟨PM3, J, e, z, v, t, P2, Pv, card_marked_intersection d T hTM i,
    hz, hv, hzgen, hvgen, hvc, hDcard, planeCubic_le_M M V1 PM3,
    hJM, hd, hc, hprod, hcore, ht, htorder, htout, htfix, htnot, htnotproduct,
    hDt, hP2, hP2T, hP2card, hP2group, hP2idx, hP2center, hP2dihedral, hPv⟩


end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Fusion.Cubic.MLocal
