module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.BinaryRadical
public import Theory.Mathieu.M22.Properties.HexadPointwise
public import Theory.GroupAction.PerfectCentralQuotient
public import Theory.Frattini.BinarySquares

/-!
# Frattini elimination for the binary M₂₂ ambient core

Write Q = O₂(M) and I = L ∩ M. The preceding actual-source result puts Q
inside S, so Q normalizes L and I. Hence [I,Q] lies in the hexad radical V,
which is central elementary in Q. Every square in Q therefore fixes I
pointwise. A hexad pointwise fixer of the perfect binary cover is trivial:
its induced automorphism of M₂₂ is inner by pointwise Sylow fixation, and
the full hexad centralizer is trivial. Thus Φ(Q) centralizes L.

The literal Φ(Q) is normalized by the full selected T. Uniqueness of M
would then put L inside M unless Φ(Q) is trivial. Consequently the original
O₂(M) is elementary abelian. Neither full-S kernel invariance nor the final
binary-cover exclusion is assumed or asserted.

Source: Aschbacher--Smith 2.3.7–2.3.9, pp.523–526; the square argument is
the central elementary displacement argument of C.1.13(a), p.124.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers M22Local Sporadic.Mathieu.M22CentralCover
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {L M : Subgroup G} {z : G}

private theorem binary_hexad_fixer [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* M22) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (R : Sylow 2 L) (hRI : (R : Subgroup L) ≤ hexadPreimage e B)
    (a : MulAut L) (ha : ∀ x ∈ hexadPreimage e B, a x = x) : a = 1 := by
  apply MulAut.centralQuotientAction_injective e
  rw [map_one]
  apply m22_automorphism_eq_one_of_fixes_hexad hB
    (R.mapSurjective (projection_surjective e))
  · rintro _ ⟨x,hx,rfl⟩
    exact hRI hx
  · intro y hy
    obtain ⟨x,rfl⟩ := projection_surjective e y
    change MulAut.centralQuotientAction e a (e (QuotientGroup.mk' (center L) x)) = _
    rw [MulAut.centralQuotientAction_apply,ha x hy]
    rfl

omit [Finite G] in
private theorem projection_quotient_eq {t u : L}
    (ht : IsConjugationProjection L z t) (hu : IsConjugationProjection L z u) :
    QuotientGroup.mk' (center L) t = QuotientGroup.mk' (center L) u := by
  apply QuotientGroup.eq.mpr
  apply mem_center_iff.mpr
  intro x
  have he : t * x * t⁻¹ = u * x * u⁻¹ := Subtype.ext ((ht x).symm.trans (hu x))
  calc
    x * (t⁻¹ * u) = t⁻¹ * (t * x * t⁻¹) * u := by group
    _ = t⁻¹ * (u * x * u⁻¹) * u := by rw [he]
    _ = (t⁻¹ * u) * x := by group

omit [Finite G] in
private theorem square_centralizes_of_displacements (Q I V : Subgroup G)
    (hV : V ≤ centralizer (Q : Set G)) (hpow : ∀ v ∈ V, v ^ 2 = 1)
    (hdisp : ∀ q ∈ Q, ∀ i ∈ I, i * q * i⁻¹ * q⁻¹ ∈ V)
    {q : G} (hq : q ∈ Q) : q ^ 2 ∈ centralizer (I : Set G) := by
  intro i hi
  let v := i * q * i⁻¹ * q⁻¹
  have hv : v ∈ V := hdisp q hq i hi
  have hvq : Commute v q := (mem_centralizer_iff.mp (hV hv) q hq).symm
  have he : i * q * i⁻¹ = v * q := by dsimp [v]; group
  have hc : i * q ^ 2 * i⁻¹ = q ^ 2 := by
    calc
      i * q ^ 2 * i⁻¹ = (i * q * i⁻¹) ^ 2 := map_pow (MulAut.conj i) q 2
      _ = (v * q) ^ 2 := by rw [he]
      _ = v ^ 2 * q ^ 2 := hvq.mul_pow 2
      _ = q ^ 2 := by rw [hpow v hv,one_mul]
  exact mul_inv_eq_iff_eq_mul.mp hc

variable {C : GroupClass} {H : Subgroup G} {S : Sylow 2 H}

/-- Uniqueness above T eliminates the literal ambient core Frattini subgroup. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_ambient_frattini_eq_bot
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) : frattini (twoCore M) = ⊥ := by
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  let := h.quasisimple
  have hk : pCore 2 L ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
  have hZp : IsPGroup 2 (center L) := IsPGroup.of_card (n := 1) (by simpa using hZ)
  obtain ⟨t,ht,hto,htn,hB,hVc⟩ := c.mathieuTwentyTwo_binary_hexad_radical_le_center_twoCore hG sourceC d hc
  obtain ⟨u,hu,_,_,_,_,_,hjoin⟩ := c.mathieuTwentyTwo_binary_hexad_join_le hG sourceC d hc
  have hproj : projection e u = projection e t := congrArg e (projection_quotient_eq hu ht)
  let B := m22FixedPoints (projection e t)
  let I := (hexadPreimage e B).map L.subtype
  let V := (hexadRadical e B).map L.subtype
  let Q := twoCore M
  have hIM : I ≤ M := by
    have hh := (show (hexadPreimage e (m22FixedPoints (projection e u))).map L.subtype ≤
      (hexadPreimage e (m22FixedPoints (projection e u))).map L.subtype ⊔
        (S : Subgroup H).map H.subtype from le_sup_left).trans hjoin
    simpa only [hproj] using hh
  have hIMeq : I = L ⊓ M := by
    have hle : hexadPreimage e B ≤ M.subgroupOf L := fun x hx => hIM (mem_map_of_mem L.subtype hx)
    have hmax : IsCoatom (hexadPreimage e B) :=
      isCoatom_comap_of_surjective (projection_surjective e) (m22_hexad_stabilizer_isCoatom B hB)
    have hp : M.subgroupOf L ≠ ⊤ := fun hn => h.outside (subgroupOf_eq_top.mp hn)
    have he := (hmax.le_iff_eq hp).mp hle
    change (hexadPreimage e B).map L.subtype = _
    rw [← he,subgroupOf_map_subtype,inf_comm]
  have hQS : Q ≤ (S : Subgroup H).map H.subtype :=
    c.mathieuTwentyTwo_binary_ambient_core_le_sylow hG sourceC d hc
  have hQL : Q ≤ normalizer (L : Set G) :=
    hQS.trans ((map_subtype_le _).trans (h.mathieuTwentyTwo_normalized hG.quasithin d.quotientIso hk))
  have hQI : Q ≤ normalizer (I : Set G) := by
    rw [hIMeq]
    exact (le_inf hQL ((pCoreIn_le 2 M).trans M.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hIQ : I ≤ normalizer (Q : Set G) := hIM.trans (le_normalizer_twoCore M)
  have hpQ : IsPGroup 2 Q := pCore_isPGroup.map M.subtype
  have hcore : I.pCoreIn 2 = V := by
    change ((hexadPreimage e B).map L.subtype).pCoreIn 2 = V
    rw [← map_pCoreIn_of_injective 2 _ L.subtype L.subtype_injective]
    exact congrArg (Subgroup.map L.subtype) (hexadRadical_eq_twoCore e hZp hB).symm
  have hinter : Q ⊓ I ≤ V := by
    rw [← hcore]
    exact le_pCoreIn_of_normalizes (hpQ.to_le inf_le_left) inf_le_right
      ((le_inf hIQ I.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hcomm : ⁅I,Q⁆ ≤ V := (le_inf
    (le_normalizer_iff_commutator_le_right.mp hIQ)
    (le_normalizer_iff_commutator_le_left.mp hQI)).trans hinter
  have hVQ : V ≤ centralizer (Q : Set G) := by
    intro v hv
    obtain ⟨vM,hvM,rfl⟩ := hVc hv
    obtain ⟨vQ,hvQ,hve⟩ := hvM
    change (vQ : M) = vM at hve
    intro q hq
    obtain ⟨qM,hqM,rfl⟩ := hq
    have he := congrArg (fun x : pCore 2 M => ((x : M) : G))
      (mem_center_iff.mp hvQ ⟨qM,hqM⟩)
    change (qM : G) * ((vQ : M) : G) = ((vQ : M) : G) * (qM : G) at he
    change (qM : G) * (vM : G) = (vM : G) * (qM : G)
    simpa only [hve] using he
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := by
    rintro _ ⟨v,hv,rfl⟩
    let := hexadRadical_elementary e hZ hB
    simpa only [← map_pow,map_one] using congrArg L.subtype (elemPow_eq_one_of_isElementaryAbelian v hv)
  obtain ⟨_,_,_,_,_,_,_,R,hR,_,_⟩ :=
    BinaryAmbient.source_square_projection c hG structural115Input sourceC d hc
  have hRI : (R : Subgroup L) ≤ hexadPreimage e B := by
    intro x hx
    have hxM := h.sylow_le (hR ▸ hx)
    have hxI : (x : G) ∈ I := hIMeq.symm ▸ ⟨x.property,hxM⟩
    exact (mem_map_iff_mem L.subtype_injective).mp hxI
  have hsq : ∀ q ∈ Q, q ^ 2 ∈ centralizer (L : Set G) := by
    intro q hq
    have hqi := square_centralizes_of_displacements Q I V hVQ hV2
      (fun x hx y hy => hcomm (commutator_mem_commutator hy hx)) hq
    let a := L.normalizerMonoidHom ⟨q ^ 2,(normalizer (L : Set G)).pow_mem (hQL hq) 2⟩
    have ha : a = 1 := binary_hexad_fixer e hB R hRI a (by
      intro x hx
      apply Subtype.ext
      change q ^ 2 * (x : G) * (q ^ 2)⁻¹ = (x : G)
      rw [← mem_centralizer_iff.mp hqi x (mem_map_of_mem L.subtype hx),mul_inv_cancel_right])
    intro x hx
    have he := DFunLike.congr_fun ha ⟨x,hx⟩
    exact (mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val he)).symm
  let F := (frattini Q).map Q.subtype
  have hFL : F ≤ centralizer (L : Set G) := by
    apply map_le_iff_le_comap.mpr
    rw [hpQ.frattini_eq_closure_squares]
    apply (closure_le _).mpr
    rintro _ ⟨q,rfl⟩
    exact hsq q q.property
  by_contra hF
  have hFne : F ≠ ⊥ := fun hb => hF ((map_eq_bot_iff_of_injective _ Q.subtype_injective).mp hb)
  have hTN : (c.T : Subgroup G) ≤ normalizer (F : Set G) :=
    c.sylow_le.trans ((le_normalizer_twoCore M).trans
      (normalizer_le_normalizer_characteristic_image Q (frattini Q)))
  apply h.centralTwoSubgroup_not_normalized_by_sylow c.T c.sylow_le c.unique
    (c.T.subtype c.sylow_le) F hFne (hpQ.to_subgroup _ |>.map Q.subtype)
    (le_centralizer_iff.mp hFL)
  simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le c.sylow_le] using hTN

/-- The actual ambient two-core is elementary abelian in the binary residue. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_ambient_core_elementary
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) : IsElementaryAbelian 2 (twoCore M) := by
  let : Fact (IsPGroup 2 (twoCore M)) := ⟨pCore_isPGroup.map M.subtype⟩
  exact (frattini_eq_bot_iff_isElementaryAbelian (p := 2)).mp
    (c.mathieuTwentyTwo_binary_ambient_frattini_eq_bot hG sourceC d hc)

end CFSG.Quasithin.Chapter2.ComponentRefinement
