module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.BinaryFrattini
public import Theory.Mathieu.M22.Properties.HexadNormalTwoAction
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Ambient

/-!
# The actual binary M₂₂ ambient core action

Let Q = O₂(M), let L be the selected binary M₂₂ component, and let V
be its literal hexad radical. Earlier source deductions give Q ≤ S and
V ≤ Z(Q). Passing conjugation through the actual central quotient of L,
the image of Q centralizes the native E₁₆ and is normalized by the inner
hexad. The full design-automorphism hexad calculation puts this image in
E₁₆. Perfectness of L then lifts each action to conjugation by an element
of V. Correcting by this element proves Q = V C_Q(L).

The centralizer factor is retained. This is an ambient-core deduction,
not a characteristicity assertion about S ∩ L or the final binary exclusion.
Source: Aschbacher--Smith I.2.2(6), p.412, and 2.3.9(7), pp.525–526.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers M22Local Sporadic.Mathieu.M22CentralCover
open M22ValueBound.Concrete
open scoped Pointwise
variable {G : Type*} [Group G] [Finite G] {L : Subgroup G}

private noncomputable def coverAction (e : (L ⧸ center L) ≃* M22) :
    normalizer (L : Set G) →* m22DesignAut :=
  designAutEquiv.symm.toMonoidHom.comp
    ((MulAut.centralQuotientAction e).comp L.normalizerMonoidHom)

omit [Finite G] in
private theorem coverAction_inner (e : (L ⧸ center L) ≃* M22) (x : L) :
    coverAction e ⟨x,L.le_normalizer x.property⟩ = inclusion (projection e x) := by
  apply designAutEquiv.injective
  change designAutEquiv (designAutEquiv.symm
    (MulAut.centralQuotientAction e (L.normalizerMonoidHom ⟨x,L.le_normalizer x.property⟩))) = _
  rw [designAutEquiv.apply_symm_apply,designAutEquiv_inclusion]
  have he : L.normalizerMonoidHom ⟨x,L.le_normalizer x.property⟩ = MulAut.conj x := by
    ext y
    rfl
  rw [he,MulAut.centralQuotientAction_conj]
  rfl

omit [Finite G] in
private theorem coverAction_apply (e : (L ⧸ center L) ≃* M22)
    (q : normalizer (L : Set G)) (x : L) :
    m22DesignAutToAut (coverAction e q) (projection e x) =
      projection e (L.normalizerMonoidHom q x) := by
  change designAutEquiv (designAutEquiv.symm
    (MulAut.centralQuotientAction e (L.normalizerMonoidHom q)))
      (e (QuotientGroup.mk' (center L) x)) = _
  rw [designAutEquiv.apply_symm_apply,MulAut.centralQuotientAction_apply]
  rfl

omit [Finite G] in
private theorem projection_quotient_eq {z : G} {t u : L}
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
private theorem cover_normal_two_action_inner [Group.IsPerfect L]
    (e : (L ⧸ center L) ≃* M22) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (Q : Subgroup G) (hp : IsPGroup 2 Q) (hQL : Q ≤ normalizer (L : Set G))
    (hIQ : (hexadPreimage e B).map L.subtype ≤ normalizer (Q : Set G))
    (hc : Q ≤ centralizer ((hexadRadical e B).map L.subtype : Set G)) :
    ∀ (q : G) (hq : q ∈ Q), ∃ v ∈ hexadRadical e B,
      L.normalizerMonoidHom ⟨q,hQL hq⟩ = MulAut.conj v := by
  let N := normalizer (L : Set G)
  let P := (Q.subgroupOf N).map (coverAction e)
  have hPn : (MulAction.stabilizer M22 B).map inclusion ≤ normalizer (P : Set m22DesignAut) := by
    rintro _ ⟨x,hx,rfl⟩
    obtain ⟨y,rfl⟩ := projection_surjective e x
    have hyn : (y : G) ∈ normalizer (Q : Set G) := hIQ (mem_map_of_mem L.subtype hx)
    have hym : (⟨(y : G),L.le_normalizer y.property⟩ : N) ∈ normalizer (Q.subgroupOf N : Set N) := by
      rw [← subgroupOf_normalizer_eq hQL]
      exact hyn
    have hh := (Q.subgroupOf N).le_normalizer_map (coverAction e) (mem_map_of_mem (coverAction e) hym)
    rwa [coverAction_inner] at hh
  have hPc : P ≤ centralizer ((m22HexadPointwiseKernel B).map inclusion : Set m22DesignAut) := by
    rintro _ ⟨q,hq,rfl⟩
    rintro _ ⟨v,hv,rfl⟩
    obtain ⟨x,rfl⟩ := projection_surjective e v
    have hfix : L.normalizerMonoidHom q x = x := by
      apply Subtype.ext
      change (q : G) * (x : G) * (q : G)⁻¹ = (x : G)
      have hh := mem_centralizer_iff.mp (hc hq) x (mem_map_of_mem L.subtype hv)
      change (x : G) * (q : G) = (q : G) * (x : G) at hh
      rw [← hh,mul_inv_cancel_right]
    have he := coverAction_apply e q x
    rw [hfix] at he
    have hcj : coverAction e q * inclusion (projection e x) * (coverAction e q)⁻¹ =
        inclusion (projection e x) := by
      apply Subtype.ext
      have hh := m22DesignAutToAut_apply_perm (coverAction e q) (projection e x)
      rw [he] at hh
      exact hh.symm
    exact (mul_inv_eq_iff_eq_mul.mp hcj).symm
  have hPK := M22OuterHexad.normal_two_fixer_le_kernel hB P (hp.comap_subtype.map _) hPc hPn
  intro q hq
  obtain ⟨v,hv,hvEq⟩ := hPK (mem_map_of_mem (coverAction e) (show
    (⟨q,hQL hq⟩ : N) ∈ Q.subgroupOf N from hq))
  obtain ⟨x,rfl⟩ := projection_surjective e v
  refine ⟨x,hv,?_⟩
  apply MulAut.centralQuotientAction_injective e
  rw [MulAut.centralQuotientAction_conj]
  have he := congrArg designAutEquiv hvEq
  rw [designAutEquiv_inclusion] at he
  change MulAut.conj (projection e x) =
    designAutEquiv (designAutEquiv.symm
      (MulAut.centralQuotientAction e (L.normalizerMonoidHom ⟨q,hQL hq⟩))) at he
  rw [designAutEquiv.apply_symm_apply] at he
  exact he.symm

variable {C : GroupClass} {H M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The original ambient core acts on L through its actual hexad radical.
The remaining factor is precisely its intersection with C_G(L). -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_ambient_core_decomposition
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    let h := c.localSetup hG structural115Input sourceC
    let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      let B := m22FixedPoints (projection e t)
      B ∈ m22Blocks ∧
      twoCore M = (hexadRadical e B).map L.subtype ⊔
        (twoCore M ⊓ centralizer (L : Set G)) := by
  dsimp only
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  let := h.quasisimple
  have hk : pCore 2 L ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
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
  have hQS : Q ≤ (S : Subgroup H).map H.subtype :=
    c.mathieuTwentyTwo_binary_ambient_core_le_sylow hG sourceC d hc
  have hQL : Q ≤ normalizer (L : Set G) :=
    hQS.trans ((map_subtype_le _).trans (h.mathieuTwentyTwo_normalized hG.quasithin d.quotientIso hk))
  have hVQ : V ≤ Q := hVc.trans (map_mono (map_subtype_le _))
  have hQV : Q ≤ centralizer (V : Set G) := by
    apply le_centralizer_iff.mp
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
  have hinner := cover_normal_two_action_inner e hB Q (pCore_isPGroup.map M.subtype)
    hQL (hIM.trans (le_normalizer_twoCore M)) hQV
  refine ⟨t,ht,hto,htn,hB,le_antisymm ?_ (sup_le hVQ inf_le_left)⟩
  intro q hq
  obtain ⟨v,hv,ha⟩ := hinner q hq
  have hvQ : (v : G) ∈ Q := hVQ (mem_map_of_mem L.subtype hv)
  have hcq : (v : G)⁻¹ * q ∈ centralizer (L : Set G) := by
    intro x hx
    have he := congrArg Subtype.val (DFunLike.congr_fun ha ⟨x,hx⟩)
    change q * x * q⁻¹ = (v : G) * x * (v : G)⁻¹ at he
    calc
      x * ((v : G)⁻¹ * q) = (v : G)⁻¹ * ((v : G) * x * (v : G)⁻¹) * q := by group
      _ = (v : G)⁻¹ * (q * x * q⁻¹) * q := by rw [← he]
      _ = ((v : G)⁻¹ * q) * x := by group
  have hmem : (v : G) * ((v : G)⁻¹ * q) ∈ V ⊔ (Q ⊓ centralizer (L : Set G)) :=
    mul_mem ((show V ≤ V ⊔ (Q ⊓ centralizer (L : Set G)) from le_sup_left)
      (mem_map_of_mem L.subtype hv))
      ((show Q ⊓ centralizer (L : Set G) ≤ V ⊔ (Q ⊓ centralizer (L : Set G))
        from le_sup_right) ⟨Q.mul_mem (Q.inv_mem hvQ) hq,hcq⟩)
  simpa only [mul_inv_cancel_left] using hmem

end CFSG.Quasithin.Chapter2.ComponentRefinement
