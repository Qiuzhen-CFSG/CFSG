module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.BinaryCoreAction
public import Theory.GroupTheory.MinimalNormalPCore
public import Theory.GroupTheory.AbelianSupplementIntersection
public import Theory.GroupTheory.SylowNormalCenterIntersection

/-!
# A genuine minimal normal module over the binary M₂₂ hexad

The selected Sylow center is cyclic. Every nontrivial elementary normal
subgroup of M inside O₂(M) therefore contains its unique central involution,
the original z. In the literal binary hexad model the commutators of this
nonconstant projection generate the augmentation radical V. Thus a minimal
normal W ≤ O₂(M) contains both z and V. The proved ambient-core action then
gives W = V C_W(L), without removing either the centralizer factor or the
possible outer action of the original Sylow group.

Minimality is stated for actual M-normal subgroups, so it supplies the
irreducibility of the original conjugation module; no classification or
recognition conclusion is assumed. This is a reduction for the remaining
binary-cover branch of Aschbacher--Smith 2.3.9(7), pp.525–526, using the
explicit I.2.2(6) hexad, p.412.
-/

public section
namespace CFSG.Quasithin.Chapter2.ComponentRefinement
open Subgroup Theory.GroupTheory Sporadic.Mathieu
open ChapterI.Section02.ExceptionalCovers M22Local Sporadic.Mathieu.M22CentralCover
open BinaryPermutation.SixCoreExtension
variable {G : Type*} [Group G] [Finite G] {L M : Subgroup G} {z : G}

private theorem radical_le_of_projected_normal_element
    (e : (L ⧸ center L) ≃* M22) (hZ : Nat.card (center L) = 2)
    [Group.IsPerfect L] (t : L) (hto : orderOf t = 2) (htn : t ∉ center L)
    (ht : IsConjugationProjection L z t)
    (hIM : (hexadPreimage e (m22FixedPoints (projection e t))).map L.subtype ≤ M)
    (N : Subgroup M) [N.Normal] (hz : z ∈ N.map M.subtype) :
    (hexadRadical e (m22FixedPoints (projection e t))).map L.subtype ≤ N.map M.subtype := by
  let B := m22FixedPoints (projection e t)
  obtain ⟨hB,htU,_⟩ := centralizer_le_fixedHexad e t hto htn
  obtain ⟨d⟩ := M22Local.Binary.exists_hexadRecognition_of_perfect e hZ hB
  let I := hexadPreimage e B
  let U := hexadRadical e B
  let f : I →* M := {
    toFun x := ⟨(x : L),hIM (mem_map_of_mem L.subtype x.property)⟩
    map_one' := rfl
    map_mul' _ _ := rfl }
  let K := N.comap f
  let Nm := K.map d.modelEquiv.toMonoidHom
  let : Nm.Normal := (inferInstance : K.Normal).map _ d.modelEquiv.surjective
  let r : U := ⟨t,htU⟩
  let v : V := (d.radicalEquiv r).toAdd
  have hv : BinaryPermutation.coreToNatural (Fin 6) v ≠ 0 :=
    fun he => htn ((d.center_iff r).mpr he)
  have hdis : ∀ a : Model, a * vector (Multiplicative.ofAdd v) * a⁻¹ *
      (vector (Multiplicative.ofAdd v))⁻¹ ∈ Nm := by
    intro a
    obtain ⟨y,rfl⟩ := d.modelEquiv.surjective a
    let ti : I := Subgroup.inclusion (hexadRadical_le e B) r
    have hti : d.modelEquiv ti = vector (Multiplicative.ofAdd v) := d.modelEquiv_radical r
    rw [← hti, ← map_inv, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    apply mem_map_of_mem
    change f (y * ti * y⁻¹ * ti⁻¹) ∈ N
    obtain ⟨zM,hzM,hzval⟩ := hz
    change (zM : G) = z at hzval
    have he : f (y * ti * y⁻¹ * ti⁻¹) = f y * zM * (f y)⁻¹ * zM⁻¹ := by
      apply Subtype.ext
      change (y : L).val * (t : G) * (y : L).val⁻¹ * (t : G)⁻¹ = _
      change _ = (y : L).val * (zM : G) * (y : L).val⁻¹ * (zM : G)⁻¹
      rw [hzval]
      have hp := ht (y : L)⁻¹
      simp only [Subgroup.coe_inv,Subgroup.coe_mul] at hp
      calc
        (y : L).val * (t : G) * (y : L).val⁻¹ * (t : G)⁻¹ =
          (y : L).val * ((t : G) * (y : L).val⁻¹ * (t : G)⁻¹) := by group
        _ = (y : L).val * (z * (y : L).val⁻¹ * z⁻¹) := by rw [← hp]
        _ = _ := by group
    rw [he]
    exact N.mul_mem ((inferInstance : N.Normal).conj_mem _ hzM _) (N.inv_mem hzM)
  have hle := normal_vector_range_of_commutators Nm v hv hdis
  rintro x ⟨u,hu,rfl⟩
  let r' : U := ⟨u,hu⟩
  have hx := hle (show vector (d.radicalEquiv r') ∈ vector.range from ⟨_,rfl⟩)
  rw [← d.modelEquiv_radical r', mem_map_equiv] at hx
  simp only [d.modelEquiv.symm_apply_apply] at hx
  exact mem_map_of_mem M.subtype hx

private theorem central_involution_mem_normal_core
    (T : Sylow 2 G) (hTM : (T : Subgroup G) ≤ M)
    (hz : z ∈ (center (T : Subgroup G)).map (T : Subgroup G).subtype)
    (hzo : orderOf z = 2) (hcyc : IsCyclic (center (T : Subgroup G)))
    (W : Subgroup M) [W.Normal] (hW : W ≠ ⊥) (hWQ : W ≤ pCore 2 M)
    [IsElementaryAbelian 2 W] : z ∈ W.map M.subtype := by
  let P := T.subtype hTM
  have hp : IsPGroup 2 W := pCore_isPGroup.of_injective
    (Subgroup.inclusion hWQ) (Subgroup.inclusion_injective hWQ)
  have hd : 2 ∣ Nat.card W := by
    rcases hp.card_eq_or_dvd with hcard | hcard
    · exact (hW (Subgroup.card_eq_one.mp hcard)).elim
    · exact hcard
  obtain ⟨w,hwZ,hwne,hwW⟩ := P.exists_ne_one_mem_center_of_normal W hd
  let wT : T := ⟨((w : M) : G), by
    have hh := w.property
    change ((w : M) : G) ∈ (T : Subgroup G) at hh
    exact hh⟩
  have hwTZ : wT ∈ center (T : Subgroup G) := by
    apply mem_center_iff.mpr
    intro x
    let xP : P := ⟨⟨x,hTM x.property⟩,by change (x : G) ∈ (T : Subgroup G); exact x.property⟩
    exact Subtype.ext (congrArg (fun a : P => ((a : M) : G)) (mem_center_iff.mp hwZ xP))
  have hwo : orderOf wT = 2 := by
    apply orderOf_eq_prime
    · apply Subtype.ext
      exact congrArg (fun a : M => (a : G))
        (elemPow_eq_one_of_isElementaryAbelian (w : M) hwW)
    · intro he
      have heG : ((w : M) : G) = 1 := congrArg (fun x : T => (x : G)) he
      exact hwne (Subtype.ext (Subtype.ext heG))
  obtain ⟨zt,hzt,hze⟩ := hz
  change (zt : G) = z at hze
  have hzto : orderOf zt = 2 := by rw [← orderOf_coe zt,hze,hzo]
  let : IsCyclic (center (T : Subgroup G)) := hcyc
  have he : (⟨wT,hwTZ⟩ : center (T : Subgroup G)) = ⟨zt,hzt⟩ :=
    IsCyclic.eq_of_orderOf_eq_two
      ((orderOf_coe (⟨wT,hwTZ⟩ : center (T : Subgroup G))).symm.trans hwo)
      ((orderOf_coe (⟨zt,hzt⟩ : center (T : Subgroup G))).symm.trans hzto)
  have hev : ((w : M) : G) = z :=
    (congrArg (fun a : center (T : Subgroup G) => ((a : T) : G)) he).trans hze
  exact hev ▸ mem_map_of_mem M.subtype hwW

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


variable {C : GroupClass} {H : Subgroup G} {S : Sylow 2 H}

/-- The actual ambient core has a minimal normal subgroup containing both
its distinguished involution and the entire binary hexad radical. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_minimal_normal_core
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    let h := c.localSetup hG structural115Input sourceC
    let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      let B := m22FixedPoints (projection e t)
      B ∈ m22Blocks ∧ ∃ W : Subgroup M,
        W.Normal ∧ W ≠ ⊥ ∧ W ≤ pCore 2 M ∧ IsElementaryAbelian 2 W ∧
        (∀ U : Subgroup M, U.Normal → U ≤ W → U = ⊥ ∨ U = W) ∧
        z ∈ W.map M.subtype ∧
        (hexadRadical e B).map L.subtype ≤ W.map M.subtype := by
  dsimp only
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  let := h.quasisimple
  obtain ⟨t,ht,hto,htn,hB,_,_,hjoin⟩ :=
    c.mathieuTwentyTwo_binary_hexad_join_le hG sourceC d hc
  let B := m22FixedPoints (projection e t)
  have hIM : (hexadPreimage e B).map L.subtype ≤ M :=
    (show (hexadPreimage e B).map L.subtype ≤
      (hexadPreimage e B).map L.subtype ⊔ (S : Subgroup H).map H.subtype
      from le_sup_left).trans hjoin
  have hQT : twoCore M ≤ (c.T : Subgroup G) := by
    simpa only [twoCore_eq_pCoreIn,Sylow.coe_subtype,map_subgroupOf_eq_of_le c.sylow_le]
      using pCoreIn_le_sylow M (c.T.subtype c.sylow_le)
  have hzC : z ∈ centralizer (c.T : Set G) := by
    obtain ⟨a,ha,he⟩ := c.mem_center
    intro x hx
    have hh := congrArg Subtype.val (mem_center_iff.mp ha ⟨x,hx⟩)
    change x * (a : G) = (a : G) * x at hh
    change (a : G) = z at he
    simpa only [he] using hh
  have hzQ : z ∈ twoCore M := h.overgroup_even
    ⟨h.sylow_le h.mem_sylow,centralizer_le hQT hzC⟩
  have hQne : pCore 2 M ≠ ⊥ := by
    intro hbot
    change z ∈ (pCore 2 M).map M.subtype at hzQ
    rw [hbot,Subgroup.map_bot,mem_bot] at hzQ
    have := c.involution
    rw [hzQ,orderOf_one] at this
    omega
  obtain ⟨W,hWn,hWne,hWQ,hWe,hWmin⟩ := exists_minimal_normal_le_pCore hQne
  let : W.Normal := hWn
  let : IsElementaryAbelian 2 W := hWe
  have hzW := central_involution_mem_normal_core c.T c.sylow_le c.mem_center c.involution
    (c.mathieuTwentyTwo_ambient_center_isCyclic hG sourceC d.quotientIso) W hWne hWQ
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
  exact ⟨t,ht,hto,htn,hB,W,hWn,hWne,hWQ,hWe,hWmin,hzW,
    radical_le_of_projected_normal_element e hZ t hto htn ht hIM W hzW⟩

/-- The minimal normal binary module retains the exact hexad action and its
fixed supplement; this is inherited from the proved full-core decomposition. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_minimal_core_decomposition
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    let h := c.localSetup hG structural115Input sourceC
    let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      let B := m22FixedPoints (projection e t)
      B ∈ m22Blocks ∧ ∃ W : Subgroup M,
        W.Normal ∧ W ≠ ⊥ ∧ W ≤ pCore 2 M ∧ IsElementaryAbelian 2 W ∧
        (∀ U : Subgroup M, U.Normal → U ≤ W → U = ⊥ ∨ U = W) ∧
        z ∈ W.map M.subtype ∧
        W.map M.subtype = (hexadRadical e B).map L.subtype ⊔
          (W.map M.subtype ⊓ centralizer (L : Set G)) := by
  dsimp only
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  obtain ⟨t,ht,hto,htn,hB,W,hWn,hWne,hWQ,hWe,hWmin,hzW,hVW⟩ :=
    c.mathieuTwentyTwo_binary_minimal_normal_core hG sourceC d hc
  obtain ⟨u,hu,_,_,_,hQeq⟩ := c.mathieuTwentyTwo_binary_ambient_core_decomposition hG sourceC d hc
  have he : projection e u = projection e t := congrArg e (projection_quotient_eq hu ht)
  change twoCore M = (hexadRadical e (m22FixedPoints (projection e u))).map L.subtype ⊔ _ at hQeq
  rw [he] at hQeq
  let V := (hexadRadical e (m22FixedPoints (projection e t))).map L.subtype
  let Wg := W.map M.subtype
  let Q := twoCore M
  have hWg : Wg ≤ Q := map_mono hWQ
  have hVQ : V ≤ Q := hVW.trans hWg
  let : IsElementaryAbelian 2 Q := c.mathieuTwentyTwo_binary_ambient_core_elementary hG sourceC d hc
  have hsplit := eq_inf_sup_inf_of_abelian_supplement Q Wg
    (Q ⊓ centralizer (L : Set G)) V hWg inf_le_left hVQ
    (by rw [sup_comm,← hQeq]; exact hWg)
    (by rw [inf_eq_left.mpr hVW]; exact le_sup_left)
  have hw : Wg ⊓ V = V := inf_eq_right.mpr hVW
  have hfix : Wg ⊓ (Q ⊓ centralizer (L : Set G)) =
      Wg ⊓ centralizer (L : Set G) := by
    rw [← inf_assoc,inf_eq_left.mpr hWg]
  rw [hw,hfix,sup_comm] at hsplit
  exact ⟨t,ht,hto,htn,hB,W,hWn,hWne,hWQ,hWe,hWmin,hzW,hsplit⟩

end CFSG.Quasithin.Chapter2.ComponentRefinement
