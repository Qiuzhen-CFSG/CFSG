module
public import CFSG.Quasithin.Chapter2.Section01To03.ComponentRefinement.SurvivingIntersections.NativeSource.BinaryHexad
public import Theory.Representation.BinaryPermutation.SixCoreExtension.NormalSubgroups

/-!
# The binary hexad radical inside the ambient two-core

The actual inner projection of z is a nonconstant vector in the hexad's
augmentation core. Since z lies in Z(O₂(M)), all its commutators with the
hexad lie there. The six-coordinate normal-subgroup calculation forces the
entire radical into this same center. In particular the original cover kernel
is centralized by O₂(M). The exact Γ₀ normalizer identity then puts O₂(M)
inside the original S.

This preserves the full S and the literal component and ambient two-cores.
It does not assert that S ∩ L is characteristic in S or that the binary
cover has been excluded. Source: Aschbacher--Smith 2.3.7–2.3.9, pp.523–526,
and I.2.2(6), pp.410,412.
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

variable {C : GroupClass} {H : Subgroup G} {S : Sylow 2 H}

/-- The full binary hexad radical lies in the center of the original ambient two-core. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_hexad_radical_le_center_twoCore
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    let h := c.localSetup hG structural115Input sourceC
    let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
    ∃ t : L, IsConjugationProjection L z t ∧ orderOf t = 2 ∧ t ∉ center L ∧
      let B := m22FixedPoints (projection e t)
      B ∈ m22Blocks ∧
      (hexadRadical e B).map L.subtype ≤
        ((center (pCore 2 M)).map (pCore 2 M).subtype).map M.subtype := by
  dsimp only
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  let := h.quasisimple
  obtain ⟨t,ht,hto,htn,hB,_,_,hIM⟩ :=
    c.mathieuTwentyTwo_binary_hexad_join_le hG sourceC d hc
  have hZ : Nat.card (center L) = 2 := by
    simpa only [h.mathieuTwentyTwo_center_eq d.quotientIso] using hc
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
  let N := (center (pCore 2 M)).map (pCore 2 M).subtype
  have hzN : z ∈ N.map M.subtype := by
    obtain ⟨zM,hzM,hze⟩ := hzQ
    change (zM : G) = z at hze
    refine ⟨zM,?_,hze⟩
    refine ⟨⟨zM,hzM⟩,?_,rfl⟩
    apply mem_center_iff.mpr
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hh := mem_centralizer_iff.mp hzC (y : M) (hQT (mem_map_of_mem M.subtype y.property))
    change (y : M).val * z = z * (y : M).val at hh
    change (y : M).val * (zM : G) = (zM : G) * (y : M).val
    simpa only [← hze] using hh
  refine ⟨t,ht,hto,htn,hB,?_⟩
  exact radical_le_of_projected_normal_element e hZ t hto htn ht
    ((show (hexadPreimage e _).map L.subtype ≤
      (hexadPreimage e _).map L.subtype ⊔ (S : Subgroup H).map H.subtype from le_sup_left).trans hIM)
    N hzN

/-- In the binary residue the full ambient two-core is already in the
original S. Centrality of the cover kernel in O₂(M), together with Γ₀,
forces this containment; characteristicity of S ∩ L is not used. -/
theorem MathieuSourceSetup.mathieuTwentyTwo_binary_ambient_core_le_sylow
    (c : MathieuSourceSetup H L M S z) (hG : IsSimpleQTKE C G)
    (sourceC : LocalC129Input C G) (d : SporadicQuotientInput L z .m22)
    (hc : Nat.card (pCore 2 L) = 2) :
    twoCore M ≤ (S : Subgroup H).map H.subtype := by
  let h := c.localSetup hG structural115Input sourceC
  let e := h.mathieuTwentyTwo_centerQuotient d.quotientIso
  obtain ⟨t,_,_,_,_,hle⟩ := c.mathieuTwentyTwo_binary_hexad_radical_le_center_twoCore hG sourceC d hc
  have hk : pCore 2 L ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  have hKL : twoCore L ≤ ((center (pCore 2 M)).map (pCore 2 M).subtype).map M.subtype := by
    change (pCore 2 L).map L.subtype ≤ _
    rw [← h.mathieuTwentyTwo_center_eq d.quotientIso]
    exact (map_mono (center_le_hexadRadical e _)).trans hle
  have hKc : twoCore L ≤ centralizer (twoCore M : Set G) := by
    intro k hk
    obtain ⟨kM,hkM,rfl⟩ := hKL hk
    obtain ⟨kQ,hkQ,hke⟩ := hkM
    intro q hq
    obtain ⟨qM,hqM,rfl⟩ := hq
    have he := congrArg (fun x : pCore 2 M => ((x : M) : G))
      (mem_center_iff.mp hkQ ⟨qM,hqM⟩)
    change (kQ : M) = kM at hke
    change (qM : G) * (kM : G) = (kM : G) * (qM : G)
    change (qM : G) * ((kQ : M) : G) = ((kQ : M) : G) * (qM : G) at he
    simpa only [hke] using he
  have hQT : twoCore M ≤ (c.T : Subgroup G) := by
    simpa only [twoCore_eq_pCoreIn,Sylow.coe_subtype,map_subgroupOf_eq_of_le c.sylow_le]
      using pCoreIn_le_sylow M (c.T.subtype c.sylow_le)
  have hHN := (h.mathieuTwentyTwo_normalized hG.quasithin d.quotientIso hk).trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have he := c.normalizer_inf_T (twoCore L)
    (fun hb => hk ((map_eq_bot_iff_of_injective _ L.subtype_injective).mp hb))
    (pCore_isPGroup.map L.subtype) hHN
  rw [← he]
  exact le_inf hQT ((le_centralizer_iff.mp hKc).trans (Subgroup.centralizer_le_normalizer _))

end CFSG.Quasithin.Chapter2.ComponentRefinement
