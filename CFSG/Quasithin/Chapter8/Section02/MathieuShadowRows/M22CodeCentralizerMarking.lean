module
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointPairing
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointCover
public import Theory.Representation.MathieuCodeRestriction.NormalizedShadowRows.CodeCentralizer
public import Theory.Representation.MathieuCodeRestriction.M22.SourceModules.Irreducibility

/-!
# Point centralizers in the selected M22 code marking

The original Sylow-fixed vector determines a hexad in the supplied whole-code
coordinates. Equivariance identifies its literal centralizer with the full
preimage of the hexad stabilizer, preserving the original homomorphism and
its entire kernel. Faithfulness of the native code identifies the centralizer
of the module in every original subgroup of L with its intersection with V.
These same coordinates supply the full original point pairing.

Source: Aschbacher--Smith H.13, H.16.4 and 8.2.11--12, printed pp.395,403,722,
refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode
open scoped IsMulCommutative Pointwise commutatorElement
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE ChapterH.Section13To16.M22Local.Hexad
variable {G : Type*} [Group G]

private theorem native_code_faithful : Function.Injective m22CodeRepresentation := by
  let : IsSimpleGroup M22 := m22_isSimpleGroup
  let : Nontrivial M22Code := Module.nontrivial_of_finrank_pos
    (by rw [finrank_m22Code]; decide : 0 < Module.finrank (ZMod 2) M22Code)
  rcases m22CodeRepresentation.normal_ker.eq_bot_or_eq_top with hk | hk
  · exact m22CodeRepresentation.ker_eq_bot_iff.mp hk
  · have he : m22CodeRepresentation = 1 := MonoidHom.ker_eq_top_iff.mp hk
    obtain ⟨u,hu⟩ := exists_ne (0 : M22Code)
    have hm : u ∈ m22CodeRepresentation.invariants := by intro g; rw [he]; rfl
    rw [m22Code_invariants_eq_bot,Submodule.mem_bot] at hm
    exact (hu hm).elim

variable (L V : Subgroup G) [IsElementaryAbelian 2 V]
    (hLN : L ≤ normalizer (V : Set G))
    (p : L →* M22) (hp : Function.Surjective p)
    (hk : p.ker = V.subgroupOf L)
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (he : ∀ l v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v) =
        m22CodeRepresentation (p l) (e v))

include hp he in
/-- The original Sylow-fixed point is a hexad vector in the supplied marking. -/
theorem m22_marking_central_hexad [Finite G]
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (z : V) (hzT : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ B : Finset (Fin 22), ∃ hB : B ∈ m22Blocks,
      e (Additive.ofMul z) = m22HexadVector hB := by
  obtain ⟨P,hP⟩ := (T.subtype (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from
    le_sup_right)).exists_map_subtype_eq_inf_of_normalizes
      (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) (sup_le L.le_normalizer hTL)
  have hPT : (P : Subgroup L).map L.subtype ≤ (T : Subgroup G) := by
    rw [hP]
    exact inf_le_left.trans (by
      rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le
        (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)])
  let S := P.mapSurjective hp
  have hfix : e (Additive.ofMul z) ∈ fixedSpace m22CodeRepresentation S := by
    intro b
    obtain ⟨l,hl,hb⟩ := b.property
    change m22CodeRepresentation b.val (e (Additive.ofMul z)) = e (Additive.ofMul z)
    rw [←hb,←he]
    apply congrArg e
    apply Additive.toMul.injective
    apply Subtype.ext
    change (l : G)*(z : G)*(l : G)⁻¹=(z : G)
    rw [hzT l (hPT (mem_map_of_mem L.subtype hl)),mul_inv_cancel_right]
  have hv : e (Additive.ofMul z) ≠ 0 := by
    intro hh
    exact hne (congrArg Additive.toMul (e.injective (hh.trans e.map_zero.symm)))
  exact NormalizedShadowRows.sylow_fixed_code_vector S _ hv hfix

include he in
/-- The full centralizer is the literal hexad preimage under the selected map. -/
theorem m22_marking_centralizer_mem_iff
    (z : V) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hzB : e (Additive.ofMul z) = m22HexadVector hB) (l : L) :
    p l ∈ MulAction.stabilizer M22 B ↔
      l.val ∈ centralizer ({(z : G)} : Set G) := by
  have hfix : m22CodeRepresentation (p l) (e (Additive.ofMul z)) = e (Additive.ofMul z) ↔
      l.val ∈ centralizer ({(z : G)} : Set G) := by
    constructor
    · intro hh
      have hv := congrArg (fun v : Additive V => (v.toMul : G))
        (e.injective ((he l (Additive.ofMul z)).trans hh))
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hv)
    · intro hh
      have hv : automizerRepresentation V
          (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) (Additive.ofMul z) =
            Additive.ofMul z := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change l.val*z.val*l.val⁻¹=z.val
        exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hh)
      exact (he l (Additive.ofMul z)).symm.trans (congrArg e hv)
  rw [hzB] at hfix
  exact (NormalizedShadowRows.code_hexad_vector_fixed_iff hB (p l)).symm.trans hfix

include hp hk he in
/-- The selected marking covers the entire original centralizer, with the
full original module kernel, exact restriction and full equivariance. -/
theorem m22_marking_centralizer_cover_of_hexad
    (z : V) {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (hzB : e (Additive.ofMul z) = m22HexadVector hB) :
    ∃ c : (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) →* MulAction.stabilizer M22 B,
      Function.Surjective c ∧
      (∀ l, (c l).val = p ⟨l,l.property.1⟩) ∧
      c.ker = V.subgroupOf (L ⊓ centralizer ({(z : G)} : Set G)) ∧
      (L ⊓ centralizer ({(z : G)} : Set G)).subgroupOf L =
        (MulAction.stabilizer M22 B).comap p ∧
      (∀ l v, e (automizerRepresentation V
        (V.normalizerMonoidHom.rangeRestrict (inclusion (inf_le_left.trans hLN) l)) v) =
          m22CodeRepresentation (c l).val (e v)) := by
  let C := L ⊓ centralizer ({(z : G)} : Set G)
  let S := MulAction.stabilizer M22 B
  let j : C →* L := inclusion inf_le_left
  have hf (l : L) : p l ∈ S ↔ l.val ∈ centralizer ({(z : G)} : Set G) :=
    m22_marking_centralizer_mem_iff L V hLN p e he z hB hzB l
  let c : C →* S := (p.comp j).codRestrict S (fun l => (hf (j l)).mpr l.property.2)
  refine ⟨c,?_,fun _ => rfl,?_,?_,fun l v => he (j l) v⟩
  · intro y
    obtain ⟨l,hl⟩ := hp y.val
    have hc : l.val ∈ C := ⟨l.property,(hf l).mp (hl.symm ▸ y.property)⟩
    exact ⟨⟨l,hc⟩,Subtype.ext hl⟩
  · ext l
    change c l = 1 ↔ (l : G) ∈ V
    have hmem : j l ∈ p.ker ↔ j l ∈ V.subgroupOf L := by rw [hk]
    exact Subtype.ext_iff.trans hmem
  · ext l
    change (l.val ∈ L ∧ l.val ∈ centralizer ({(z : G)} : Set G)) ↔ p l ∈ S
    exact ⟨fun hl => (hf l).mpr hl.2,fun hl => ⟨l.property,(hf l).mp hl⟩⟩

include hp hk he in
/-- Select the hexad and its full centralizer cover in the original coordinates. -/
theorem m22_marking_centralizer_cover [Finite G]
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (z : V) (hzT : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    ∃ B : Finset (Fin 22), ∃ hB : B ∈ m22Blocks,
      e (Additive.ofMul z) = m22HexadVector hB ∧
      ∃ c : (L ⊓ centralizer ({(z : G)} : Set G) : Subgroup G) →* MulAction.stabilizer M22 B,
        Function.Surjective c ∧
        (∀ l, (c l).val = p ⟨l,l.property.1⟩) ∧
        c.ker = V.subgroupOf (L ⊓ centralizer ({(z : G)} : Set G)) ∧
        (L ⊓ centralizer ({(z : G)} : Set G)).subgroupOf L =
          (MulAction.stabilizer M22 B).comap p ∧
        (∀ l v, e (automizerRepresentation V
          (V.normalizerMonoidHom.rangeRestrict (inclusion (inf_le_left.trans hLN) l)) v) =
            m22CodeRepresentation (c l).val (e v)) := by
  obtain ⟨B,hB,hzB⟩ := m22_marking_central_hexad L V hLN p hp e he T hTL z hzT hne
  exact ⟨B,hB,hzB,m22_marking_centralizer_cover_of_hexad L V hLN p hp hk e he z hB hzB⟩

include hk he in
/-- Faithfulness detects the entire module centralizer in every subgroup of L. -/
theorem m22_marking_centralizer_kernel (X : Subgroup G) (hXL : X ≤ L) :
    (centralizer (V : Set G)).subgroupOf X = V.subgroupOf X := by
  ext x
  change (x : G) ∈ centralizer (V : Set G) ↔ (x : G) ∈ V
  constructor
  · intro hx
    let l : L := ⟨x,hXL x.property⟩
    have hact : m22CodeRepresentation (p l) = 1 := by
      apply LinearMap.ext
      intro w
      obtain ⟨v,rfl⟩ := e.surjective w
      have hv : automizerRepresentation V
          (V.normalizerMonoidHom.rangeRestrict (inclusion hLN l)) v = v := by
        apply Additive.toMul.injective
        apply Subtype.ext
        change (x : G)*(v.toMul : G)*(x : G)⁻¹ = v.toMul
        exact mul_inv_eq_iff_eq_mul.mpr (hx v.toMul v.toMul.property).symm
      exact (he l v).symm.trans (congrArg e hv)
    have hp1 : p l = 1 := native_code_faithful (hact.trans m22CodeRepresentation.map_one.symm)
    exact (show l ∈ V.subgroupOf L from hk ▸ hp1)
  · intro hx v hv
    exact congrArg Subtype.val (mul_comm' (⟨v,hv⟩ : V) (⟨x,hx⟩ : V))

include hk he in
/-- The point-pairing actor kernel is exactly the original module intersection. -/
theorem m22_marking_point_kernel [Finite G] (z : G) :
    (centralizer (V : Set G)).subgroupOf (Centralizer.localTwoCore L z) =
      V.subgroupOf (Centralizer.localTwoCore L z) :=
  m22_marking_centralizer_kernel L V hLN p hk e he _
    ((Centralizer.localTwoCore_le L z).trans ((Centralizer.localResidual_le L z).trans inf_le_left))

include hp hk he in
/-- The selected whole-code marking discharges the original full point-pairing
premise and its exact kernel, with both fixed-space conclusions retained. -/
theorem m22_marking_point_pairing [Finite G]
    (T : Sylow 2 G) (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (z : V) (hzT : (z : G) ∈ centralizer (T : Set G)) (hne : z ≠ 1) :
    Centralizer.SourcePointPairing L V z NativePairing.Section ∧
      (centralizer (V : Set G)).subgroupOf (Centralizer.localTwoCore L z) =
        V.subgroupOf (Centralizer.localTwoCore L z) ∧
      V ⊓ centralizer (Centralizer.localTwoCore L z : Set G) = zpowers (z : G) ∧
      ∀ v : V,
        (∀ x : Centralizer.localTwoCore L z, ⁅(x : G),(v : G)⁆ ∈ zpowers (z : G)) ↔
          (v : G) ∈ Centralizer.commutatorSpace L V z := by
  obtain ⟨B,hB,hzB,c,hc,_,hck,_,hce⟩ :=
    m22_marking_centralizer_cover L V hLN p hp hk e he T hTL z hzT hne
  have hkp : IsPGroup 2 c.ker := by
    rw [hck]
    exact (IsElementaryAbelian.isPGroup 2 V).comap_subtype
  obtain ⟨hf,hfk⟩ := m22_point_full_residual_cover L z hB c hc hkp
  obtain ⟨hpair,hfix,hmod⟩ := m22_point_hexad_pairing L V z hLN hB e
    (c.comp (inclusion (Centralizer.localResidual_le L z))) hf hfk hzB
      (fun r v => hce (inclusion (Centralizer.localResidual_le L z) r) v)
  exact ⟨hpair,m22_marking_point_kernel L V hLN p hk e he z,hfix,hmod⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
