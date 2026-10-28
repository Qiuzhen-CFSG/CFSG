module
public import CFSG.Quasithin.ChapterH.Section13To16.M22Local.Hexad.NativeCoordinates
public import CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows.M22CodePointSpace

/-!
# The original M22 point section from arbitrary hexad coordinates

Conjugate an arbitrary native hexad and the whole code by the same operator.
The full original point-residual map retains its kernel. Its intrinsic core
moves the actual five-space, while the marked original vector spans the
native fixed line. The inner A6 quotient gives the irreducible original
interval, and the native whole-code displacement gives [V,L_z]=V.

Source: Aschbacher--Smith H.16.4 and 8.2.11--12, printed pp.403,722.
The original whole-code marking, residual surjection and full two-group
kernel remain the earlier-source inputs.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
open Sporadic.Mathieu MathieuCode MathieuCode.Hexad
open MathieuCode.Hexad.ChiefFlag MathieuCode.Hexad.ChiefFlag.Actions
open M22ChapterH.Hexad.Action
open scoped IsMulCommutative Pointwise
namespace CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
open ChapterE ChapterH.Section13To16.M22Local.Hexad
variable {G : Type*} [Group G] [Finite G]
set_option backward.isDefEq.respectTransparency false

omit [Finite G] in
/-- The actual original central line in native whole-code coordinates. -/
theorem m22_point_line_coordinates (V : Subgroup G) [IsElementaryAbelian 2 V]
    (z : V) (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (hz : e (Additive.ofMul z) = m22HexadVector m22Hexad24Ten_mem) (v : Additive V) :
    (v.toMul : G) ∈ zpowers (z : G) ↔ e v ∈ V1.toSubmodule := by
  have hp : e (Additive.ofMul z) ∈ V1.toSubmodule := by
    rw [hz, NativeCoordinates.fixedLine_span]
    exact Submodule.subset_span (Set.mem_singleton _)
  constructor
  · intro hv
    let A := binarySubgroup (V1.toSubmodule.comap e.toLinearMap)
    have hA : zpowers (z : G) ≤ A.map V.subtype :=
      zpowers_le.mpr ⟨z,hp,rfl⟩
    obtain ⟨w,hw,he⟩ := hA hv
    have he' : w = v.toMul := Subtype.ext he
    change e (Additive.ofMul w) ∈ V1.toSubmodule at hw
    rw [he'] at hw
    exact hw
  · intro hv
    rw [NativeCoordinates.fixedLine_span] at hv
    obtain ⟨a,ha⟩ := Submodule.mem_span_singleton.mp hv
    fin_cases a
    · have he : e v = 0 := by simpa using ha.symm
      have hv0 := e.map_eq_zero_iff.mp he
      rw [hv0]
      exact (zpowers (z : G)).one_mem
    · change (1 : ZMod 2) • m22HexadVector m22Hexad24Ten_mem = e v at ha
      rw [one_smul] at ha
      have he : e v = e (Additive.ofMul z) := ha.symm.trans hz.symm
      rw [e.injective he]
      exact mem_zpowers _

/-- Whole-code equivariance identifies the literal original point commutator. -/
theorem m22_point_residual_commutator_coordinates
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : G)
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* M22ChapterH.Hexad.Action.Inner)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v)) (v : Additive V) :
    (v.toMul : G) ∈ Centralizer.commutatorSpace L V z ↔ e v ∈ V5.toSubmodule := by
  rw [NativeSource.code_clauses.1.commutator_space]
  exact m22_point_commutator_coordinates V (Centralizer.localTwoCore L z)
    (((Centralizer.localTwoCore_le L z).trans
      ((Centralizer.localResidual_le L z).trans inf_le_left)).trans hLN) e
    ((m22ToPairStabilizer.comp M22ChapterH.Hexad.Action.Inner.subtype).comp
      (f.comp (inclusion (Centralizer.localTwoCore_le L z))))
    (fun x v => he (inclusion (Centralizer.localTwoCore_le L z) x) v)
    (m22_point_core_range L z f hf hk) v

/-- The original point residual has no invariant subgroup properly between
its original central line and its literal rank-five commutator. -/
theorem m22_point_residual_irreducible_interval
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* M22ChapterH.Hexad.Action.Inner)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hz : e (Additive.ofMul z) = m22HexadVector m22Hexad24Ten_mem)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v)) :
    ∀ Y : Subgroup G, zpowers (z : G) ≤ Y → Y ≤ Centralizer.commutatorSpace L V z →
      Centralizer.localResidual L z ≤ normalizer (Y : Set G) →
      Y = zpowers (z : G) ∨ Y = Centralizer.commutatorSpace L V z := by
  intro Y hZY hYW hRY
  have hWV := Centralizer.commutatorSpace_le L V z hLN
  have hYV := hYW.trans hWV
  let S := (binarySpace (Y.subgroupOf V)).map e.toLinearMap
  have hS (v : Additive V) : e v ∈ S ↔ (v.toMul : G) ∈ Y := by
    constructor
    · rintro ⟨w,hw,he⟩
      exact e.injective he ▸ hw
    · intro hv
      exact ⟨v,hv,rfl⟩
  have h1 : V1.toSubmodule ≤ S := by
    intro w hw
    obtain ⟨v,rfl⟩ := e.surjective w
    exact (hS v).mpr (hZY ((m22_point_line_coordinates V z e hz v).mpr hw))
  have h5 : S ≤ V5.toSubmodule := by
    intro w hw
    obtain ⟨v,rfl⟩ := e.surjective w
    exact (m22_point_residual_commutator_coordinates L V z hLN e f hf hk he v).mp
      (hYW ((hS v).mp hw))
  have hstable (g : M22ChapterH.Hexad.Action.Inner) (v : M22Code) (hv : v ∈ S) :
      m22CodeRepresentation g.val v ∈ S := by
    obtain ⟨r,rfl⟩ := hf g
    obtain ⟨w,rfl⟩ := e.surjective v
    rw [← he]
    apply (hS _).mpr
    exact le_normalizer_iff.mp hRY r r.property w.toMul ((hS w).mp hv)
  rcases NativeCoordinates.invariant_interval S h1 h5 hstable with h | h
  · left
    apply le_antisymm _ hZY
    intro v hv
    let w : Additive V := Additive.ofMul ⟨v,hYV hv⟩
    apply (m22_point_line_coordinates V z e hz w).mpr
    rw [← h]
    exact (hS w).mpr hv
  · right
    apply le_antisymm hYW
    intro v hv
    let w : Additive V := Additive.ofMul ⟨v,hWV hv⟩
    apply (hS w).mp
    rw [h]
    exact (m22_point_residual_commutator_coordinates L V z hLN e f hf hk he w).mp hv

/-- The original central line is properly contained in the original five-space. -/
theorem m22_point_residual_strict
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* M22ChapterH.Hexad.Action.Inner)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hz : e (Additive.ofMul z) = m22HexadVector m22Hexad24Ten_mem)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v)) :
    zpowers (z : G) < Centralizer.commutatorSpace L V z := by
  have h15 : V1.toSubmodule < V5.toSubmodule := NativeSource.code_clauses.1.strict.2.1
  have hZW : zpowers (z : G) ≤ Centralizer.commutatorSpace L V z := by
    apply zpowers_le.mpr
    apply (m22_point_residual_commutator_coordinates L V z hLN e f hf hk he _).mpr
    apply h15.le
    exact (m22_point_line_coordinates V z e hz _).mp (mem_zpowers _)
  apply lt_of_le_of_ne hZW
  intro h
  apply h15.ne
  apply le_antisymm h15.le
  intro w hw
  obtain ⟨v,rfl⟩ := e.surjective w
  apply (m22_point_line_coordinates V z e hz v).mp
  rw [h]
  exact (m22_point_residual_commutator_coordinates L V z hLN e f hf hk he v).mpr hw

omit [Finite G] in
/-- The original residual moves the whole original code subgroup. -/
theorem m22_point_residual_full_movement
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : G)
    (hLN : L ≤ normalizer (V : Set G))
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* M22ChapterH.Hexad.Action.Inner)
    (hf : Function.Surjective f)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v)) :
    ⁅V,Centralizer.localResidual L z⁆ = V := by
  let R := Centralizer.localResidual L z
  have hRV : R ≤ normalizer (V : Set G) :=
    ((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN
  let a := V.normalizerMonoidHom.rangeRestrict.comp (inclusion hRV)
  let ρ := (automizerRepresentation V).comp a
  let q := M22ChapterH.Hexad.Action.Inner.subtype.comp f
  have hq : q.range = M22ChapterH.Hexad.Action.Inner := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hf,
      ← MonoidHom.range_eq_map, range_subtype]
  have hact (r : R) (v : V) :
      ρ r (Additive.ofMul v) = Additive.ofMul
        (⟨(r : G)*(v : G)*(r : G)⁻¹,le_normalizer_iff.mp hRV r r.property v v.property⟩ : V) := rfl
  have hcomm := commutator_image_eq ρ V V R hRV le_rfl (MonoidHom.id R)
    (MonoidHom.id V) (fun r v => hact r v) ⊤ (by ext v; simp [binarySubgroup])
  have hC : (⁅V,R⁆).subgroupOf V = binarySubgroup (subspaceCommutator ρ ⊤ (⊤ : Subgroup R)) := by
    simpa only [map_id,(MonoidHom.id R).range_eq_top_of_surjective (fun r => ⟨r,rfl⟩)] using hcomm
  have he' (r : R) (w : M22Code) :
      ρ r (e.symm w) = e.symm (m22CodeRepresentation (q r) w) := by
    apply e.injective
    exact (he r (e.symm w)).trans (by rw [e.apply_symm_apply,e.apply_symm_apply]; rfl)
  have hm := subspaceCommutator_map_embedding ρ m22CodeRepresentation q
    e.symm.toLinearMap he' (⊤ : Subgroup R) (⊤ : Submodule (ZMod 2) M22Code)
  have hM : subspaceCommutator ρ ⊤ (⊤ : Subgroup R) = ⊤ := by
    simpa only [Submodule.map_top,LinearEquiv.range,←MonoidHom.range_eq_map,hq,
      NativeInner.full_movement] using hm
  apply le_antisymm (le_normalizer_iff_commutator_le_left.mp hRV)
  intro v hv
  have hm : (⟨v,hv⟩ : V) ∈ (⁅V,R⁆).subgroupOf V := by
    rw [hC,hM]
    trivial
  exact hm

/-- An arbitrary original hexad marking supplies all four point-section
conclusions, with its whole kernel and its actual central vector retained. -/
theorem m22_point_hexad_section
    (L V : Subgroup G) [IsElementaryAbelian 2 V] (z : V)
    (hLN : L ≤ normalizer (V : Set G))
    {B : Finset (Fin 22)} (hB : B ∈ m22Blocks)
    (e : Additive V ≃ₗ[ZMod 2] M22Code)
    (f : Centralizer.localResidual L z →* MulAction.stabilizer M22 B)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hz : e (Additive.ofMul z) = m22HexadVector hB)
    (he : ∀ r v, e (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (f r).val (e v)) :
    Nat.card (Centralizer.commutatorSpace L V z) = 32 ∧
      zpowers (z : G) < Centralizer.commutatorSpace L V z ∧
      (∀ Y : Subgroup G, zpowers (z : G) ≤ Y → Y ≤ Centralizer.commutatorSpace L V z →
        Centralizer.localResidual L z ≤ normalizer (Y : Set G) →
        Y = zpowers (z : G) ∨ Y = Centralizer.commutatorSpace L V z) ∧
      ⁅V,Centralizer.localResidual L z⁆ = V := by
  let E := e.trans (WholeCodeCoordinates.codeEquiv hB)
  let F := WholeCodeCoordinates.actorMap hB f
  have hF : Function.Surjective F := WholeCodeCoordinates.actorMap_surjective hB f hf
  have hK : IsPGroup 2 F.ker := by
    change IsPGroup 2 (WholeCodeCoordinates.actorMap hB f).ker
    rw [WholeCodeCoordinates.actorMap_ker]
    exact hk
  have hZ : E (Additive.ofMul z) = m22HexadVector m22Hexad24Ten_mem :=
    (congrArg (WholeCodeCoordinates.codeEquiv hB) hz).trans
      (WholeCodeCoordinates.codeEquiv_point hB)
  have hE : ∀ r v, E (automizerRepresentation V
      (V.normalizerMonoidHom.rangeRestrict (inclusion
        (((Centralizer.localResidual_le L z).trans inf_le_left).trans hLN) r)) v) =
        m22CodeRepresentation (F r).val (E v) := fun r v =>
    (congrArg (WholeCodeCoordinates.codeEquiv hB) (he r v)).trans
      (WholeCodeCoordinates.codeEquiv_equivariant hB (f r) (e v))
  exact ⟨m22_point_residual_commutator_card L V z hLN E F hF hK hE,
    m22_point_residual_strict L V z hLN E F hF hK hZ hE,
    m22_point_residual_irreducible_interval L V z hLN E F hF hK hZ hE,
    m22_point_residual_full_movement L V z hLN E F hF hE⟩

end CFSG.Quasithin.Chapter8.Section02.MathieuShadowRows
