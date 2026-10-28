module

public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.CoreElimination.InternalModule
public import Theory.GroupTheory.PCoreRestriction
public import Theory.GroupTheory.RadicalNormalizerControl
public import Theory.GroupTheory.PRadical

/-!
# Comparing the internal orbit with the C.2.7 module

For D=K₁R, the source seed lies in Ω₁(Z(O₂(D))): it lies in O₂(H),
which restricts into O₂(D), and centralizes R containing O₂(D). Its local
normal closure is exactly its K₁-orbit and embeds both into the full H-orbit
and into Ω₁(Z(O₂(D))). The two local modules have centralizer O₂(D),
because the seed centralizer is a two-group. Their faithful core-quotient
representations are intertwined by the actual subgroup inclusion.

The final fixed-space test applies to either genuine conjugation module.
It does not identify the full H-module with the local C.2.7 module, or assert
that the source geometry has one of the classified block models.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.2.7
(printed pp.145–147) and the characteristic-two paragraph of 15.4.20
(printed p.1164).
-/

@[expose] public section

open Subgroup Stellmacher Theory.GroupTheory
open Representation.BinaryOffender Representation.NormalElementaryQuotient
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
variable {H : Type*} [Group H]

/-- The actual module in C.2.7, intrinsically in its acting group. -/
noncomputable def omegaCoreModule (D : Type*) [Group D] : Subgroup D :=
  omegaOneCenterAmbient (pCore 2 D)

instance omegaCoreModule_normal (D : Type*) [Group D] : (omegaCoreModule D).Normal := by
  apply normal_iff_map_conj_eq.mpr
  intro d
  rw [omegaCoreModule, ← omegaOneCenterAmbient_map_injective _ (MulAut.conj d).injective,
    Subgroup.Normal.map_conj_eq]

instance omegaCoreModule_elementary (D : Type*) [Group D] :
    IsElementaryAbelian 2 (omegaCoreModule D) := omegaOneCenterAmbient_elementaryAbelian _

theorem omegaCoreModule_central (D : Type*) [Group D] :
    pCore 2 D ≤ centralizer (omegaCoreModule D : Set D) := by
  intro q hq z hz
  exact ((mem_omegaOneCenterAmbient_iff _ _).mp hz).2.2 q hq |>.symm

/-- The ambient core restricts into every subgroup's intrinsic core. -/
theorem seed_le_local_core (D Z : Subgroup H) (hZQ : Z ≤ pCore 2 H) :
    Z.subgroupOf D ≤ pCore 2 D := by
  have hQ : (pCore 2 H).subgroupOf D ≤ pCore 2 D :=
    le_sSup ⟨inferInstance, pCore_isPGroup.comap_subtype⟩
  exact (show Z.subgroupOf D ≤ (pCore 2 H).subgroupOf D from fun _ hz => hZQ hz).trans hQ

/-- Once the local core lies in R, the Sylow-central seed lies in the
actual C.2.7 module. No equality of the two modules is asserted. -/
theorem seed_le_omegaCoreModule (D R Z : Subgroup H)
    [IsElementaryAbelian 2 Z] (hZQ : Z ≤ pCore 2 H)
    (hQR : (pCore 2 D).map D.subtype ≤ R) (hRC : R ≤ centralizer (Z : Set H)) :
    Z.subgroupOf D ≤ omegaCoreModule D := by
  intro z hz
  apply (mem_omegaOneCenterAmbient_iff _ _).mpr
  exact ⟨seed_le_local_core D Z hZQ hz,
    Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (z : H) hz),
    fun q hq => Subtype.ext ((mem_centralizer_iff.mp
      (hRC (hQR ⟨q, hq, rfl⟩)) z hz).symm)⟩

/-- Radicality supplies the local-core containment used in the comparison. -/
theorem local_core_le_radical [Finite H] (D R : Subgroup H) (hRD : R ≤ D)
    (hR : IsPRadical 2 (R.subgroupOf D)) : (pCore 2 D).map D.subtype ≤ R := by
  have hc := pCore_le_of_pCore_normalizer_le (R.subgroupOf D) hR.isPGroup hR.2.le
  exact (map_mono hc).trans_eq (map_subgroupOf_eq_of_le hRD)

/-- The local orbit embeds into both the full internal module and the
C.2.7 module, using precisely the source's centralizing supplement. -/
theorem local_orbit_comparison (D K R Z : Subgroup H)
    [IsElementaryAbelian 2 Z] (hKD : K ≤ D) (hRD : R ≤ D) (hZD : Z ≤ D)
    (hDK : D ≤ normalizer (K : Set H)) (hgen : K ⊔ R = D)
    (hZQ : Z ≤ pCore 2 H) (hQR : (pCore 2 D).map D.subtype ≤ R)
    (hRC : R ≤ centralizer (Z : Set H)) :
    (normalClosure (Z.subgroupOf D : Set D)).map D.subtype = conjugateModule K Z ∧
      conjugateModule K Z ≤ normalClosure (Z : Set H) ∧
      conjugateModule K Z ≤ (omegaCoreModule D).map D.subtype := by
  let : (K.subgroupOf D).Normal := normal_subgroupOf_of_le_normalizer hDK
  have hgen' : K.subgroupOf D ⊔ R.subgroupOf D = ⊤ := by
    apply map_injective D.subtype_injective
    rw [Subgroup.map_sup, map_subgroupOf_eq_of_le hKD, map_subgroupOf_eq_of_le hRD, hgen,
      ← MonoidHom.range_eq_map, range_subtype]
  have hc' : R.subgroupOf D ≤ centralizer (Z.subgroupOf D : Set D) := by
    intro r hr z hz
    exact Subtype.ext (mem_centralizer_iff.mp (hRC hr) z hz)
  have he := congrArg (Subgroup.map D.subtype)
    (normalClosure_eq_conjugateModule (K.subgroupOf D) (R.subgroupOf D)
      (Z.subgroupOf D) hgen' hc')
  rw [conjugateModule_subgroupOf_map hKD hZD] at he
  refine ⟨he, ?_, ?_⟩
  · apply iSup_le
    intro k
    rintro _ ⟨z, hz, rfl⟩
    exact (normalClosure_normal (s := (Z : Set H))).conj_mem z (le_normalClosure hz) k
  · rw [← he]
    exact map_mono (normalClosure_le_normal
      (seed_le_omegaCoreModule D R Z hZQ hQR hRC))

/-- Both action kernels are the same intrinsic core. This strengthens the
upper bound of C.2.7(1) for the actual seed-centralizer geometry. -/
theorem comparison_centralizers (D Z : Subgroup H) (hZD : Z ≤ D)
    (hseed : Z.subgroupOf D ≤ omegaCoreModule D)
    (hC : IsPGroup 2 (centralizer (Z : Set H))) :
    centralizer (normalClosure (Z.subgroupOf D : Set D) : Set D) = pCore 2 D ∧
      centralizer (omegaCoreModule D : Set D) = pCore 2 D := by
  have hp : IsPGroup 2 (centralizer (Z.subgroupOf D : Set D)) := by
    have hcLe : centralizer (Z.subgroupOf D : Set D) ≤
        (centralizer (Z : Set H)).comap D.subtype := by
      intro c hc z hz
      exact congrArg Subtype.val (hc ⟨z, hZD hz⟩ hz)
    exact (hC.comap_of_injective D.subtype D.subtype_injective).to_le hcLe
  have hcore : pCore 2 D ≤ centralizer (Z.subgroupOf D : Set D) :=
    (omegaCoreModule_central D).trans (centralizer_le hseed)
  have hc := centralizer_normalClosure_eq_pCore_of_isPGroup 2 (Z.subgroupOf D) hp hcore
  refine ⟨hc, le_antisymm ?_ (omegaCoreModule_central D)⟩
  rw [← hc]
  exact centralizer_le (normalClosure_le_normal hseed)


/-- Actual conjugation on an elementary normal subgroup with two-core kernel. -/
noncomputable def coreAction (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hc : centralizer (V : Set H) = pCore 2 H) :
    Representation (ZMod 2) (H ⧸ pCore 2 H) (Additive V) :=
  representation V (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    ((QuotientGroup.ker_mk' _).trans hc.symm)

theorem coreAction_apply (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hc : centralizer (V : Set H) = pCore 2 H) (g : H) (v : Additive V) :
    ((coreAction V hc (QuotientGroup.mk' _ g) v).toMul : H) =
      g * (v.toMul : H) * g⁻¹ :=
  representation_apply V _ (QuotientGroup.mk'_surjective _) _ g v

theorem coreAction_injective (V : Subgroup H) [V.Normal] [IsElementaryAbelian 2 V]
    (hc : centralizer (V : Set H) = pCore 2 H) : Function.Injective (coreAction V hc) :=
  representation_injective V _ (QuotientGroup.mk'_surjective _) _

/-- The inclusion of the orbit module into the C.2.7 module is linear. -/
noncomputable def moduleInclusion {V W : Subgroup H}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] (hVW : V ≤ W) :
    Additive V →ₗ[ZMod 2] Additive W :=
  (inclusion hVW).toAdditive.toZModLinearMap 2

theorem moduleInclusion_injective {V W : Subgroup H}
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] (hVW : V ≤ W) :
    Function.Injective (moduleInclusion hVW) := by
  intro a b hab
  exact Additive.toMul.injective ((inclusion_injective hVW) hab)

/-- The inclusion intertwines the actions of the same actual core quotient. -/
theorem moduleInclusion_equivariant {V W : Subgroup H} [V.Normal] [W.Normal]
    [IsElementaryAbelian 2 V] [IsElementaryAbelian 2 W] (hVW : V ≤ W)
    (hV : centralizer (V : Set H) = pCore 2 H)
    (hW : centralizer (W : Set H) = pCore 2 H)
    (g : H ⧸ pCore 2 H) (v : Additive V) :
    moduleInclusion hVW (coreAction V hV g v) =
      coreAction W hW g (moduleInclusion hVW v) := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  apply Additive.toMul.injective
  apply Subtype.ext
  change ((coreAction V hV (QuotientGroup.mk' _ x) v).toMul : H) = _
  rw [coreAction_apply, coreAction_apply]
  rfl

/-- A Sylow fixing the seed cannot have a non-Sylow element fixing all of
its module fixed space. The input is an actual conjugation module. -/
theorem no_fixedSpace_enlargement (V Z : Subgroup H) [V.Normal]
    [IsElementaryAbelian 2 V] (hc : centralizer (V : Set H) = pCore 2 H)
    (hZV : Z ≤ V) (P : Sylow 2 H)
    (hCZ : centralizer (Z : Set H) = (P : Subgroup H))
    (g : H ⧸ pCore 2 H) (hg : g ∉ (P : Subgroup H).map (QuotientGroup.mk' _))
    (hfix : ∀ v ∈ fixedSpace (coreAction V hc)
      ((P : Subgroup H).map (QuotientGroup.mk' _)), coreAction V hc g v = v) : False := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 H) g
  apply hg
  apply mem_map_of_mem
  rw [← hCZ]
  intro z hz
  let v : Additive V := Additive.ofMul ⟨z, hZV hz⟩
  have hv : v ∈ fixedSpace (coreAction V hc) ((P : Subgroup H).map (QuotientGroup.mk' _)) := by
    intro a
    obtain ⟨y, hy, hay⟩ := a.property
    change coreAction V hc (a : H ⧸ pCore 2 H) v = v
    rw [← hay]
    apply Additive.toMul.injective
    apply Subtype.ext
    rw [coreAction_apply]
    change y * z * y⁻¹ = z
    have hh := mem_centralizer_iff.mp (hCZ.symm ▸ hy) z hz
    rw [← hh, mul_inv_cancel_right]
  have hh := congrArg (fun w : Additive V => (w.toMul : H)) (hfix v hv)
  rw [coreAction_apply] at hh
  exact (mul_inv_eq_iff_eq_mul.mp hh).symm

end CFSG.Quasithin.Chapter15.Section04.LocalSetup.CoreElimination.BlockSieve
