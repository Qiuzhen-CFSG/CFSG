module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
import all CFSG.Quasithin.ChapterC.Section01.BlockTypes.AutomorphismAction
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.FixedLayerCentralizer
public import Theory.Representation.SL3OddNaturalNormalizer.Semilinear

/-!
# Quotient-centralizing actors on natural binary SL3 blocks

An automorphism fixing L/O₂(L) induces an additive scalar on the actual
natural module. Over a field of order two this scalar is one. The three
subgroups lemma and [U(L),L]=U(L) lift fixation across the central attachment
of U(L). A two-perfect actor then fixes the entire short group by the
subgroup-and-quotient kernel argument.

The internal import of AutomorphismAction unfolds only the existing model
actor in the proof; its public abstraction boundary is preserved.
Source: Aschbacher--Smith C.1.10 and 15.1.24(2), pp.124 and 1101.
-/

public section
open Subgroup Representation Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {L F : Type*} [Group L] [Field F]

private theorem binary_module_fixed_of_quotient_fixed
    {ρ : Matrix.SpecialLinearGroup (Fin 3) F →* MulAut (Multiplicative (Fin 3 → F))}
    (m : BlockModuleModel L ρ) (hF : Nat.card F = 2)
    (hρ : ∀ g v, (ρ g v).toAdd = specialLinearNatural 3 g v.toAdd)
    (a : MulAut L) (ha : quotientAut (pCore 2 L) a = 1) :
    blockModuleAut a = 1 := by
  let b := m.moduleAction a
  let f : (Fin 3 → F) →+ (Fin 3 → F) := {
    toFun v := (b (Multiplicative.ofAdd v)).toAdd
    map_zero' := b.map_one
    map_add' v w := b.map_mul (Multiplicative.ofAdd v) (Multiplicative.ofAdd w) }
  have hq : m.quotientAction a = 1 := by
    apply MulEquiv.ext
    intro g
    obtain ⟨l,rfl⟩ := m.actor_surjective g
    rw [m.quotientAction_actor]
    have hh := DFunLike.congr_fun ha (QuotientGroup.mk' (pCore 2 L) l)
    rw [quotientAut_apply_mk] at hh
    exact congrArg m.quotientIso hh
  have hf (g : Matrix.SpecialLinearGroup (Fin 3) F) (v : Fin 3 → F) :
      f (specialLinearNatural 3 g v) = specialLinearNatural 3 g (f v) := by
    have hh := m.actions_compatible a g (Multiplicative.ofAdd v)
    rw [hq] at hh
    have hh' := congrArg Multiplicative.toAdd hh
    rw [hρ] at hh'
    change (b (ρ g (Multiplicative.ofAdd v))).toAdd = _ at hh'
    have he : ρ g (Multiplicative.ofAdd v) = Multiplicative.ofAdd (specialLinearNatural 3 g v) :=
      Multiplicative.toAdd.injective (hρ g _)
    rw [he] at hh'
    exact hh'
  obtain ⟨c,hc⟩ := SL3OddNaturalNormalizer.centralizer_scalar f hf
  have hc0 : c ≠ 0 := by
    intro he
    have hi : Function.Injective f := b.injective
    have hh : f (fun _ => 1) = f 0 := by simp only [hc,he,zero_smul]
    have hh' := congrFun (hi hh) 0
    exact one_ne_zero hh'
  obtain ⟨z,_,hz⟩ := (Nat.card_eq_two_iff' (0 : F)).mp hF
  have hc1 : c = 1 := (hz c hc0).trans (hz 1 one_ne_zero).symm
  have hb : b = 1 := by
    apply MulEquiv.ext
    intro v
    apply Multiplicative.toAdd.injective
    exact (hc v.toAdd).trans (by rw [hc1,one_smul]; rfl)
  apply MulEquiv.ext
  intro v
  apply m.moduleIso.injective
  obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (blockFixed L) v
  have hh := DFunLike.congr_fun hb (m.moduleIso (QuotientGroup.mk' (blockFixed L) u))
  change m.moduleAction a (m.moduleIso (QuotientGroup.mk' (blockFixed L) u)) = _ at hh
  rw [m.moduleAction_mk] at hh
  rw [blockModuleAut_apply_mk]
  exact hh

variable {G : Type*} [Group G] [Finite G]

/-- A two-perfect actor fixing the literal core quotient of a natural binary
SL3 block centralizes its full cover. -/
theorem IsSL3EvenBlock.centralizes_of_coreQuotient
    {X Y : Subgroup G} (hX : IsSL3EvenBlock X 1) (hY : IsPPerfect 2 Y)
    (hn : Y ≤ normalizer (X : Set G)) (hcore : ⁅Y,X⁆ ≤ X.pCoreIn 2) :
    Y ≤ centralizer (X : Set G) := by
  let U := (blockU X).map X.subtype
  have hAU : ⁅Y,U⁆ ≤ centralizer (X : Set G) := by
    apply commutator_le.mpr
    intro y hy u hu
    let a : MulAut X := X.normalizerMonoidHom ⟨y,hn hy⟩
    have hq : quotientAut (pCore 2 X) a = 1 := by
      apply MulEquiv.ext
      intro z
      obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 X) z
      rw [quotientAut_apply_mk]
      apply QuotientGroup.eq_iff_div_mem.mpr
      obtain ⟨w,hw,he⟩ := hcore (commutator_mem_commutator hy x.property)
      simp only [div_eq_mul_inv]
      exact (Subtype.ext he : w = a x * x⁻¹) ▸ hw
    obtain ⟨F,_,_,hF,ρ,⟨m⟩,hρ⟩ := hX.2.2
    have hm := binary_module_fixed_of_quotient_fixed m (by simpa using hF) hρ a hq
    obtain ⟨w,hw,rfl⟩ := hu
    have hh := DFunLike.congr_fun hm (QuotientGroup.mk' (blockFixed X) ⟨w,hw⟩)
    rw [blockModuleAut_apply_mk] at hh
    have hc0 : MulAut.characteristic (blockU X) a ⟨w,hw⟩ / (⟨w,hw⟩ : blockU X) ∈
        blockFixed X := QuotientGroup.eq_iff_div_mem.mp hh
    change (a w / w : X) ∈ center X at hc0
    have hc : (a w * w⁻¹ : X) ∈ center X := by
      simpa only [div_eq_mul_inv] using hc0
    intro x hx
    exact congrArg X.subtype (mem_center_iff.mp hc ⟨x,hx⟩)
  have hOU : X.pCoreIn 2 ≤ centralizer (U : Set G) :=
    (map_mono hX.2.1.core_centralizes_blockU).trans
      (map_centralizer_le_centralizer_image _ X.subtype)
  have hrot : ⁅⁅U,X⁆,Y⁆ = ⊥ := commutator_commutator_eq_bot_of_rotate
    (commutator_eq_bot_iff_le_centralizer.mpr (by rw [commutator_comm]; exact hcore.trans hOU))
    (commutator_eq_bot_iff_le_centralizer.mpr hAU)
  have hUX : ⁅U,X⁆ = U := by
    have hi := commutator_isPPerfect_idempotent X (X.pCoreIn 2)
      hX.2.1.twoPerfect (isPGroup_pCoreIn 2 X)
      (X.le_normalizer.trans (normalizer_le_normalizer_characteristic_image X (pCore 2 X)))
    simpa only [pCoreIn,U,blockU,map_commutator,←MonoidHom.range_eq_map,range_subtype] using hi
  rw [hUX] at hrot
  exact hX.2.1.centralizes_of_normalizing_coreQuotient_and_blockU X Y hY hn hcore
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hrot))

end CFSG.Quasithin.ChapterC
