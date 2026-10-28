module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition.FixedNormalizerFactors
public import Theory.GroupAction.FourCubicQuotient

/-!
# Cubic fixed points on the literal rank-two seed

The actual parabolic centralizer identity identifies the kernel of its
conjugation action with O2(I2). Thus the source S3 quotient acts faithfully
on the actual four-group, and its cubic fixes only the identity.
-/

public noncomputable section
open Subgroup InvertedCubicTensor
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
variable {G:Type*} [Group G] [Finite G] {T:Sylow 2 G} {V:Subgroup G}

theorem binary_core_cubic_seed_fixed_free (F:InvariantFlag T V 2)
    (L:Subgroup G) (e:((F.I₂ L)⧸pCore 2 (F.I₂ L))≃*S₃)
    (hIG:F.I₂ L≤F.Gi 2)
    (hcore:F.I₂ L⊓centralizer (F.Vi 2:Set G)=(F.I₂ L).pCoreIn 2)
    (h:F.I₂ L) (hh:F.binaryCoreProjection L e h=cubic)
    (v:G) (hv:v∈V) (hfix:(h:G)*v*(h:G)⁻¹=v) : v=1 := by
  let π := F.binaryCoreProjection L e
  have hπ:Function.Surjective π := by
    intro s
    obtain ⟨i,hi⟩ := QuotientGroup.mk'_surjective (pCore 2 (F.I₂ L)) (e.symm s)
    exact ⟨i,by rw [F.binaryCoreProjection_apply,hi,e.apply_symm_apply]⟩
  have hkπ:π.ker=pCore 2 (F.I₂ L) := by
    ext i
    change F.binaryCoreProjection L e i=1 ↔ i∈pCore 2 (F.I₂ L)
    rw [F.binaryCoreProjection_apply]
    constructor
    · intro hi
      exact (QuotientGroup.eq_one_iff i).mp (e.injective (hi.trans e.map_one.symm))
    · intro hi
      change e (QuotientGroup.mk i)=1
      rw [(QuotientGroup.eq_one_iff i).mpr hi,map_one]
  have hVN:F.I₂ L≤normalizer (V:Set G) := by simpa only [Gi,F.last] using hIG
  let act := V.normalizerMonoidHom.comp (inclusion hVN)
  have hka:act.ker=((F.I₂ L).pCoreIn 2).subgroupOf (F.I₂ L) := by
    ext i
    change act i=1 ↔ (i:G)∈(F.I₂ L).pCoreIn 2
    rw [←hcore]
    constructor
    · intro hi
      refine ⟨i.property,?_⟩
      intro w hw
      have he := congrArg (fun a:MulAut V=>(a ⟨w,F.last ▸ hw⟩:G)) hi
      change (i:G)*w*(i:G)⁻¹=w at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    · intro hi
      ext w
      change (i:G)*(w:G)*(i:G)⁻¹=w
      exact mul_inv_eq_iff_eq_mul.mpr ((hi.2 w (F.last.symm ▸ w.property)).symm)
  have hk:π.ker=act.ker := by
    rw [hka,hkπ]
    exact ((pCore 2 (F.I₂ L)).comap_map_eq_self_of_injective (F.I₂ L).subtype_injective).symm
  have hc:Nat.card V=4 := by
    simpa only [F.last,show (2:ℕ)^2=4 from rfl] using F.card 2 le_rfl
  have he : act h ⟨v,hv⟩=⟨v,hv⟩ := Subtype.ext hfix
  exact congrArg Subtype.val (Theory.GroupAction.cubic_four_action_fixed_free π hπ act hk hc h hh ⟨v,hv⟩ he)
end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.Recognition
