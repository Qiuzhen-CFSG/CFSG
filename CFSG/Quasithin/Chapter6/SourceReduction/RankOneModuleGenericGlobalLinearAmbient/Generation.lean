module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalLinearAmbient.CentralFusion
public import Theory.SpecificGroups.PSL3.LinearAmbientGeometry.StrongEmbedding
public import BenderSuzuki.SE.SingleInvolutionClass
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericGlobalNormalizerAction

/-!
# Linear generation when the source Sylow is ambient Sylow

Assume the actual common factor Sylow S equals T. Its central involution
has two-core contained in S, so the proved core alternatives and local
intersection bounds give C_G(z) ≤ N_G(L) ∩ N_G(O²(H)). In fact its core is S.
Sylow conjugacy and the affine root-plane fusion give one involution class
in every overgroup of the factor join. A proper full-normalizer join would
therefore be strongly embedded, contrary to the noncommuting root
involutions and Bender–Suzuki. The factor join is normal there, and the
original simplicity makes it the entire group too.

The S=T premise is explicit here and is discharged for odd n in OddDegree.
It is not assumed in the prepared all-degree terminal recognition theorem.
Source: the generation step of Aschbacher–Smith F.4.45–46, printed p.297,
with a Bender–Suzuki argument replacing the odd-order subgroup count;
§5.3.7, p.660 (`refs/quasithin.pdf`).
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
variable {G : Type*} [Group G] [Finite G]

variable {T : Sylow 2 G} {L W H A B : Subgroup G} {n : ℕ}
    (d : Preparation T L H A B (residual H))
    (h : Input KnownSimple.IsKnownSimple T L W n)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hp : Group.IsPerfect (residual H))
    (F : Type) [Field F] [Finite F] [CharP F 2]
    {m : ℕ} (hm : 0 < m) (hF : Nat.card F = 2^m)
    (he : Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F)) ∨
      Nonempty (RankTwoAmalgam.Iso
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H))
      (ChapterF.GreenBook.LieModels.LinearThree.amalgam F).reverse))
    (hmax : residual H ∈ Chapter1.LStar G (T : Subgroup G))
include d h hH hp hm hF he hmax

/-- Source §5.3.7 follows from the actual equality S=T. -/
theorem Preparation.linear_centralizer_le_inter_of_sourceS_eq_sylow
    (hST : sourceS L H = (T : Subgroup G))
    (z : G) (hz : orderOf z = 2) (hzS : z ∈ centerIn (sourceS L H)) :
    centralizer ({z} : Set G) ≤
      normalizer (L : Set G) ⊓ normalizer (residual H : Set G) := by
  have hzT : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    rw [← hST]
    exact fun x hx => mem_centralizer_singleton_iff.mpr (hzS.2 x hx)
  have hR : (centralizer ({z} : Set G)).pCoreIn 2 ≤ sourceS L H := by
    rw [hST]
    have hh := pCoreIn_le_sylow (centralizer ({z} : Set G)) (T.subtype hzT)
    simpa only [Sylow.coe_subtype,subgroupOf_map_subtype,inf_eq_left.mpr hzT] using hh
  exact d.linear_centralizer_le_inter_of_core_le h hH hp F hm hF he hmax z hz hzS hzT hR

/-- The central involution core is the actual Sylow S once S=T. -/
theorem Preparation.linear_centralizer_core_eq_sourceS_of_sourceS_eq_sylow
    (hST : sourceS L H = (T : Subgroup G))
    (z : G) (hz : orderOf z = 2) (hzS : z ∈ centerIn (sourceS L H)) :
    (centralizer ({z} : Set G)).pCoreIn 2 = sourceS L H := by
  let C := centralizer ({z} : Set G)
  have hSC : sourceS L H ≤ C := fun x hx => mem_centralizer_singleton_iff.mpr (hzS.2 x hx)
  have hTC : (T : Subgroup G) ≤ C := hST ▸ hSC
  have hCN : C ≤ normalizer (sourceS L H : Set G) := by
    have hc := d.linear_centralizer_le_inter_of_sourceS_eq_sylow h hH hp F hm hF he hmax hST z hz hzS
    have hl := d.linear_factor_centralizer h hH hp F hm hF he hmax 0 z hzS
      (by intro hh; simp [hh] at hz)
    rw [← hl]
    exact (le_inf (hc.trans inf_le_left) C.le_normalizer).trans inf_normalizer_le_normalizer_inf
  apply le_antisymm
  · have hh := pCoreIn_le_sylow C (T.subtype hTC)
    rw [hST]
    simpa only [Sylow.coe_subtype,subgroupOf_map_subtype,inf_eq_left.mpr hTC] using hh
  · exact le_pCoreIn_of_normalizes (hST.symm ▸ T.isPGroup') hSC hCN

/-- Every overgroup of the original factors has one internal involution class when S=T. -/
theorem Preparation.linear_involutions_fused_in_overgroup
    (hST : sourceS L H = (T : Subgroup G))
    (Y : Subgroup G) (hJY : L ⊔ residual H ≤ Y)
    (z : G) (hz : z ∈ centerIn (sourceS L H)) (hz1 : z ≠ 1) :
    ∀ y ∈ Y, orderOf y = 2 → ∃ g ∈ Y, g * z * g⁻¹ = y := by
  have hTY : (T : Subgroup G) ≤ Y := by
    rw [← hST]
    exact (d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0).trans
      (le_sup_left.trans hJY)
  intro y hy hy2
  let yM : Y := ⟨y,hy⟩
  have hyM : orderOf yM = 2 := (orderOf_coe yM).symm.trans hy2
  have hpY : IsPGroup 2 (zpowers yM) := IsPGroup.of_card (n := 1)
    (by rw [Nat.card_zpowers,hyM,pow_one])
  obtain ⟨P,hP⟩ := hpY.exists_le_sylow
  obtain ⟨a,ha⟩ := MulAction.exists_smul_eq Y P (T.subtype hTY)
  have hay : (a : G) * y * (a : G)⁻¹ ∈ (T : Subgroup G) := by
    change a * yM * a⁻¹ ∈ (T.subtype hTY : Subgroup Y)
    rw [← ha]
    exact mem_map_of_mem (MulAut.conj a).toMonoidHom (hP (mem_zpowers yM))
  have ha2 : orderOf ((a : G) * y * (a : G)⁻¹) = 2 :=
    ((MulAut.conj (a : G)).orderOf_eq y).trans hy2
  obtain ⟨b,hb,hbz⟩ := d.linear_sourceS_involution_fused h hH hp F hm hF he hmax
    z hz hz1 _ (hST ▸ hay) ha2
  refine ⟨(a : G)⁻¹ * b,Y.mul_mem (Y.inv_mem a.property) (hJY hb),?_⟩
  calc
    _ = (a : G)⁻¹ * (b * z * b⁻¹) * (a : G) := by group
    _ = y := by rw [hbz]; group

/-- Both original joins generate the ambient group when S=T; no generation premise is assumed. -/
theorem Preparation.linear_ambient_generation_of_sourceS_eq_sylow
    (hST : sourceS L H = (T : Subgroup G)) :
    normalizer (L : Set G) ⊔ normalizer (residual H : Set G) = ⊤ ∧
      L ⊔ residual H = ⊤ := by
  obtain ⟨z,hz,hz2,hzT⟩ := d.linear_exists_sylow_central_involution h hH hp F hm hF he hmax
  have hz1 : z ≠ 1 := by intro hh; simp [hh] at hz2
  let J := L ⊔ residual H
  let M := normalizer (L : Set G) ⊔ normalizer (residual H : Set G)
  have hJM : J ≤ M := sup_le (L.le_normalizer.trans le_sup_left)
    ((residual H).le_normalizer.trans le_sup_right)
  have hSJ : sourceS L H ≤ J :=
    (d.linear_sourceS_le_factors h hH.1.1.2 hp F hm hF he 0).trans le_sup_left
  have hclass := d.linear_involutions_fused_in_overgroup h hH hp F hm hF he hmax
    hST M hJM z hz hz1
  obtain ⟨_,⟨e⟩,_⟩ := d.linear_core_structure h hH hp F hm hF he
  have hMG : M = ⊤ := by
    by_contra hproper
    apply Matrix.PSL3.LinearAmbientGeometry.not_stronglyEmbedded_of_unipotent F hm hF
      (sourceS L H) e M
    exact BenderSuzuki.isStronglyEmbedded_of_single_involution_class M hproper z hz2
      (hJM (hSJ hz.1))
      ((d.linear_centralizer_le_inter_of_sourceS_eq_sylow h hH hp F hm hF he hmax hST z hz2 hz).trans
        (inf_le_left.trans le_sup_left)) hclass
  have hcomp : ConcreteAmalgamComparison
      (sourceParabolicAmalgam ![L,residual H] (sourceS L H)) := .linear F m hm hF he
  have hlocal := d.normalizer_local_conditions h hH hmax rfl
    (d.common_sylow_of_comparison h hH.1.1.2 hp hcomp)
    (d.parabolic_sylow_core_eq_of_comparison h hH.1.1.2 hp hcomp)
  have hN : J.Normal := normalizer_eq_top_iff.mp (top_le_iff.mp (by
    have hh := normalizer_pair_normalizes hlocal
    change M ≤ normalizer (J : Set G) at hh
    rwa [hMG] at hh))
  let : IsSimpleGroup G := h.qtke.simple
  have hJG : J = ⊤ := hN.eq_bot_or_eq_top.resolve_left (by
    intro hbot
    exact hz1 (mem_bot.mp (hbot ▸ hSJ hz.1)))
  exact ⟨hMG,hJG⟩

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.Global
