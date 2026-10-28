module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Sections
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Outside.Setup
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.Actions.PointNormalizer.Kernel
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.CartanCore.NaturalSum.Action
public import Theory.GroupTheory.CoreCentralNormalizerAction
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding

/-!
# The exceptional actor on the two original closure sections

Conjugation by the original K acts on U/Z(U), where U is E.W, and on
its literal image in G₁/V₁. The two kernels are characterized by ambient
commutators. The point-image kernel is G₁-invariant and normalizes the
original solvable residual L₁: it preserves V, hence belongs to M₁.

An elementary central quotient of order at most 256 gives the actual
faithful action quotient an order dividing |GL₈(2)|. Transfer to
K/O₂,Z(K) is stated separately with its still-required kernel premise.
No exclusion of an odd extension or equality K=L₁ is asserted here.
Source: Aschbacher--Smith 11.5.7, refs/quasithin.pdf, printed p.782.
-/

@[expose] public noncomputable section
open Subgroup
open scoped commutatorElement
open CFSG.Quasithin.Chapter12.Section02
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {D : ChosenModule T L V} (E : Geometry D)

theorem K_normalizes_closure : E.K ≤ normalizer (E.W : Set G) :=
  E.K_le_G₁.trans (le_normalizer_conjugateSpanBy V E.G₁)

def conjugation : E.K →* MulAut E.W :=
  E.W.normalizerMonoidHom.comp (inclusion (K_normalizes_closure E))

theorem conjugation_apply (k : E.K) (u : E.W) :
    (conjugation E k u : G) = (k : G) * (u : G) * (k : G)⁻¹ := rfl

def centralAction : E.K →* MulAut (CentralQuotient E) :=
  (quotientAut (center E.W)).comp (conjugation E)

theorem centralAction_apply_mk (k : E.K) (u : E.W) :
    centralAction E k (QuotientGroup.mk' (center E.W) u) =
      QuotientGroup.mk' (center E.W) (conjugation E k u) :=
  quotientAut_apply_mk _ _ _

theorem mem_centralAction_kernel_iff (k : E.K) :
    k ∈ (centralAction E).ker ↔ ∀ u ∈ E.W, ⁅(k : G), u⁆ ∈ closureCenter E := by
  constructor
  · intro hk u hu
    have he := congrArg (fun a : MulAut (CentralQuotient E) =>
      a (QuotientGroup.mk' (center E.W) ⟨u,hu⟩)) (MonoidHom.mem_ker.mp hk)
    rw [centralAction_apply_mk] at he
    have hc := QuotientGroup.eq_iff_div_mem.mp he
    refine ⟨conjugation E k ⟨u,hu⟩ / ⟨u,hu⟩,hc,?_⟩
    simp only [subtype_apply,div_eq_mul_inv,coe_mul,coe_inv,conjugation_apply,
      commutatorElement_def]
  · intro hk
    apply MonoidHom.mem_ker.mpr
    ext a
    obtain ⟨u,rfl⟩ := QuotientGroup.mk'_surjective (center E.W) a
    rw [centralAction_apply_mk]
    apply QuotientGroup.eq_iff_div_mem.mpr
    obtain ⟨z,hz,he⟩ := hk u u.property
    have he' : z = conjugation E k u / u := by
      apply Subtype.ext
      simpa only [subtype_apply,div_eq_mul_inv,coe_mul,coe_inv,conjugation_apply,
        commutatorElement_def] using he
    exact he' ▸ hz

def pointAction : E.K →* MulAut (E.tilde E.W) :=
  E.tildeConjugation E.W E.K E.K_le_G₁ (K_normalizes_closure E)

theorem mem_pointAction_kernel_iff (k : E.K) :
    k ∈ (pointAction E).ker ↔ ∀ u ∈ E.W, ⁅(k : G), u⁆ ∈ E.V₁ := by
  constructor
  · intro hk u hu
    have he := congrArg (fun a : MulAut (E.tilde E.W) =>
      (a (E.tildeProjection E.W (Outside.closure_le_point_normalizer E) ⟨u,hu⟩) : E.Tilde))
      (MonoidHom.mem_ker.mp hk)
    change QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨k,E.K_le_G₁ k.property⟩ *
      QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)
        ⟨u,Outside.closure_le_point_normalizer E hu⟩ *
      (QuotientGroup.mk' (E.V₁.subgroupOf E.G₁) ⟨k,E.K_le_G₁ k.property⟩)⁻¹ =
      QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)
        ⟨u,Outside.closure_le_point_normalizer E hu⟩ at he
    have hc : QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)
        ⁅(⟨k,E.K_le_G₁ k.property⟩ : E.G₁),
          ⟨u,Outside.closure_le_point_normalizer E hu⟩⁆ = 1 := by
      rw [map_commutatorElement,commutatorElement_def,he,mul_inv_cancel]
    have hm : ⁅(⟨k,E.K_le_G₁ k.property⟩ : E.G₁),
        (⟨u,Outside.closure_le_point_normalizer E hu⟩ : E.G₁)⁆ ∈
          E.V₁.subgroupOf E.G₁ := (QuotientGroup.eq_one_iff _).mp hc
    exact hm
  · intro hk
    apply MonoidHom.mem_ker.mpr
    ext a
    obtain ⟨u,rfl⟩ := E.tildeProjection_surjective E.W
      (Outside.closure_le_point_normalizer E) a
    have hc : QuotientGroup.mk' (E.V₁.subgroupOf E.G₁)
        ⁅(⟨k,E.K_le_G₁ k.property⟩ : E.G₁),
          ⟨u,Outside.closure_le_point_normalizer E u.property⟩⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hk u u.property)
    rw [map_commutatorElement,commutatorElement_def,mul_inv_eq_one] at hc
    exact hc

theorem pointAction_kernel_eq_quotient_kernel :
    (pointAction E).ker = (Outside.quotientAction E E.K E.K_le_G₁).ker := by
  ext k
  rw [mem_pointAction_kernel_iff]
  exact (Outside.mem_actionCentralizer_iff E E.K E.K_le_G₁ k).symm

theorem pointAction_kernel_normalizes_residual :
    (pointAction E).ker.map E.K.subtype ≤ normalizer (E.L₁ : Set G) := by
  apply le_trans _ E.pointNormalizer_normalizes_L₁
  refine le_inf ?_ ((map_subtype_le _).trans E.K_le_G₁)
  apply le_trans _ (Outside.seed_normalizer_le_M E)
  apply le_normalizer_iff_commutator_le_right.mpr
  apply commutator_le.mpr
  rintro k ⟨a,ha,rfl⟩ v hv
  exact E.V₁_le ((mem_pointAction_kernel_iff E a).mp ha v
    (le_conjugateSpanBy V E.G₁ hv))

theorem pointAction_kernel_normalized :
    E.G₁ ≤ normalizer ((pointAction E).ker.map E.K.subtype : Set G) := by
  apply le_normalizer_iff.mpr
  rintro g hg _ ⟨k,hk,rfl⟩
  let k' : E.K := ⟨g * (k : G) * g⁻¹,
    (mem_normalizer_iff.mp (E.G₁_normalizes_K hg) k).mp k.property⟩
  refine ⟨k',?_,rfl⟩
  apply (mem_pointAction_kernel_iff E k').mpr
  intro u hu
  have hu' : g⁻¹ * u * g ∈ E.W := by
    simpa only [inv_inv,Geometry.W] using
      (mem_normalizer_iff.mp
        (le_normalizer_conjugateSpanBy V E.G₁ (E.G₁.inv_mem hg)) u).mp hu
  have hc := (mem_pointAction_kernel_iff E k).mp hk _ hu'
  have hc' : g * ⁅(k : G),g⁻¹ * u * g⁆ * g⁻¹ ∈ E.V₁ :=
    (mem_normalizer_iff.mp hg _).mp hc
  have he : ⁅(k' : G),u⁆ = g * ⁅(k : G),g⁻¹ * u * g⁆ * g⁻¹ := by
    dsimp only [k']
    simp only [commutatorElement_def]
    group
  rwa [he]

theorem centralAction_quotient_card_dvd_binary_eight
    [IsElementaryAbelian 2 (CentralQuotient E)]
    (hcard : Nat.card (CentralQuotient E) ≤ 256) :
    Nat.card (E.K ⧸ (centralAction E).ker) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  obtain ⟨f,hf⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p := 2) (n := 8) (CentralQuotient E) hcard
  let a : (E.K ⧸ (centralAction E).ker) →* MulAut (CentralQuotient E) :=
    QuotientGroup.kerLift (centralAction E)
  exact card_dvd_of_injective (f.comp a)
    (hf.comp (QuotientGroup.kerLift_injective _))

theorem coreCentral_card_dvd_binary_eight_of_kernel_le
    [IsElementaryAbelian 2 (CentralQuotient E)]
    (hcard : Nat.card (CentralQuotient E) ≤ 256)
    (hk : (centralAction E).ker ≤ centralPreimage (pCore 2 E.K)) :
    Nat.card (coreCentralQuotient E.K) ∣
      Nat.card (Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)) := by
  rw [← Nat.card_congr (centralPreimageQuotientEquiv (pCore 2 E.K)).toEquiv]
  apply dvd_trans ?_ (centralAction_quotient_card_dvd_binary_eight E hcard)
  rw [← index_eq_card,← index_eq_card]
  exact index_dvd_of_le hk

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Linear.Block.Exceptional
