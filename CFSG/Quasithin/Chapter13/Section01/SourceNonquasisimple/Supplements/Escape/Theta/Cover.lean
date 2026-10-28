module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta.Factors
public import CFSG.Quasithin.ChapterA.Section04.Intersection
public import Theory.GroupTheory.CComponent.QuotientLifting
public import Theory.GroupTheory.CComponent.QuasisimpleFactors

/-!
# Detecting an escaping odd factor in a theta subgroup

The ordinary layer of H/O₂(H) lifts to C-components of H. If those
components stay in M, but a theta preimage does not, one of its odd
supercritical factors escapes. The two-residual lifts have the same
quotient images, so an escaping factor gives the literal source witness.
Source: Aschbacher--Smith 13.1.6, printed p.868.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta
open Chapter1 ChapterG.Section08
variable {G : Type*} [Group G] [Finite G]

/-- The full preimage of a member of Θ(H/O₂(H)), embedded in G. -/
def preimage (H : Subgroup G) (θ : Subgroup (XiQuotient H)) : Subgroup G :=
  (θ.comap (QuotientGroup.mk' (pCore 2 H))).map H.subtype

omit [Finite G] in
theorem preimage_le (H : Subgroup G) (θ : Subgroup (XiQuotient H)) :
    preimage H θ ≤ H := map_subtype_le _

omit [Finite G] in
theorem core_le_preimage (H : Subgroup G) (θ : Subgroup (XiQuotient H)) :
    H.pCoreIn 2 ≤ preimage H θ := by
  apply map_mono
  intro x hx
  change QuotientGroup.mk' (pCore 2 H) x ∈ θ
  change (x : H ⧸ pCore 2 H) ∈ θ
  rw [(QuotientGroup.eq_one_iff x).mpr hx]
  exact θ.one_mem

omit [Finite G] in
theorem preimage_image (H : Subgroup G) (θ : Subgroup (XiQuotient H)) :
    ChapterA.Section04.twoCoreQuotientImage H (preimage H θ) = θ := by
  unfold ChapterA.Section04.twoCoreQuotientImage preimage
  rw [subgroupOf,comap_map_eq_self_of_injective H.subtype_injective]
  exact map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

/-- Ordinary quotient components lift into the supplied C-component cover. -/
theorem layer_le_image_of_components_le {H M : Subgroup G}
    (hcomp : ∀ C ∈ cComponentsIn H, C ≤ M) :
    componentLayer (XiQuotient H) ≤
      (M.subgroupOf H).map (QuotientGroup.mk' (pCore 2 H)) := by
  let : Group.IsNilpotent (pCore 2 H) := pCore_isNilpotent
  apply sSup_le
  intro C hC
  obtain ⟨B,hB,he⟩ := hC.isCComponent.exists_map_quotient_eq (pCore 2 H)
  rw [← he]
  apply map_mono
  have hBM : B.map H.subtype ≤ M := hcomp _ ⟨map_subtype_le _,by
    rw [subgroupOf,comap_map_eq_self_of_injective H.subtype_injective]
    exact hB⟩
  intro b hb
  exact hBM (mem_map_of_mem H.subtype hb)

/-- An outside theta preimage has an outside odd two-perfect factor. -/
theorem exists_factor_outside {H M : Subgroup G}
    {θ : Subgroup (XiQuotient H)} (hθ : IsThetaSubgroup θ)
    (hcore : H.pCoreIn 2 ≤ M) (hcomp : ∀ C ∈ cComponentsIn H, C ≤ M)
    (hout : ¬ preimage H θ ≤ M) :
    ∃ d : ℕ, d.Prime ∧ Odd d ∧
      ∃ D : Subgroup (pCore d (XiQuotient H)),
        IsSupercriticalPSubgroup d D ∧ ¬ factor H d D ≤ M := by
  obtain ⟨D,hD,rfl⟩ := hθ
  have ho (p : FittingPrimes (XiQuotient H)) : Odd p.val := by
    have hf := fitting_odd_of_twoCore_eq_bot (pCore_quotient_pCore_eq_bot 2 (G := H))
    exact hf.of_dvd_nat p.property.2
  by_contra hn
  push Not at hn
  have hfac (p : FittingPrimes (XiQuotient H)) : factor H p.val (D p) ≤ M :=
    hn p.val p.property.1 (ho p) (D p) (hD p)
  let q := QuotientGroup.mk' (pCore 2 H)
  have hE (p : FittingPrimes (XiQuotient H)) :
      (D p).map (pCore p.val (XiQuotient H)).subtype ≤ (M.subgroupOf H).map q := by
    let : Fact p.val.Prime := ⟨p.property.1⟩
    rw [← factor_image H (ho p) (D p)]
    apply map_mono
    intro y hy
    exact hfac p (mem_map_of_mem H.subtype hy)
  have hθM : componentLayer (XiQuotient H) ⊔
      ⨆ p, (D p).map (pCore p.val (XiQuotient H)).subtype ≤ (M.subgroupOf H).map q :=
    sup_le (layer_le_image_of_components_le hcomp) (iSup_le hE)
  apply hout
  apply map_le_iff_le_comap.mpr
  have hh := comap_mono (f := q) hθM
  rw [comap_map_eq,QuotientGroup.ker_mk'] at hh
  exact hh.trans (sup_le le_rfl (fun x hx => hcore (mem_map_of_mem H.subtype hx)))

/-- The actual source consumer of the escaping theta factor. The global
intersection argument must still provide the outside theta preimage. -/
theorem witness_of_preimage_outside {T : Sylow 2 G} {L H : Subgroup G}
    {θ : Subgroup (XiQuotient H)} (hθ : IsThetaSubgroup θ)
    (hcore : H.pCoreIn 2 ≤ normalizer (L : Set G))
    (hcomp : ∀ C ∈ cComponentsIn H, C ≤ normalizer (L : Set G))
    (hcent : centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      normalizer (L : Set G))
    (hout : ¬ preimage H θ ≤ normalizer (L : Set G)) :
    ∃ Y : Subgroup G, Witness T L H Y ∧ OddShape Y := by
  obtain ⟨d,hd,ho,D,hD,houtD⟩ := exists_factor_outside hθ hcore hcomp hout
  let : Fact d.Prime := ⟨hd⟩
  exact ⟨factor H d D,witness_of_factor_outside ho hD hcore hcent houtD,
    factor_oddShape ho hD hcore houtD⟩

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.Theta
