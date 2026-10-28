module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced.Inputs
public import Theory.GroupTheory.PPerfectHom

/-!
# Reducedness for the full diagonal-centralizer action

Pull O₂(G_z/C_Gz(V_z)) back to G_z and intersect with T. If this
intersection lies in T₁, it fixes E; equality of quotient images shows
the whole pullback fixes E. Normality then makes it fix V_z. Otherwise
the local commutator calculation forces X into the pullback. Since X is
two-perfect its image is trivial, and the local residual calculation makes
X normal in G_z, contrary to X<K_z.

This proves 10.2.11(2) conditional only on the separate local seed analysis.
The quotient is the full G_z/C_Gz(V_z), not the action of K_z T.
Source: Aschbacher--Smith, printed p.753.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  {D : FundamentalSetup KnownSimple.IsKnownSimple T L}
  {s : SourceLinearThreeSurvivor T D} {a b : G}
namespace Configuration
variable (c : Configuration s a b) (h : SeedAnalysis c)
include c

omit [Finite G] c in
/-- The literal seed is normal exactly when its G_z span is itself. -/
theorem seed_span_eq_of_normalizes
    (hn : centralizer ({a*b} : Set G) ≤ normalizer (centralizerSeed T L (a*b) : Set G)) :
    componentSpan T L (a*b) = centralizerSeed T L (a*b) :=
  le_antisymm (conjugateSpanBy_le le_rfl hn) (le_conjugateSpanBy _ _)

include h in
/-- The seed normality case of the full-module centralization argument. -/
theorem full_centralizes_of_seed_normalizes
    (hn : centralizer ({a*b} : Set G) ≤ normalizer (centralizerSeed T L (a*b) : Set G)) :
    D.fullModule ≤ centralizer (centralizerModule a b : Set G) := by
  have hXW : centralizerSeed T L (a*b) ≤ centralizer (centralizerModule a b : Set G) :=
    le_centralizer_conjugateSpanBy_of_normalizes _ _ _ hn h.fixes
  have hCW : centralizer ({a*b} : Set G) ≤
      normalizer (centralizer (centralizerModule a b : Set G) : Set G) :=
    (le_normalizer_conjugateSpanBy _ _).trans (normalizer_le_normalizer_centralizer _)
  have hVW := (commutator_mono le_rfl hXW).trans
    (le_normalizer_iff_commutator_le_right.mp (c.full_le.trans hCW))
  have hcentral := c.span_central_core_of_seedJoin_core h.core_bound
  have hWW : centralizerModule a b ≤ centralizer (centralizerModule a b : Set G) :=
    (hcentral.trans inf_le_right).trans (centralizer_le (hcentral.trans inf_le_left))
  exact h.generates.le.trans (sup_le hVW ((le_conjugateSpanBy _ _).trans hWW))

include h in
/-- Source 10.2.11(2), with its full faithful action quotient. -/
theorem reduced_of_seedAnalysis
    (hlt : centralizerSeed T L (a*b) < componentSpan T L (a*b)) :
    IsPReduced 2 ((centralizerModule a b).subgroupOf (centralizer ({a*b} : Set G))) := by
  let H := centralizer ({a*b} : Set G)
  let W := centralizerModule a b
  let X := centralizerSeed T L (a*b)
  let U := W.subgroupOf H
  let : U.Normal := span_normal
  let C := centralizer (U : Set H)
  let q := QuotientGroup.mk' C
  let P := pCore 2 (H ⧸ C)
  let N := P.comap q
  let J := N.map H.subtype
  let R := J ⊓ (T : Subgroup G)
  have hHJ : H ≤ normalizer (J : Set G) := by
    simpa only [J, normalizer_eq_top, ← MonoidHom.range_eq_map, range_subtype]
      using N.le_normalizer_map H.subtype
  have hTR : (T : Subgroup G) ≤ normalizer (R : Set G) :=
    (le_inf (c.sylow_le.trans hHJ) (T : Subgroup G).le_normalizer).trans
      inf_normalizer_le_normalizer_inf
  have hJU : R ≤ (T : Subgroup G) := inf_le_right
  have hWJ : W ≤ centralizer (J : Set G) := by
    by_cases hR : R ≤ (T : Subgroup G) ⊓ normalizer (L : Set G)
    · have hEJ : zpowers a ⊔ zpowers b ≤ centralizer (J : Set G) := by
        have hPC : P ≤ ((T.subtype c.sylow_le : Sylow 2 H) : Subgroup H).map q :=
          pCore_isPGroup.le_sylow_of_normal
            ((T.subtype c.sylow_le).mapSurjective (QuotientGroup.mk'_surjective C))
        have hER : zpowers a ⊔ zpowers b ≤ centralizer (R : Set G) :=
          sup_le (zpowers_le.mpr (centralizer_le hR c.first_fixed))
            (zpowers_le.mpr (centralizer_le hR c.second_fixed))
        intro e he j hj
        obtain ⟨n, hn, rfl⟩ := hj
        obtain ⟨t, ht, heq⟩ := hPC hn
        have htN : t ∈ N := by
          change q t ∈ P
          rw [heq]
          exact hn
        have htJ : (t:G) ∈ J := mem_map_of_mem H.subtype htN
        have htR : (t:G) ∈ R := ⟨htJ, ht⟩
        have hnC : t⁻¹*n ∈ C := by
          apply (QuotientGroup.eq_one_iff _).mp
          change q (t⁻¹*n) = 1
          rw [map_mul, map_inv, heq, inv_mul_cancel]
        have heW : e ∈ W := le_conjugateSpanBy _ _ he
        have hc := congrArg Subtype.val (hnC (⟨e,c.span_le heW⟩ : H) heW)
        have hte := hER he t htR
        change e * ((t:G)⁻¹ * (n:G)) = ((t:G)⁻¹ * (n:G)) * e at hc
        calc
          (n:G) * e = (t:G) * (((t:G)⁻¹ * (n:G)) * e) := by group
          _ = (t:G) * (e * ((t:G)⁻¹ * (n:G))) := by rw [hc]
          _ = e * (n:G) := by rw [← mul_assoc, hte]; group
      exact conjugateSpanBy_le hEJ (hHJ.trans (normalizer_le_normalizer_centralizer _))
    · have hXR : ⁅X,R⁆ = X := h.commutator R hJU hTR hR
      have hXJ : X ≤ J := hXR.symm.le.trans
        ((commutator_mono le_rfl (show R ≤ J from inf_le_left)).trans
          (le_normalizer_iff_commutator_le_right.mp ((seed_le (T := T) (L := L) (a := a) (b := b)).trans hHJ)))
      let f : X →* P := (q.comp (inclusion (seed_le (T := T) (L := L) (a := a) (b := b)))).codRestrict P (by
        intro x
        obtain ⟨n, hn, he⟩ := hXJ x.property
        have hn' : n = inclusion (seed_le (T := T) (L := L) (a := a) (b := b)) x := Subtype.ext he
        change q (inclusion (seed_le (T := T) (L := L) (a := a) (b := b)) x) ∈ P
        rw [← hn']
        exact hn)
      have hf : f = 1 := (isPPerfect_embedded_pResidual 2 _).hom_eq_one_of_isPGroup
        pCore_isPGroup f
      have hXC : X ≤ H ⊓ centralizer (W : Set G) := by
        intro x hx
        refine ⟨(seed_le (T := T) (L := L) (a := a) (b := b)) hx, ?_⟩
        have hh := congrArg (fun k : X →* P => ((k ⟨x,hx⟩ : P) : H ⧸ C)) hf
        have hk : (⟨x,(seed_le (T := T) (L := L) (a := a) (b := b)) hx⟩ : H) ∈ C := (QuotientGroup.eq_one_iff _).mp hh
        intro w hw
        exact congrArg Subtype.val (hk (⟨w,c.span_le hw⟩ : H) hw)
      have hnorm := h.normal_in_kernel (H ⊓ centralizer (W : Set G))
        (le_inf inf_le_left (c.kernel_le_moved_normalizer.trans inf_le_left))
        kernel_normalized hXC
      exact (hlt.ne (seed_span_eq_of_normalizes hnorm).symm).elim
  have hP : P = ⊥ := by
    apply bot_unique
    intro y hy
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective C y
    apply (QuotientGroup.eq_one_iff _).mpr
    intro u hu
    exact Subtype.ext ((hWJ hu g (mem_map_of_mem H.subtype hy)).symm)
  let : IsElementaryAbelian 2 W :=
    c.span_elementary_of_central_core (c.span_central_core_of_seedJoin_core h.core_bound)
  exact ⟨inferInstance, IsElementaryAbelian.subgroupOf c.span_le, hP⟩

end Configuration
end CFSG.Quasithin.Chapter10.SourceLinearThreeReplacement.Geometry.CoreReduced
