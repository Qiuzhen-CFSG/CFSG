module
public import Stellmacher.SectionEight.GeneratedContext
public import Stellmacher.SectionFiveToSeven.HypothesisTwoToSectionSeven
public import Stellmacher.SectionFiveToSeven.Result7_6.LocalFacts
public import BenderSuzuki.External.Huppert.IV.Basic

/-!
# The characteristic Sylow obstruction in Stellmacher (8.3)

A native local group F has a supplied Sylow two-subgroup whose ambient image
lies in the edge Sylow and is normalized by the next stabilizer. If F together
with the specified edge Sylow generates the initial stabilizer, no nontrivial
characteristic subgroup of that supplied Sylow has normal image in F. The
original wrapper specializes the image to the next critical-path core.
The injection companion accepts nested native groups with their exact map
into the ambient group, retaining both subgroup wrappers. The supplemental
local-context theorems use only the genuine Section Seven hypotheses. The
legacy declarations retain their exact signatures through `toLocalContext`.

Transport the characteristic subgroup through the exact Sylow-image
equivalence. Its ambient image is normalized by the next stabilizer, since
that stabilizer normalizes B and the transported subgroup is characteristic
in B. If its native image were normal in F,
the initial stabilizer would normalize it as well. The actual edge endpoint
identities and the generation hypothesis make the image a normal two-subgroup
of the ambient group, whose two-core is trivial. Its two-group property comes
from the supplied native Sylow and its image, without requiring an ambient
Sylow containing the edge subgroup. Injectivity then reflects
triviality to the original subgroup. No centrality assumption is needed.

Source: Stellmacher, Journal of Algebra 190 (1997), (8.3), journal p.38;
refs/latex/stellmacher-n-group.tex, the hypothesis used to apply (2.4).
-/

namespace Stellmacher.SectionEight
open Stellmacher.Later Stellmacher.SectionsFiveToSeven CosetGraphContext
/-- A next-stabilizer-normalized Sylow image has the characteristic obstruction. -/
public theorem eight_three_normalized_image_obstruction_of_injective_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (B : Subgroup H) (hBS : B ≤ S)
    (hPbB : GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (B : Set H))
    {F : Type*} [Group F] (f : F →* H) (hf : Function.Injective f)
    (T : Sylow 2 F)
    (hT : (T : Subgroup F).map f = B)
    (hgen : f.range ⊔ S = GAt ctx.Γ ctx.criticalPath.a) :
    ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup F).subtype).Normal := by
  classical
  let h := ctx.sectionSeven
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let Q := B
  let Pa := stabilizer Γ cp.a
  let Pb := stabilizer Γ cp.firstStep
  have hSPb : S ≤ Pb := (SevenSix.edge_sylow_data h Γ cp).2.1
  have hPbQ : Pb ≤ Subgroup.normalizer (Q : Set H) := hPbB
  let e : T ≃* Q :=
    ((T : Subgroup F).equivMapOfInjective f hf).trans
      (MulEquiv.subgroupCongr hT)
  have he (x : T) : ((e x : Q) : H) = f (x : F) := by
    simp only [e, MulEquiv.trans_apply]
    rw [MulEquiv.subgroupCongr_apply]
    exact Subgroup.coe_equivMapOfInjective_apply _ _ _ x
  intro K hKchar hKne hKnormal
  let KQ : Subgroup Q := K.map e.toMonoidHom
  have hKQchar : KQ.Characteristic := by
    rw [Subgroup.characteristic_iff_map_le]
    intro φ x hx
    obtain ⟨y, hy, rfl⟩ := hx
    obtain ⟨k, hk, rfl⟩ := hy
    let ψ : T ≃* T := e.trans (φ.trans e.symm)
    have hψK := (Subgroup.characteristic_iff_map_le.mp hKchar) ψ
    exact ⟨ψ k, hψK ⟨k, hk, rfl⟩, e.apply_symm_apply _⟩
  let X : Subgroup H := KQ.map Q.subtype
  have hXF : X = (K.map (T : Subgroup F).subtype).map f := by
    dsimp only [X, KQ]
    rw [Subgroup.map_map, Subgroup.map_map]
    apply congrArg (fun f => K.map f)
    ext x
    exact he x
  have hXQ : X ≤ Q := Subgroup.map_subtype_le _
  have hPbX : Pb ≤ Subgroup.normalizer (X : Set H) := by
    let _ : KQ.Characteristic := hKQchar
    exact hPbQ.trans
      (BenderSuzuki.External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic Q KQ)
  have hFX : f.range ≤ Subgroup.normalizer (X : Set H) := by
    apply Subgroup.le_normalizer_iff.mpr
    rintro _ ⟨g, rfl⟩ x hx
    rw [hXF] at hx ⊢
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨g * y * g⁻¹, hKnormal.conj_mem y hy g, by simp⟩
  have hPaX : Pa ≤ Subgroup.normalizer (X : Set H) := by
    change f.range ⊔ S = Pa at hgen
    rw [← hgen]
    exact sup_le hFX (hSPb.trans hPbX)
  have hcover : Pa ⊔ Pb = ⊤ := by
    rcases cp.edge_stabilizers_are_P with hedge | hedge
    · rw [show Pa = P1 from hedge.1,show Pb = P2 from hedge.2,ctx.sectionSeven.generated]
    · rw [show Pa = P2 from hedge.1,show Pb = P1 from hedge.2,sup_comm,ctx.sectionSeven.generated]
  have hXN : X.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    apply top_unique
    rw [← hcover]
    exact sup_le hPaX hPbX
  have _hQS : Q ≤ S := hBS
  have hQ2 : IsPGroup 2 Q := by
    change IsPGroup 2 B
    rw [← hT]
    exact T.isPGroup'.map f
  have hX2 : IsPGroup 2 X := hQ2.to_le hXQ
  have hXbot : X = ⊥ := by
    apply le_bot_iff.mp
    exact (show X ≤ pCore 2 H from le_sSup ⟨hXN,hX2⟩).trans_eq h.twoCore_eq_bot
  apply hKne
  apply (Subgroup.map_eq_bot_iff_of_injective K (f := e.toMonoidHom) e.injective).mp
  exact (Subgroup.map_eq_bot_iff_of_injective KQ Q.subtype_injective).mp hXbot

/-- A next-stabilizer-normalized Sylow image has the characteristic obstruction. -/
public theorem eight_three_normalized_image_obstruction_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (B : Subgroup H) (hBS : B ≤ S)
    (hPbB : GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (B : Set H))
    (F : Subgroup H) (T : Sylow 2 F)
    (hT : (T : Subgroup F).map F.subtype = B)
    (hgen : F ⊔ S = GAt ctx.Γ ctx.criticalPath.a) :
    ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup F).subtype).Normal := by
  apply eight_three_normalized_image_obstruction_of_injective_local ctx B hBS hPbB
    F.subtype F.subtype_injective T hT
  simpa only [Subgroup.range_subtype] using hgen

/-- The exact characteristic-subgroup obstruction for the local (2.4) application. -/
public theorem eight_three_characteristic_obstruction_local
    {H : Type*} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (F : Subgroup H) (T : Sylow 2 F)
    (hT : (T : Subgroup F).map F.subtype = QAt ctx.Γ ctx.criticalPath.firstStep)
    (hgen : F ⊔ S = GAt ctx.Γ ctx.criticalPath.a) :
    ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup F).subtype).Normal := by
  let h := ctx.sectionSeven
  exact eight_three_normalized_image_obstruction_local ctx _
    (SevenSix.local_cores_le_edge_sylow h ctx.Γ ctx.criticalPath).2
    (SevenSix.stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.firstStep)
    F T hT hgen

/-- A next-stabilizer-normalized Sylow image has the characteristic obstruction. -/
public theorem eight_three_normalized_image_obstruction_of_injective
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (B : Subgroup H) (hBS : B ≤ S)
    (hPbB : GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (B : Set H))
    {F : Type*} [Group F] (f : F →* H) (hf : Function.Injective f)
    (T : Sylow 2 F)
    (hT : (T : Subgroup F).map f = B)
    (hgen : f.range ⊔ S = GAt ctx.Γ ctx.criticalPath.a) :
    ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup F).subtype).Normal := by
  exact eight_three_normalized_image_obstruction_of_injective_local
    ctx.toLocalContext B hBS hPbB f hf T hT hgen

/-- A next-stabilizer-normalized Sylow image has the characteristic obstruction. -/
public theorem eight_three_normalized_image_obstruction
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (B : Subgroup H) (hBS : B ≤ S)
    (hPbB : GAt ctx.Γ ctx.criticalPath.firstStep ≤ Subgroup.normalizer (B : Set H))
    (F : Subgroup H) (T : Sylow 2 F)
    (hT : (T : Subgroup F).map F.subtype = B)
    (hgen : F ⊔ S = GAt ctx.Γ ctx.criticalPath.a) :
    ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup F).subtype).Normal := by
  exact eight_three_normalized_image_obstruction_local ctx.toLocalContext B hBS hPbB F T hT hgen

/-- The exact characteristic-subgroup obstruction for the local (2.4) application. -/
public theorem eight_three_characteristic_obstruction
    {H : Type*} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (F : Subgroup H) (T : Sylow 2 F)
    (hT : (T : Subgroup F).map F.subtype = QAt ctx.Γ ctx.criticalPath.firstStep)
    (hgen : F ⊔ S = GAt ctx.Γ ctx.criticalPath.a) :
    ∀ K : Subgroup T, K.Characteristic → K ≠ ⊥ →
      ¬ (K.map (T : Subgroup F).subtype).Normal := by
  exact eight_three_characteristic_obstruction_local ctx.toLocalContext F T hT hgen
end Stellmacher.SectionEight
