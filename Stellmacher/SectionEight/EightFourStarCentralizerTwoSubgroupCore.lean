module
public import Stellmacher.SectionEight.EightFourStarCentralizerCore
public import Theory.GroupTheory.SubgroupConjugation

/-!
# Two-subgroups centralizing the first star lie in the first core

Any 2-subgroup D of the first-step stabilizer that centralizes the actual
initial star closure can be conjugated into the distinguished edge Sylow.
The star closure is normal in the stabilizer, so this conjugation preserves
centralization. Applying the exact edge-Sylow centralizer theorem and then
transporting the first core back (using its graph-action covariance) gives
D≤Q_first. This is the source-(8) interface where Q_end is known inside the
first stabilizer but need not lie in the distinguished Sylow.

No false edge-Sylow containment is assumed and no length-two hypothesis is
needed. The local theorem uses the same Section Seven graph and supplied
quotient witness. Its original canonical API is an exact wrapper through
that local context. Source: Stellmacher (8.4), Journal of Algebra190 (1997), p39.
-/

namespace Stellmacher.SectionEight
open Later SectionsFiveToSeven CosetGraphContext
universe u
/-- Every two-subgroup of the first stabilizer centralizing the initial star lies in its core. -/
public theorem eight_four_star_centralizer_two_subgroup_core_local
    {H : Type u} [Group H] [Finite H]
    {S P1 P2 : Subgroup H}
    (ctx : SectionEightLocalContext H S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (D : Subgroup H) (hDP : D ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : IsPGroup 2 D)
    (hDC : ⁅D,(Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype⁆ = ⊥) :
    D ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let F := w.oneJFixedPoints S
  let C0 := Subgroup.normalClosure (F.subgroupOf P : Set P)
  let C := C0.map P.subtype
  let h := ctx.sectionSeven
  obtain ⟨_,U,hU⟩ := (SevenSix.edge_sylow_data h Γ cp).2
  obtain ⟨T,hDT⟩ := (hD.comap_subtype (K := P)).exists_le_sylow
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq P T U
  let e := MulAut.conj (g : H)
  have hDmS : D.map e.toMonoidHom ≤ S := by
    rintro x ⟨d,hd,rfl⟩
    have hdT : (⟨d,hDP hd⟩ : P) ∈ (T : Subgroup P) := hDT hd
    have hdU : g * (⟨d,hDP hd⟩ : P) * g⁻¹ ∈ (U : Subgroup P) := by
      rw [← hg]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hdT
    rw [← hU]
    exact Subgroup.mem_map_of_mem P.subtype hdU
  have hCn : (C.subgroupOf P).Normal := by
    change ((C0.map P.subtype).comap P.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective P.subtype_injective]
    infer_instance
  have hPC : P ≤ Subgroup.normalizer (C : Set H) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le C0)).mp hCn
  have hCm : C.map e.toMonoidHom = C :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPC g.property)
  have hDCm : ⁅D.map e.toMonoidHom,C⁆ = ⊥ := by
    have hh := congrArg (Subgroup.map e.toMonoidHom) hDC
    rw [Subgroup.map_commutator,Subgroup.map_bot] at hh
    change ⁅D.map e.toMonoidHom,C.map e.toMonoidHom⁆ = ⊥ at hh
    rwa [hCm] at hh
  have hbound := eight_four_star_centralizer_core_local ctx hcenter w hbranch
    (D.map e.toMonoidHom) hDmS hDCm
  have hQm : (QAt Γ cp.firstStep).map e.toMonoidHom = QAt Γ cp.firstStep := by
    have hfix : Γ.act (g : H)⁻¹ cp.firstStep = cp.firstStep :=
      (Set.ext_iff.mp (Γ.stabilizer_def cp.firstStep) (g : H)⁻¹).mp
        (P.inv_mem g.property)
    have hh := SevenSix.q_act Γ (g : H)⁻¹ cp.firstStep
    rw [hfix,inv_inv] at hh
    exact hh.symm
  rw [← hQm] at hbound
  exact (Subgroup.map_le_map_iff_of_injective e.injective).mp hbound

/-- Canonical specialization preserving the supplied subgroup and star. -/
public theorem eight_four_star_centralizer_two_subgroup_core
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    (ctx : SectionEightContext H S0 S P1 P2)
    (hcenter : ZAt ctx.Γ ctx.criticalPath.firstStep ≤
      CenterAmbient (GAt ctx.Γ ctx.criticalPath.firstStep))
    (w : QuotientModuleWitness
      (GAt ctx.Γ ctx.criticalPath.a)
      (GAt ctx.Γ ctx.criticalPath.a ⊓
        Subgroup.centralizer (ZAt ctx.Γ ctx.criticalPath.a : Set H))
      (ZAt ctx.Γ ctx.criticalPath.a))
    (hbranch : (Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype ≠ w.oneJFixedPoints S)
    (D : Subgroup H) (hDP : D ≤ GAt ctx.Γ ctx.criticalPath.firstStep)
    (hD : IsPGroup 2 D)
    (hDC : ⁅D,(Subgroup.normalClosure
      ((w.oneJFixedPoints S).subgroupOf (GAt ctx.Γ ctx.criticalPath.firstStep) :
        Set (GAt ctx.Γ ctx.criticalPath.firstStep))).map
          (GAt ctx.Γ ctx.criticalPath.firstStep).subtype⁆ = ⊥) :
    D ≤ QAt ctx.Γ ctx.criticalPath.firstStep := by
  exact eight_four_star_centralizer_two_subgroup_core_local ctx.toLocalContext hcenter w hbranch D hDP hD hDC
end Stellmacher.SectionEight
