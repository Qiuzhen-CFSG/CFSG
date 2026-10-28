module

public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.EndpointGeometry.Generation
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Five.Localization.SecondActor.Faithfulness
public import Theory.GroupTheory.SylowKernelCore

/-!
# Generation across the original terminal edge

Write E = Gγ,γb−1 and let e be the actual critical-pair conjugator.
F.9.13 identifies E with (L₁T)^e and places U_H in O₂(E). Thus the
pulled-back actor B = e⁻¹(U_H) lies in O₂(L₁T). The descended action
on U_H/V₁ shows that B cannot lie in O₂(H): otherwise U_H would
centralize Uγ/A₁, contradicting D_H < U_H from 13.8.8(2).

The intersection O₂(L₁T)* ∩ C_H*(P*) is a normal two-subgroup of H*,
which has trivial two-core. The parabolic-core centralizer theorem
therefore makes B* faithful on P*, so [P*,B*] is nontrivial. The five-factor
calculation makes P* elementary abelian; irreducibility forces P* into the normal closure
of B*. The proved base-generation lemma then gives H = ⟨B^H⟩(L₁T).
Mapping this equality by e gives the required seed U_H and exactly E.

The final conditional theorem takes ReducedFive, RankOneFactors, and
four precise earlier source consequences: F.9.13(1), the U_H-containment
following from F.9.13(2), the Sylow consequence O₂(H) ≤ L₁T, and the
strict denominator in 13.8.8(2). The genuine standing setup and minimal
solvable Hz membership supply these inputs in the source assembly.
The reversed actor's movement and its invariant-subgroup consequence
are proved here; no reversed critical-path construction is needed for
this generation equality.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 13.8.13,
printed p.951 (PDF p.968), the paragraph beginning “Therefore”, with
F.9.13(1)–(2), printed p.322, and 13.8.8(2), printed p.949.
-/

@[expose] public section

open Subgroup
open CFSG.Quasithin.Chapter13.Section08
open CriticalGeometry
namespace CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry
variable {G : Type*} [Group G]

private theorem starImage_eq_bot_iff {H B : Subgroup G} (hBH : B ≤ H) :
    Source.starImage H B = ⊥ ↔ B ≤ Source.QH H := by
  have hc : (Source.QH H).subgroupOf H = pCore 2 H :=
    comap_map_eq_self_of_injective H.subtype_injective _
  rw [Source.starImage, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk', ← hc]
  exact ⟨fun h b hb => h (show (⟨b, hBH hb⟩ : H) ∈ B.subgroupOf H from hb),
    fun h _ hb => h hb⟩

/-- Descent through the actual two-core makes its commutators vanish modulo Z. -/
theorem core_commutator_le {H U Z : Subgroup G} [(Z.subgroupOf U).Normal]
    (a : StarAction H U Z) : ⁅Source.QH H, U⁆ ≤ Z := by
  have hQH : Source.QH H ≤ H := pCoreIn_le 2 H
  have hactors : a.actors (Source.QH H) = ⊥ := by
    rw [StarAction.actors, (starImage_eq_bot_iff hQH).mpr le_rfl, Subgroup.map_bot]
  have hbot : commutatorAction (a.actors (Source.QH H)) (U ⧸ Z.subgroupOf U) = ⊥ := by
    rw [hactors, commutatorAction_eq_closure]
    apply le_bot_iff.mp
    rw [closure_le]
    rintro _ ⟨b, w, rfl⟩
    have hb : (b : MulAut (U ⧸ Z.subgroupOf U)) = 1 := b.property
    change w⁻¹ * (b : MulAut _) w ∈ (⊥ : Subgroup _)
    simp only [hb, MulAut.one_apply, inv_mul_cancel, one_mem]
  rw [a.commutatorAction_eq_tildeImage _ hQH, tildeImage, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hbot
  rw [commutator_comm]
  have hcomm : ⁅U, Source.QH H⁆ ≤ U :=
    le_normalizer_iff_commutator_le_left.mp (hQH.trans a.normalizes)
  intro x hx
  exact hbot (show (⟨x, hcomm hx⟩ : U) ∈ ⁅U, Source.QH H⁆.subgroupOf U from hx)

private theorem map_span (e : G ≃* G) (B H : Subgroup G) :
    (conjugateSpanBy B H).map e.toMonoidHom =
      conjugateSpanBy (B.map e.toMonoidHom) (H.map e.toMonoidHom) := by
  rw [conjugateSpanBy, MonoidHom.map_closure, conjugateSpanBy]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨h, hh, b, hb, rfl⟩, rfl⟩
    exact ⟨e h, mem_map_of_mem _ hh, e b, mem_map_of_mem _ hb,
      by simp only [map_mul, map_inv]; rfl⟩
  · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨h * b * h⁻¹, ⟨h, hh, b, hb, rfl⟩, by simp only [map_mul, map_inv]⟩

/-- A nontrivial star image in the parabolic two-core must move P*. -/
theorem core_actor_moves [Finite G] {H L₁ T M Vα B : Subgroup G}
    (r : ReducedFive H L₁ T M Vα)
    (hB : B ≤ (L₁ ⊔ T).pCoreIn 2) (hnot : ¬ B ≤ Source.QH H) :
    ⁅Source.starImage H r.P, Source.starImage H B⁆ ≠ ⊥ := by
  have hBH : B ≤ H := hB.trans ((pCoreIn_le 2 _).trans (r.generated ▸ le_sup_right))
  have hBstar : Source.starImage H B ≤ Source.starImage H ((L₁ ⊔ T).pCoreIn 2) :=
    map_mono (fun _ hx => hB hx)
  intro hcomm
  rw [commutator_comm] at hcomm
  have hcentral := commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hzero : Source.starImage H B = ⊥ := by
    apply le_bot_iff.mp
    rw [← SecondActor.parabolic_core_star_centralizer r]
    exact le_inf hBstar hcentral
  exact hnot ((starImage_eq_bot_iff hBH).mp hzero)

/-- The original terminal edge is the stored conjugate of the base edge. -/
theorem terminal_edge_eq_map {L T H V L₁ : Subgroup G}
    (c : CriticalPair L T H V)
    (hbase : edgeGroup L T H (base L T H false) (base L T H true) = L₁ ⊔ T) :
    edgeGroup L T H c.gamma c.previous =
      (L₁ ⊔ T).map (MulAut.conj (c.gb : G)).toMonoidHom := by
  have he : (L ⊔ T) ⊓ H = L₁ ⊔ T := by
    simpa [edgeGroup, vertexGroup_base] using hbase
  rw [edgeGroup, c.vertexGroup_gamma, CriticalPair.previous, ← c.gb_zero,
    vertexGroup_smul, vertexGroup_base]
  change H.map _ ⊓ (L ⊔ T).map _ = _
  rw [← map_inf _ _ _ (MulAut.conj (c.gb : G)).injective, inf_comm, he]

/-- The pulled-back U_H has nontrivial star image, by the strict source denominator. -/
theorem reversed_actor_not_le_core {L T H V V₃ V₁ : Subgroup G}
    (c : CriticalPair L T H V) [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (a : StarAction H (Source.UH H V₃) V₁)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃) :
    ¬ (Source.UH H V₃).map (MulAut.conj (c.gb : G)).symm.toMonoidHom ≤ Source.QH H := by
  intro hcore
  let e := MulAut.conj (c.gb : G)
  have hback : ((Source.UH H V₃).map e.symm.toMonoidHom).map e.toMonoidHom =
      Source.UH H V₃ := (map_symm_eq_iff_map_eq _ (e := e)).mp rfl
  have hcomm := map_mono (f := e.toMonoidHom)
    ((commutator_mono hcore le_rfl).trans (core_commutator_le a))
  rw [map_commutator, hback] at hcomm
  exact hproper.not_ge (le_commutatorPreimage le_rfl hcomm)

/-- The endpoint-generation equality in the five-primary branch of 13.8.13.
`hbase` and `hedge` are the earlier F.9.13 edge facts; `hcore` follows
from T being Sylow in H, and `hproper` is 13.8.8(2). The original seed
and terminal edge are retained through the actual conjugator. -/
theorem endpoint_generation [Finite G] {L T H V V₃ V₁ L₁ M Vα : Subgroup G}
    (c : CriticalPair L T H V) [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (a : StarAction H (Source.UH H V₃) V₁)
    (r : ReducedFive H L₁ T M Vα) (f : RankOneFactors a r.P (c.Ugamma V₃))
    (hbase : edgeGroup L T H (base L T H false) (base L T H true) = L₁ ⊔ T)
    (hedge : Source.UH H V₃ ≤ (edgeGroup L T H c.gamma c.previous).pCoreIn 2)
    (hcore : Source.QH H ≤ L₁ ⊔ T)
    (hproper : Source.DH (Source.UH H V₃) (c.Ugamma V₃) (c.Aone V₁) < Source.UH H V₃) :
    vertexGroup L T H c.gamma =
      conjugateSpanBy (Source.UH H V₃) (vertexGroup L T H c.gamma) ⊔
        edgeGroup L T H c.gamma c.previous := by
  let e := MulAut.conj (c.gb : G)
  let B := (Source.UH H V₃).map e.symm.toMonoidHom
  have hback : B.map e.toMonoidHom = Source.UH H V₃ :=
    (map_symm_eq_iff_map_eq _ (e := e)).mp rfl
  have hB : B ≤ (L₁ ⊔ T).pCoreIn 2 := by
    apply (map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
    rw [hback, map_pCoreIn_of_injective 2 _ _ e.injective,
      ← terminal_edge_eq_map c hbase]
    exact hedge
  have hBH : B ≤ H := hB.trans ((pCoreIn_le 2 _).trans (r.generated ▸ le_sup_right))
  have hmove := core_actor_moves r hB (reversed_actor_not_le_core c a hproper)
  have hgen := congrArg (Subgroup.map e.toMonoidHom)
    (base_generation_of_moves a r f.factors hBH hcore hmove)
  rw [Subgroup.map_sup, map_span, hback, ← c.vertexGroup_gamma,
    ← terminal_edge_eq_map c hbase] at hgen
  exact hgen

end CFSG.Quasithin.Chapter13.Section08.SolvableExclusion.Five.Localization.EndpointGeometry

end
