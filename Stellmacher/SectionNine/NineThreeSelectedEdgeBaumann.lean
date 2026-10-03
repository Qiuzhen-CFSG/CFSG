module
public import Stellmacher.SectionNine.NineTwoAmbientSetup
public import Stellmacher.SectionFiveToSeven.Result6_1
public import Stellmacher.BaumannMap

/-!
# Baumann noncontainment for the selected second edge in (9.3)

For the genuine ambient Section Nine context, choose any Sylow two-subgroup
of the edge joining the first-step vertex to a supplied neighbor. Its
Baumann subgroup is not contained in the first-step core. This is exactly
the hypothesis required by the prescribed-actor, selected-Baumann version
of (7.8) for the second extraction in (9.3).

The edge Sylow theorem makes the selected subgroup a Sylow image inside
the first-step stabilizer. Sylow conjugacy there transports a hypothetical
Baumann containment to the Sylow whose graph image is the distinguished T;
normality of the two-core preserves that containment. Injective Baumann
transport through the actual embedding maps T to S. The ambient orientation
identifies the first-step stabilizer with P₂, and its intrinsic two-core
maps into O₂(P₂). This contradicts the proved Baumann noncontainment (6.1).

The supplied edge Sylow is preserved. No residual assertion is made about
several different Sylow choices, and Hypothesis Two stays on the ambient H.
Source: Stellmacher (9.3)(3), Journal of Algebra 190 (1997), p.49, using
(6.1), (7.3), and (7.8), `refs/files/stellmacher-n-group.pdf`.
-/
namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

private theorem sylow_baumann_core_transfer
    {G : Type u} [Group G] [Finite G] (U V : Sylow 2 G)
    (hU : baumannIn (U : Subgroup G) ≤ pCore 2 G) :
    baumannIn (V : Subgroup G) ≤ pCore 2 G := by
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq G U V
  have hV : (V : Subgroup G) = (U : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [← hg,Sylow.coe_subgroup_smul,Subgroup.pointwise_smul_def]
    congr 1
  have hBm : (baumannIn (U : Subgroup G)).map (MulAut.conj g).toMonoidHom =
      baumannIn (V : Subgroup G) := by
    rw [hV]
    exact baumann_map_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective _
  rw [← hBm]
  rintro a ⟨u,hu,rfl⟩
  exact (inferInstance : (pCore 2 G).Normal).conj_mem u (hU hu) g

public theorem nine_three_selected_edge_baumann_not_le_core
    {H : Type u} [Group H] [Finite H]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {G : Type u} [Group G] [Finite G]
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (l : ctx.Γ.Vertex) (hl : l ∈ neighborhood ctx.Γ ctx.criticalPath.firstStep)
    (U : Sylow 2 ↥(stabilizer ctx.Γ ctx.criticalPath.firstStep ⊓ stabilizer ctx.Γ l)) :
    ¬ baumannIn (sylowTwoAmbient
      (stabilizer ctx.Γ ctx.criticalPath.firstStep ⊓ stabilizer ctx.Γ l) U) ≤
      q ctx.Γ ctx.criticalPath.firstStep := by
  let P := stabilizer ctx.Γ ctx.criticalPath.firstStep
  let W := sylowTwoAmbient (P ⊓ stabilizer ctx.Γ l) U
  obtain ⟨_,_,hmapP,_⟩ := nine_two_ambient_setup ctx
  have hW : IsSylowTwoIn W P :=
    ((lemma_seven_three ctx.sectionSeven ctx.Γ).sylow_and_core _ _ hl U).1
  obtain ⟨_,R,hR⟩ := hW
  obtain ⟨_,R0,hR0⟩ := (edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  have hBm (V : Sylow 2 P) :
      (baumannIn (V : Subgroup P)).map P.subtype =
        baumannIn ((V : Subgroup P).map P.subtype) :=
    baumann_map_injective P.subtype P.subtype_injective _
  intro hbad
  rw [q,ctx.Γ.twoCoreAt_def] at hbad
  have hRbad : baumannIn (R : Subgroup P) ≤ pCore 2 P := by
    apply (Subgroup.map_le_map_iff_of_injective P.subtype_injective).mp
    rw [hBm,hR]
    exact hbad
  have hR0bad := sylow_baumann_core_transfer R R0 hRbad
  have hTbad : baumannIn T ≤ twoCoreIn P := by
    have hm := Subgroup.map_mono (f := P.subtype) hR0bad
    rw [hBm,hR0] at hm
    exact hm
  let f : P →* P2 := (embedding.comp P.subtype).codRestrict P2 (fun p =>
    hmapP ▸ Subgroup.mem_map_of_mem embedding p.property)
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨g,hg,hgp⟩ := Subgroup.mem_map.mp (hmapP.ge p.property)
    exact ⟨⟨g,hg⟩,Subtype.ext hgp⟩
  have hcoremap : (twoCoreIn P).map embedding ≤ twoCoreIn P2 := by
    change ((pCore 2 P).map P.subtype).map embedding ≤ (pCore 2 P2).map P2.subtype
    rw [Subgroup.map_map]
    have he : embedding.comp P.subtype = P2.subtype.comp f := rfl
    rw [he,← Subgroup.map_map]
    apply Subgroup.map_mono
    exact le_sSup ⟨pCore_normal.map f hf,pCore_isPGroup.map f⟩
  have hBmap : (baumannIn T).map embedding = baumannIn S := by
    rw [show (baumannIn T).map embedding = baumannIn (T.map embedding) from
      baumann_map_injective embedding ctx.embedding_injective T,ctx.map_S]
  have hBS : baumannIn S ≤ twoCoreIn P2 := by
    rw [← hBmap]
    exact (Subgroup.map_mono hTbad).trans hcoremap
  exact lemma_six_one S0 S P1 P2 ctx.hypothesisTwo hBS
end Stellmacher.SectionNine
