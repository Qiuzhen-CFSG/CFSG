module
public import Stellmacher.SectionNine.NineEightNoncontainedNormalizer
public import Stellmacher.UniqueMaximalContainingTransport
public import Stellmacher.UniqueMaximalContainingMap
public import Theory.GroupTheory.ElementaryOddSylowUniqueMaximal

/-!
# The elementary-three obstruction in the noncontained branch of (9.8)

Under the genuine extracted-neighbor hypotheses, assume its center escapes
the initial stabilizer. Then the image of the first-step two-residual in
the ordinary first-step two-core quotient is not elementary abelian at three.
This is the prime-three consequence of the source's stronger assertion (*)
needed by the transvection branch; the literal residual image is retained.

The extracted center and the initial edge generate a proper subgroup of
the first-step stabilizer, by the W normalizer argument. If the residual
image were elementary three, it would be a normal supplement to the
projected Sylow subgroup. Unique maximal containment descends to this
quotient. Coprime invariant-complement theory would then make the projected
Sylow maximal. Its preimage is the original Sylow because the two-core lies
in it. The proper join would consequently be just the Sylow, forcing the
extracted center back into the initial stabilizer.

Source: Stellmacher (9.8), printed p.55/PDF p.45, assertion (*).
-/

namespace Stellmacher.SectionNine
open Later SectionsFiveToSeven CosetGraphContext SevenSix
universe u

public theorem nine_eight_noncontained_residual_image_not_elementary_three
    {H G : Type u} [Group H] [Finite H] [Group G] [Finite G]
    {S0 : Sylow 2 H} {S P1 P2 : Subgroup H}
    {embedding : G →* H} {T A B : Subgroup G}
    (ctx : AmbientSectionNineContext H S0 S P1 P2 embedding T A B)
    (hb : 3 < ctx.criticalPath.length)
    (hcontain : ZAt ctx.Γ ctx.criticalPath.a' ≤ VAt ctx.Γ ctx.criticalPath.firstStep)
    (neighbor : ctx.Γ.Vertex) (hneighbor : neighbor ∈ neighborhood ctx.Γ ctx.criticalPath.a')
    (hindex : QuotientCardEq (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a)
      (GeneratedNeighborhoodV ctx.Γ ctx.criticalPath.a ⊓ GAt ctx.Γ neighbor) 2)
    (hnot : ¬ ZAt ctx.Γ ctx.criticalPath.a ≤ GAt ctx.Γ neighbor)
    (hescape : ¬ ZAt ctx.Γ neighbor ≤ GAt ctx.Γ ctx.criticalPath.a) :
    ¬ IsElementaryAbelian 3
      (((EAt ctx.Γ ctx.criticalPath.firstStep).subgroupOf
        (GAt ctx.Γ ctx.criticalPath.firstStep)).map
        (QuotientGroup.mk' (pCore 2 (GAt ctx.Γ ctx.criticalPath.firstStep)))) := by
  classical
  let Γ := ctx.Γ
  let cp := ctx.criticalPath
  let P := GAt Γ cp.firstStep
  let E := EAt Γ cp.firstStep
  let q := QuotientGroup.mk' (pCore 2 P)
  let R := (E.subgroupOf P).map q
  intro hR
  let _ : IsElementaryAbelian 3 R := hR
  have hEeq : E = twoResidualAmbient P := Γ.twoResidualAt_def cp.firstStep
  have hEP : E ≤ P := by
    rw [hEeq]
    exact Subgroup.map_subtype_le _
  have hEn : (E.subgroupOf P).Normal := by
    rw [hEeq]
    exact twoResidualIn_normal P
  let _ : R.Normal := hEn.map q (QuotientGroup.mk'_surjective _)
  obtain ⟨hTP, U, hU⟩ := (edge_sylow_data ctx.sectionSeven Γ cp).2
  have hUP : (U : Subgroup P) = T.subgroupOf P := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTP]
    exact hU
  have hkerU : q.ker ≤ (U : Subgroup P) := by
    rw [QuotientGroup.ker_mk']
    exact (pCore_isPGroup (p := 2)).le_sylow_of_normal U
  let Ubar := U.mapSurjective (QuotientGroup.mk'_surjective (pCore 2 P))
  have hcomapU : ((U : Subgroup P).map q).comap q = (U : Subgroup P) := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerU]
  have hlocal := (edge_local_data ctx.sectionSeven Γ cp).2
  have hPset := (pFamily_iff_pSet _ _ _).mp hlocal.1
  have huniq : IsUniqueMaximalContaining (U : Subgroup P) ⊤ :=
    native_uniqueMaximalContaining P _ (by rw [hU]; exact hPset.2)
  have hUproper : (U : Subgroup P) ≠ ⊤ := by
    obtain ⟨M,hM,hUM,_⟩ := (uniqueMaximalContaining_top_iff _).mp huniq
    intro htop
    exact hM.ne_top (top_unique (htop ▸ hUM))
  have hUbarProper : (U : Subgroup P).map q ≠ ⊤ := by
    intro htop
    apply hUproper
    rw [← hcomapU,htop,Subgroup.comap_top]
  have huniqBar := uniqueMaximalContaining_map_of_ne_top q
    (QuotientGroup.mk'_surjective _) _ huniq hUbarProper
  have hgen : R ⊔ (Ubar : Subgroup (P ⧸ pCore 2 P)) = ⊤ := by
    have hgenP : E.subgroupOf P ⊔ (U : Subgroup P) = ⊤ := by
      apply Subgroup.map_injective P.subtype_injective
      rw [Subgroup.map_sup,Subgroup.map_subgroupOf_eq_of_le hEP,hU,
        ← MonoidHom.range_eq_map,Subgroup.range_subtype]
      rw [hEeq]
      exact SectionThree.twoResidual_sup_sylowImage (show IsSylowSubgroupIn T P from ⟨U,hU⟩)
    change (E.subgroupOf P).map q ⊔ (U : Subgroup P).map q = ⊤
    rw [← Subgroup.map_sup,hgenP,Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
  have hmaxBar : IsCoatom (Ubar : Subgroup (P ⧸ pCore 2 P)) := by
    apply Theory.GroupTheory.sylow_isCoatom_of_elementary_odd_supplement_unique_maximal R Ubar hgen
    obtain ⟨M,hM,hUM,huniqM⟩ := (uniqueMaximalContaining_top_iff _).mp huniqBar
    exact ⟨M,⟨hM,hUM⟩,fun N hN => huniqM N hN.1 hN.2⟩
  have hmax : IsCoatom (U : Subgroup P) := by
    have hh := Subgroup.isCoatom_comap_of_surjective (QuotientGroup.mk'_surjective (pCore 2 P)) hmaxBar
    change IsCoatom (((U : Subgroup P).map q).comap q) at hh
    rwa [hcomapU] at hh
  let J := (GAt Γ cp.a ⊓ P) ⊔ ZAt Γ neighbor
  have hJP : J < P := nine_eight_extracted_center_proper_join ctx hb hcontain neighbor hneighbor hindex hnot
  have hUJ : (U : Subgroup P) ≤ J.subgroupOf P := by
    intro element helement
    have hT : (element : G) ∈ T := hU.le (Subgroup.mem_map_of_mem P.subtype helement)
    exact (le_sup_left : GAt Γ cp.a ⊓ P ≤ J) (cp.S_le_edge_stabilizers hT)
  have hJproper : J.subgroupOf P ≠ ⊤ := by
    intro htop
    exact hJP.not_ge (Subgroup.subgroupOf_eq_top.mp htop)
  have hJeq : J.subgroupOf P = (U : Subgroup P) := by
    by_contra hne
    exact hJproper (hmax.2 _ (lt_of_le_of_ne hUJ (fun heq => hne heq.symm)))
  have hJT : J ≤ T := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hJP.le,hJeq,hU]
  exact hescape (le_sup_right.trans (hJT.trans (edge_sylow_data ctx.sectionSeven Γ cp).1.1))

end Stellmacher.SectionNine
