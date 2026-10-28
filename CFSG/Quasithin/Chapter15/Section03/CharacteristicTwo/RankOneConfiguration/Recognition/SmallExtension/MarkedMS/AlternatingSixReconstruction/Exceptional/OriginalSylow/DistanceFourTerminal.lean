module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourBaumann
public import Theory.Representation.HexacodeAction.SmallInvolution.Descent
public import CFSG.Quasithin.ChapterK.Section01To04.Alternating.Recognition.Six.FourSpace
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourEvenCover
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistanceFourMovingCost

/-!
# Exclusion of the original distance-four Borel branch

The moving radius has derived subgroup of order greater than two: its
normality and noncentrality in the whole original stabilizer exclude both
smaller orders. Restrict the moving central quotient to the actual even
preimage, whose quotient by the original two-core is the full triple cover
of A6. The opposed full span has image of order four and fixed codimension
at most two. Full residual movement and zero fixed space therefore give
an irreducible natural-four or faithful hexacode-six quotient.

Both quotient markings retain the literal original residual. In the natural
case invariant commutators bound the moving derived group by two. In the
hexacode case the separating invariant commutator forms vanish. Each
contradicts the established noncentral derived radius. The full original
graph, both covers, their central attachments and the odd cubic kernel E/Q
are retained throughout; the quotient used for recognition kills exactly Q.

Source: Meierfrankenfeld--Stellmacher (1993), (3.8), (3.10) and (5.12)(2),
printed pp.878--881,925--926; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.NaturalStructure.Exclusion
open scoped IsMulCommutative commutatorElement Pointwise
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "π" => CubicAction.projection h e hz hk
include h e hz hk in
/-- The moving derived subgroup cannot be centralized by the whole original stabilizer. -/
theorem borel_four_moving_derived_card_gt_two
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) :
    2 < Nat.card (_root_.commutator (Vcirc Rg (alpha Rg))) := by
  let a := alpha Rg
  let D := ⁅V Rg a,V Rg a⁆
  have hb := distance_gt_two h e hz hk
  have hfixed := borel_four_radius_derived_fixed_base h e hz hk u hR
  have hcard : Nat.card D = Nat.card (_root_.commutator (Vcirc Rg a)) := by
    rw [show D = ⁅V Rg a,V Rg a⁆ from rfl,
      radius_derived_eq_moving_derived_original h (sourceGeometry h) hb a (beta Rg)
        rfl (base_adjacent Rg) hfixed,
      ←map_subtype_commutator,card_map_of_injective (Vcirc Rg a).subtype_injective]
  have hDN : stabilizer Rg a ≤ normalizer (D : Set (FreeAmalgam Rg)) := by
    intro g hg
    rw [mem_normalizer_iff_map_conj_eq]
    change (⁅V Rg a,V Rg a⁆).map (MulAut.conj g).toMonoidHom = ⁅V Rg a,V Rg a⁆
    have hm : (V Rg a).map (MulAut.conj g).toMonoidHom = V Rg a :=
      mem_normalizer_iff_map_conj_eq.mp (V_normalized a hg)
    rw [map_commutator,hm]
  have hDG : D ≤ stabilizer Rg a :=
    hfixed.trans (inf_le_left.trans (fun _ hx => hx.1))
  let := finite_stabilizer Rg a
  let := Finite.of_injective (inclusion hDG) (inclusion_injective hDG)
  by_contra! hle
  change Nat.card (_root_.commutator (Vcirc Rg a)) ≤ 2 at hle
  have hc : Nat.card D = 1 ∨ Nat.card D = 2 := by
    have hp := Nat.card_pos (α := D)
    omega
  apply (borel_four_radius_derived_configuration h e hz hk u hR).2.2.2
  change D ≤ _
  rcases hc with hc | hc
  · exact (card_eq_one.mp hc).le.trans bot_le
  · exact le_centralizer_iff.mp (hDN.trans (normalizer_le_centralizer_of_card_two D hc))


open Atlas.Codes
include h e hz hk in
private theorem moving_recognition_impossible
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {J : Type*} [Group J] [Finite J]
    (j : J →* stabilizer Rg (alpha Rg)) (hj : Function.Injective j)
    (hres : (pResidual 2 J).map j = pResidual 2 (stabilizer Rg (alpha Rg)))
    (f : J →* HexAutomorphisms) (hE : hexSign.ker ≤ f.range)
    (hp : IsPGroup 2 f.ker) (A : Subgroup J)
    (hAE : A.map f ≤ hexSign.ker)
    (t : HexEvenAutomorphisms) (ht : orderOf t = 2) (htA : t.val ∈ A.map f)
    (hcost :
      letI := moving_central_quotient_elementary (sourceGeometry h)
        (sourceDistance_pos h) (alpha Rg) rfl
        (borel_four_radius_derived_fixed_base h e hz hk u hR)
      fixedCodim ((Offenders.linearize (movingQuotientAction (alpha Rg))).comp j) A ≤ 2) : False := by
  let a := alpha Rg
  have hb := distance_gt_two h e hz hk
  have hfixed := borel_four_radius_derived_fixed_base h e hz hk u hR
  let := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h) a rfl hfixed
  let := finite_moving (sourceGeometry h) hb a rfl
  let ρ := Offenders.linearize (movingQuotientAction a)
  let τ := ρ.comp j
  have hfull : subspaceCommutator τ ⊤ (pResidual 2 J) = ⊤ := by
    rw [subspaceCommutator_comp_map,hres]
    exact movingQuotientAction_full_original h (sourceGeometry h) hb a rfl hfixed
  have hfix : fixedSpace τ (pResidual 2 J) = ⊥ := by
    rw [fixedSpace_comp_map,hres]
    exact movingQuotient_fixedSpace_eq_bot_original h (sourceGeometry h) hb a rfl hfixed
  have hlo := borel_four_moving_derived_card_gt_two h e hz hk u hR
  change 2 < Nat.card (_root_.commutator (Vcirc Rg a)) at hlo
  have hn : Nontrivial (Additive ((Vcirc Rg a) ⧸ center (Vcirc Rg a))) := by
    by_contra! hh
    let := hh
    have hcomm : IsMulCommutative (Vcirc Rg a) := ⟨⟨fun x y => by
      have hx : QuotientGroup.mk' (center (Vcirc Rg a)) x = 1 :=
        Additive.ofMul.injective (Subsingleton.elim _ _)
      exact (mem_center_iff.mp ((QuotientGroup.eq_one_iff x).mp hx) y).symm⟩⟩
    let := hcomm
    rw [commutator_eq_bot,card_bot] at hlo
    omega
  let := hn
  obtain ⟨q₀,hq₀,σ,hσ,hnσ,hστ,hdegree⟩ := Hexacode.SmallInvolution.exists_residual_model
    f hE hp τ hfull hfix A hAE t ht htA hcost
  let er : pResidual 2 J ≃* pResidual 2 (stabilizer Rg a) :=
    ((pResidual 2 J).equivMapOfInjective j hj).trans (MulEquiv.subgroupCongr hres)
  have her (g : pResidual 2 (stabilizer Rg a)) : j (er.symm g).val = g.val := by
    exact congrArg Subtype.val (er.apply_symm_apply g)
  let q := q₀.comp er.symm.toMonoidHom
  have hq : Function.Surjective q := hq₀.comp er.symm.surjective
  have hσρ (g : pResidual 2 (stabilizer Rg a)) (v) : σ (q g) v = ρ g.val v := by
    change σ (q₀ (er.symm g)) v = ρ g.val v
    have hh := hστ (er.symm g) v
    change σ (q₀ (er.symm g)) v = ρ (j (er.symm g).val) v at hh
    rwa [her] at hh
  let := hσ
  rcases hdegree with ⟨hcenter,hdim⟩ | ⟨hfσ,hdim⟩
  · let η := (quotientOfLEKer σ (center HexEvenAutomorphisms) hcenter).comp
      Hexacode.even_quotient_center_equiv.symm.toMonoidHom
    have hησ (g : HexEvenAutomorphisms) : η (hexEvenCoordinate g) = σ g := by
      change quotientOfLEKer σ (center HexEvenAutomorphisms) hcenter
        (Hexacode.even_quotient_center_equiv.symm (hexEvenCoordinate g)) = _
      have hh : Hexacode.even_quotient_center_equiv.symm (hexEvenCoordinate g) =
          QuotientGroup.mk' (center HexEvenAutomorphisms) g :=
        Hexacode.even_quotient_center_equiv.symm_apply_eq.mpr rfl
      rw [hh]
      rfl
    have hfη : Function.Injective η := by
      let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      rcases (MonoidHom.normal_ker η).eq_bot_or_eq_top with hker | hker
      · exact η.ker_eq_bot_iff.mp hker
      · exfalso
        apply hnσ
        ext g v
        rw [←hησ]
        have hh : hexEvenCoordinate g ∈ η.ker := hker.symm ▸ mem_top _
        exact LinearMap.congr_fun hh v
    obtain ⟨E⟩ := CFSG.Quasithin.ChapterK.Alternating.RecognitionInputs.Six.actionEquiv_of_faithful_fourSpace η hfη hdim
    let f := E.groupEquiv.toMonoidHom.comp (hexEvenCoordinate.comp q)
    have hfs : Function.Surjective f := E.groupEquiv.surjective.comp (hexEvenCoordinate_surjective.comp hq)
    have hm : HasNaturalMovingQuotient (L := L) (R := R) a := by
      refine ⟨inferInstance,(alternatingGroup (Fin 6)).subtype.comp f,?_,E.linearEquiv,?_⟩
      · intro x hx
        obtain ⟨g,hg⟩ := hfs ⟨x,hx⟩
        exact ⟨g,congrArg Subtype.val hg⟩
      · intro g v
        rw [←hσρ g v,←hησ]
        exact E.intertwines _ _
    have hup := moving_derived_card_le_two_of_natural a hfixed hm
    omega
  · obtain ⟨E,F,hF⟩ := Hexacode.EvenBinaryRecognition.exists_equivariant σ hfσ hσ hdim
    let f := E.toMonoidHom.comp q
    have hfs : Function.Surjective f := E.surjective.comp hq
    have hm : HasHexacodeMovingQuotient (L := L) (R := R) a := by
      refine ⟨inferInstance,hexSign.ker.subtype.comp f,?_,F,?_⟩
      · intro x hx
        obtain ⟨g,hg⟩ := hfs ⟨x,hx⟩
        exact ⟨g,congrArg Subtype.val hg⟩
      · intro g v
        rw [←hσρ g v]
        exact hF _ _
    let := moving_commutative_of_hexacode (sourceGeometry h) (sourceDistance_pos h) a rfl hfixed hm
    rw [commutator_eq_bot,card_bot] at hlo
    omega

include h e hz hk in
/-- The distance-four original Borel branch contradicts both actual moving quotient models. -/
theorem borel_four_impossible
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom) : False := by
  let a := alpha Rg
  have hb := distance_gt_two h e hz hk
  obtain ⟨z,p,_⟩ := borel_four_exists_large_critical h e hz hk u hR
  let c := p.walk.getVert 2
  let P := localZSpan Rg a c
  let P₀ := P.comap (embedM Rg)
  let H := evenCoverGroup L R
  let A := P₀.subgroupOf H
  let j := evenCoverEmbedding h
  let f := hexSign.ker.subtype.comp (evenCoverProjection h e hz)
  have hl : p.walk.length = 4 := p.length_eq_b.trans (borel_distance_eq_four h e hz hk u hR)
  have hc : color Rg c = false := (p.vertex_color (by omega)).mpr (by decide)
  have hca : (cosetGraph Rg).dist c a = 2 := by
    rw [SimpleGraph.dist_comm,p.dist_start (by omega)]
  have hPQ : P ≤ Q Rg c :=
    (localZSpan_le_V Rg (by rw [SimpleGraph.dist_comm]; exact hca.le)).trans
      ((sourceGeometry h).V_le_Q hb c hc)
  have hPG : P ≤ stabilizer Rg a := hPQ.trans (Q_le_stabilizer_of_dist_two Rg c a hc hca)
  have hPm : P₀.map (embedM Rg) = P :=
    map_comap_eq_self (hPG.trans_eq (stabilizer_m_base Rg))
  obtain ⟨v,hv⟩ := borel_four_opposed_span_image h e hz hk u hR p
  have hAlt : P₀.map π ≤ alternatingGroup (Fin 6) := by
    change CubicAction.graphImage h e hz hk P ≤ _
    rw [hv]
    exact (map_mono (show D0 ≤ alternatingGroup (Fin 6) from inf_le_right)).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (by rw [normalizer_eq_top]; exact mem_top v))
  have hPH : P₀ ≤ H := le_evenCoverGroup_of_even_image h e hz hk P₀ hAlt
  have hAm : A.map H.subtype = P₀ := map_subgroupOf_eq_of_le hPH
  have hAj : A.map j = P.subgroupOf (stabilizer Rg a) := by
    apply Subgroup.map_injective (stabilizer Rg a).subtype_injective
    rw [map_subgroupOf_eq_of_le hPG,map_map]
    change A.map ((embedM Rg).comp H.subtype) = P
    rw [←map_map,hAm,hPm]
  have hfk : f.ker = (pCore 2 (L ⊔ R : Subgroup G)).subgroupOf H := by
    rw [MonoidHom.ker_comp_of_injective _ _ hexSign.ker.subtype_injective,
      evenCoverProjection_kernel]
  have hcard : Nat.card (A.map f) = 4 := by
    change Nat.card (A.map (hexSign.ker.subtype.comp (evenCoverProjection h e hz))) = 4
    rw [←map_map,card_map_of_injective hexSign.ker.subtype_injective]
    rw [evenCoverProjection_graph_image_card h e hz P hPG hPH]
    exact (borel_four_opposed_spans h e hz hk u hR p).2.1
  have hAE : A.map f ≤ hexSign.ker := by
    rintro _ ⟨x,_,rfl⟩
    exact (evenCoverProjection h e hz x).property
  obtain ⟨x,hx2⟩ := exists_prime_orderOf_dvd_card' (G := A.map f) 2 (by rw [hcard]; decide)
  let t : HexEvenAutomorphisms := ⟨x,hAE x.property⟩
  have ht : orderOf t = 2 := by
    rw [Subgroup.orderOf_mk]
    exact (orderOf_injective _ (A.map f).subtype_injective x).trans hx2
  have hE : hexSign.ker ≤ f.range := by
    intro x hx
    obtain ⟨g,hg⟩ := evenCoverProjection_surjective h e hz ⟨x,hx⟩
    exact ⟨g,congrArg Subtype.val hg⟩
  have hfp : IsPGroup 2 f.ker := by
    rw [hfk]
    exact pCore_isPGroup.comap_subtype
  apply moving_recognition_impossible h e hz hk u hR j (evenCoverEmbedding_injective h)
    (evenCoverEmbedding_residual_map h) f hE hfp A hAE t ht x.property
  let := moving_central_quotient_elementary (sourceGeometry h) (sourceDistance_pos h)
    a rfl (borel_four_radius_derived_fixed_base h e hz hk u hR)
  have hh := borel_four_opposed_span_moving_fixed_codim_le_two h e hz hk u hR p
  change fixedCodim ((Offenders.linearize (movingQuotientAction a)).comp j) A ≤ 2
  unfold fixedCodim
  rw [fixedSpace_comp_map,hAj]
  exact hh

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
