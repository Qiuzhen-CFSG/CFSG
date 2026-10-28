module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelOpposite
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.BorelOpposite
public import Theory.GroupTheory.NormalizedSupConsequences
public import Mathlib.GroupTheory.IndexNormal
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicPlaneNormalizer



/-!
# Paired opposite movers and nonsplitting in the original Borel branch

The paired selectors simultaneously transport every index-two edge subgroup
containing the starting two-core. Their two conjugates and the unchanged
critical seed generate the entire local stabilizer. The finite calculation
uses the common square of all index-two Borel subgroups; its lift retains
the full cubic kernel E and the original graph embeddings.

If a distinct opposite mover contains Q, its central omega subgroup lies
in X = Omega-one of Z(Q). Were X the product of U and the local fixed part,
its fixed indices under the two movers would be four and eight. The movers
are conjugate along their common edge, so their central omega subgroups
have equal orders. Characteristic two identifies these with the two fixed
subgroups in X, giving a contradiction. This proves the nonsplitting clause
for the entire X, without identifying it with Z or U.

The small-critical-path theorem now supplies both alternatives of the
opposite-mover comparison (5.5)(c), with the same paired selectors and fixed
central attachments. Large critical-image comparisons, backward critical
paths and the terminal contradictions (5.11)--(5.12) remain required for
whole-core exhaustion. Both full moving covers, of orders 16 and 32, remain.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.5)(b,c), printed pp.915--917, and (5.7), p.919;
Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance.CubicFull


private theorem omegaCenter_eq_fixed_of_selfcentralizing
    {H : Type*} [Group H] (P Q J : Subgroup H)
    (hQJ : Q ≤ J) (hJP : J ≤ P)
    (hself : P ⊓ centralizer (Q : Set H) ≤ Q) :
    omegaCenter J = omegaCenter Q ⊓ centralizer (J : Set H) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxJ,hx2,hxc⟩ := mem_omegaCenter_iff.mp hx
    have hxQ : x ∈ Q := hself ⟨hJP hxJ,fun y hy => hxc y (hQJ hy)⟩
    exact ⟨mem_omegaCenter_iff.mpr ⟨hxQ,hx2,fun y hy => hxc y (hQJ hy)⟩,hxc⟩
  · rintro ⟨hx,hxc⟩
    obtain ⟨hxQ,hx2,_⟩ := mem_omegaCenter_iff.mp hx
    exact mem_omegaCenter_iff.mpr ⟨hQJ hxQ,hx2,hxc⟩

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "Rg" => edge L R
local notation "M" => (L ⊔ R : Subgroup G)
local notation "π" => CubicAction.projection h e hz hk

include h e hz in
private theorem vertex_core_selfcentralizing {a t : Vertex Rg}
    (ha : color Rg a = false) (hat : Adjacent Rg a t) :
    stabilizer Rg a ⊓ centralizer (Q Rg a : Set (FreeAmalgam Rg)) ≤ Q Rg a := by
  obtain ⟨i,hi,hir,_,hiQ,_⟩ := remaining_edge_coordinates h e hz ha hat
  rintro x ⟨hx,hxc⟩
  obtain ⟨m,rfl⟩ := hir ▸ hx
  rw [←hiQ]
  apply mem_map_of_mem
  apply h.relative_self_centralizing
  intro q hq
  apply hi
  simpa only [map_mul] using hxc (i q) (hiQ ▸ mem_map_of_mem i hq)

include h e hz hk in
/-- A distinct opposite Borel mover containing Q prevents the full central
omega layer from splitting into its moving part and the local fixed part. -/
theorem borel_opposite_containing_core_nonsplit (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {a c t : Vertex Rg} (ha : color Rg a = false) (hc : color Rg c = false)
    (hat : Adjacent Rg a t) (hct : Adjacent Rg c t)
    (hne : edgeOffenderJoin a t ≠ edgeOffenderJoin c t)
    (hcore : Q Rg a ≤ edgeOffenderJoin c t) :
    X Rg a ≠ U Rg a ⊔ (X Rg a ⊓ centralizer (stabilizer Rg a : Set (FreeAmalgam Rg))) := by
  intro hsplit
  obtain ⟨Ja,_,hJa,hQa,hAT,_,_,hfixa,_⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR ha hat
  obtain ⟨Jc,_,hJc,_,hCT,_⟩ :=
    borel_edge_maximal_offenders h e hz hk u hR hc hct
  have hfixc := borel_cross_thompson_fixed_index_eq_eight h e hz hk u hR ha hc hat hct hne
  rw [hJc] at hcore hfixc
  have hTP : Q Rg t ≤ stabilizer Rg a := fun _ hx => hx.2 a (adjacent_symm Rg hat)
  have hXP : X Rg a ≤ stabilizer Rg a := (omegaCenter_le (Q Rg a)).trans (fun _ hx => hx.1)
  let := finite_stabilizer Rg a
  let : Finite (X Rg a) := Finite.of_injective (inclusion hXP) (inclusion_injective _)
  have fixed_index (J : Subgroup (FreeAmalgam Rg)) (hQJ : Q Rg a ≤ J) (hJT : J ≤ Q Rg t) :
      (omegaCenter J).relIndex (X Rg a) = (centralizer (J : Set (FreeAmalgam Rg))).relIndex (U Rg a) := by
    have he := omegaCenter_eq_fixed_of_selfcentralizing (stabilizer Rg a) (Q Rg a) J
      hQJ (hJT.trans hTP) (vertex_core_selfcentralizing h e hz ha hat)
    change omegaCenter J = X Rg a ⊓ centralizer (J : Set (FreeAmalgam Rg)) at he
    let F := X Rg a ⊓ centralizer (J : Set (FreeAmalgam Rg))
    have hUF : U Rg a ⊔ F = X Rg a := by
      apply le_antisymm (sup_le (hsplit ▸ le_sup_left) inf_le_left)
      rw [hsplit]
      exact sup_le le_sup_left ((inf_le_inf_left _ (centralizer_le (hJT.trans hTP))).trans le_sup_right)
    have hUX : U Rg a ≤ X Rg a := hsplit ▸ le_sup_left
    let : Finite F := Finite.of_injective (inclusion (show F ≤ X Rg a from inf_le_left))
      (inclusion_injective _)
    rw [he]
    change F.relIndex (X Rg a) = _
    have hidx := relIndex_sup_of_normalizes (U Rg a) F
      ((inf_le_left.trans hXP).trans (U_normalized a))
    rw [hUF] at hidx
    rw [hidx]
    have hfu : F ⊓ U Rg a = U Rg a ⊓ centralizer (J : Set (FreeAmalgam Rg)) := by
      dsimp only [F]
      ext v
      exact ⟨fun hv => ⟨hv.2,hv.1.2⟩,fun hv => ⟨⟨hUX hv.1,hv.2⟩,hv.1⟩⟩
    rw [←inf_relIndex_right F (U Rg a),hfu,inf_relIndex_left]
  have hia := fixed_index Ja hQa hAT
  have hic := fixed_index Jc hcore hCT
  rw [hfixa] at hia
  rw [hfixc] at hic
  obtain ⟨g,hg,hga⟩ := stabilizer_transitive_neighbors Rg t
    (adjacent_symm Rg hat) (adjacent_symm Rg hct)
  have hgt : act Rg g t = t := hg
  have hconj := remaining_edge_join_act h e hz hk u (Or.inr hR) ha hat g
  rw [hga,hgt,hJa,hJc] at hconj
  have homega : Nat.card (omegaCenter Ja) = Nat.card (omegaCenter Jc) := by
    rw [hconj,omegaCenter_map _ _ (MulAut.conj g⁻¹).injective,
      card_map_of_injective (MulAut.conj g⁻¹).injective]
  have hea := omegaCenter_eq_fixed_of_selfcentralizing (stabilizer Rg a) (Q Rg a) Ja
    hQa (hAT.trans hTP) (vertex_core_selfcentralizing h e hz ha hat)
  have hec := omegaCenter_eq_fixed_of_selfcentralizing (stabilizer Rg a) (Q Rg a) Jc
    hcore (hCT.trans hTP) (vertex_core_selfcentralizing h e hz ha hat)
  have haX : omegaCenter Ja ≤ X Rg a := hea ▸ inf_le_left
  have hcX : omegaCenter Jc ≤ X Rg a := hec ▸ inf_le_left
  have hma := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) (omegaCenter Ja) (X Rg a) bot_le haX
  have hmc := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam Rg)) (omegaCenter Jc) (X Rg a) bot_le hcX
  rw [relIndex_bot_left,relIndex_bot_left,hia] at hma
  rw [relIndex_bot_left,relIndex_bot_left,hic,←homega] at hmc
  let : Finite (omegaCenter Ja) := Finite.of_injective (inclusion haX) (inclusion_injective _)
  have hp : 0 < Nat.card (omegaCenter Ja) := Nat.card_pos
  omega

include h e hz hk in
/-- The same paired selectors discharge both opposite-mover alternatives
of source (5.5)(c) for a small critical image: individual residual generation,
or joint generation, exact intersection index and nonsplitting of the full X. -/
theorem borel_small_critical_opposite_pair_selectors (u : S)
    (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z : Vertex Rg} (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hsmall : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    {c : Vertex Rg} (hc : color Rg c = false)
    (hcb : Adjacent Rg c (p.walk.getVert 1))
    (hne : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ≠
      edgeOffenderJoin c (p.walk.getVert 1)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧
      ∃ r ∈ L.subgroupOf (L ⊔ R),
        let x := (embedM Rg r)⁻¹
        let J := edgeOffenderJoin (alpha Rg) t
        let J' := edgeOffenderJoin (alpha Rg) (act Rg x t)
        ∃ g ∈ stabilizer Rg (alpha Rg),
          act Rg g (p.walk.getVert 1) = t ∧
          (J ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
          J ⊔ J' = stabilizer Rg (alpha Rg) ∧
          Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
          Q Rg (act Rg x t) ⊔ Z Rg z = stabilizer Rg (alpha Rg) ∧
          Z Rg (p.walk.getVert 1) ⊓ centralizer (J : Set (FreeAmalgam Rg)) ≤
            centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          Z Rg (p.walk.getVert 1) ⊓ centralizer (J' : Set (FreeAmalgam Rg)) ≤
            centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg)) ∧
          ((Ltilde Rg (alpha Rg) ≤ edgeOffenderJoin (act Rg g c) t ⊔ Z Rg z ∧
            Ltilde Rg (alpha Rg) ≤
              edgeOffenderJoin (act Rg x (act Rg g c)) (act Rg x t) ⊔ Z Rg z) ∨
            (Q Rg (alpha Rg) ≤ edgeOffenderJoin c (p.walk.getVert 1) ∧
              (Q Rg (alpha Rg)).relIndex
                (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ⊓
                  edgeOffenderJoin c (p.walk.getVert 1)) = 4 ∧
              (edgeOffenderJoin (act Rg g c) t ⊔
                edgeOffenderJoin (act Rg x (act Rg g c)) (act Rg x t)) ⊔ Z Rg z =
                  stabilizer Rg (alpha Rg) ∧
              X Rg (alpha Rg) ≠ U Rg (alpha Rg) ⊔
                (X Rg (alpha Rg) ⊓ centralizer
                  (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))) := by
  obtain ⟨t,hat,r,hr,hgen,hpair,_,_,hBfirst,hBsecond,hfix,hfix',_,_,_,g,hg,hgt,hopposite⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hsmall
  let x := (embedM Rg r)⁻¹
  have hab : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  refine ⟨t,hat,r,hr,g,hg,hgt,hgen,hpair,hBfirst,hBsecond,hfix,hfix',?_⟩
  by_cases hcore : Q Rg (alpha Rg) ≤ edgeOffenderJoin c (p.walk.getVert 1)
  · have hcg : color Rg (act Rg g c) = false := by rw [action_preserves_color,hc]
    have hcgt : Adjacent Rg (act Rg g c) t := by
      rw [←hgt]
      exact (adjacent_act_iff Rg g _ _).mpr hcb
    obtain ⟨Jc,_,hJc,_,hCT,hi,_⟩ := borel_edge_maximal_offenders h e hz hk u hR hc hcb
    have hh := hopposite (edgeOffenderJoin c (p.walk.getVert 1)) hcore
      (by rwa [hJc]) (by rwa [hJc])
    have hgJ := remaining_edge_join_act h e hz hk u (Or.inr hR) hc hcb g
    rw [hgt] at hgJ
    have hxJ := remaining_edge_join_act h e hz hk u (Or.inr hR) hcg hcgt x
    dsimp only at hh
    rw [←hgJ,←hxJ] at hh
    exact Or.inr ⟨hcore,borel_opposite_containing_core_index h e hz hk u hR rfl hc
      hab hcb hne hcore,hh,borel_opposite_containing_core_nonsplit h e hz hk u hR
        rfl hc hab hcb hne hcore⟩
  · have hcg : color Rg (act Rg g c) = false := by rw [action_preserves_color,hc]
    have hcgt : Adjacent Rg (act Rg g c) t := by
      rw [←hgt]
      exact (adjacent_act_iff Rg g _ _).mpr hcb
    have hcoreg : ¬ Q Rg (alpha Rg) ≤ edgeOffenderJoin (act Rg g c) t := by
      rw [←hgt]
      exact borel_core_not_le_transported_mover h e hz hk u hR hc hcb hcore g hg
    have hx : x ∈ stabilizer Rg (alpha Rg) := by
      change x ∈ stabilizer Rg (mVertex Rg 1)
      rw [stabilizer_m_base]
      exact ⟨r⁻¹,by rw [map_inv]⟩
    have hxat : Adjacent Rg (alpha Rg) (act Rg x t) := by
      rw [←show act Rg x (alpha Rg) = alpha Rg from hx]
      exact (adjacent_act_iff Rg x _ _).mpr hat
    have hcx : color Rg (act Rg x (act Rg g c)) = false := by
      rw [action_preserves_color,hcg]
    have hcxt := (adjacent_act_iff Rg x _ _).mpr hcgt
    have hcorex := borel_core_not_le_transported_mover h e hz hk u hR hcg hcgt hcoreg x hx
    exact Or.inl ⟨(borel_opposite_generation_of_core_not_le h e hz hk u hR rfl hcg
      hat hcgt _ hBfirst hcoreg).2,
      (borel_opposite_generation_of_core_not_le h e hz hk u hR rfl hcx
        hxat hcxt _ hBsecond hcorex).2⟩

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
