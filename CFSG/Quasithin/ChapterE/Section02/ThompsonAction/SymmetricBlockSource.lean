module
public import CFSG.Quasithin.ChapterC.Section01.RankOne.Alternating.FiveBlockSource.ExternalCharacteristic
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.PairedFive.Source
public import CFSG.Quasithin.ChapterC.Section01.RankOne.ChiProduct.SelectedRankOne.FiveComponent
public import CFSG.Quasithin.ChapterE.Section02.ThompsonAction.QuasisimpleFiveWhole
/-!
# The original symmetric-five block conclusion

The full canonical characteristic pair is taken on the original Baumann
subgroup. In the paired case the actual selected alternating component and
its Sylow normalizer generate the ambient group together with T. Both local
normal alternatives therefore contradict exactly the original Baumann
characteristic-subgroup hypothesis. The resulting A₅ block retains its
literal moved support, the original Thompson commutator and generation.

Source: Aschbacher–Smith C.1.24(a), E.2.3(4), pp.130–131,217.
-/
public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.ChapterE.ThompsonAction
open ChapterB ChapterB.SourceInduction ChapterC ChapterC.RankOne
open ChapterC.RankOne.ChiProduct.SelectedRankOne Chapter1.Section02
universe u
variable {G H : Type u} [Group G] [Finite G] [Group H] [Finite H]

omit [Finite H] in
theorem covered_five_block_of_no_characteristic_baumann
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* Equiv.Perm (Fin 5)) (hq : Function.Surjective q)
    (hk : q.ker = centralizer (U : Set G))
    (p : Additive U →ₗ[ZMod 2] BinaryPermutation.core (Fin 5)) (hp : Function.Surjective p)
    (he : ∀ g v, p (NormalElementaryQuotient.representation U q hq hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (p v))
    (hfix : ∀ v, p v = 0 → ∀ g ∈ alternatingGroup (Fin 5),
      NormalElementaryQuotient.representation U q hq hk g v = v)
    (hfit : generalizedFitting G = pCore 2 G)
    (hno : ∀ D : Subgroup (baumann (T : Subgroup G)), D.Characteristic →
      (D.map (baumann (T : Subgroup G)).subtype).Normal → D = ⊥) :
    IsBlock (pResidual 2 G) ∧ IsAlternatingBlock (pResidual 2 G) 5 ∧
      pResidual 2 G = ⁅pResidual 2 G,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype = ⁅U,pResidual 2 G⁆ ∧
      (blockU (pResidual 2 G)).map (pResidual 2 G).subtype ≤ U := by
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  obtain ⟨D,hD⟩ := exists_baumann_universal_pair.{u,u} (T : Subgroup G) T.isPGroup' hTne
  obtain ⟨hc,⟨eL⟩⟩ := symmetric_five_residual_component h36 hG T hP U hU hJ q hq hk
  have him : (pResidual 2 G).map q = alternatingGroup (Fin 5) := by
    rw [map_pResidual_of_surjective 2 q hq,Equiv.Perm.twoResidual_eq_alternating]
  rcases FiveBlockSource.source_normal_alternatives T hfit (pResidual 2 G) hc
      (pResidual_sup_sylow_eq_top T) eL U q hq hk him p hp he hfix hJ D hD with hf | hs | hb
  · exact (D.first_ne_bot (hno D.first D.first_characteristic hf)).elim
  · exact (D.second_ne_bot (hno D.second D.second_characteristic hs)).elim
  · exact hb

theorem selected_component_sup_sylow
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (Y A : Subgroup H) [Y.Normal]
    (hJA : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ Y)
    (hYA : Y ≤ normalizer (A : Set H))
    (L : Subgroup G) (hL : L.IsCComponent)
    (hcan : (solvableResidual (A.comap q)).map (A.comap q).subtype = L) :
    L ⊔ (T : Subgroup G) = ⊤ := by
  let Q := Y.comap q
  let := hL.perfect
  let : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL.ne_bot
  have hn : Q ≤ normalizer (L : Set G) := selected_component_normalized q A L Q hcan
    ((map_comap_le q Y).trans hYA)
  have hres : pResidual 2 G ≤ Q := map_le_iff_le_comap.mp
    (RankOneBaumann.residual_image_le_normal_thompson_layer T hP U hU hJ q hq hk Y hJA)
  have hgen : Q ⊔ (T : Subgroup G) = ⊤ := top_unique
    ((pResidual_sup_sylow_eq_top T).symm.le.trans (sup_le_sup_right hres _))
  have horbit := source_factor_orbit_eq_residual T hP Q L hn hgen
  apply top_unique
  rw [←pResidual_sup_sylow_eq_top T]
  apply sup_le ?_ le_sup_right
  rw [←horbit]
  apply iSup_le
  intro t
  rintro x ⟨l,hl,rfl⟩
  have ht : (t:G) ∈ L ⊔ (T : Subgroup G) := (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right) t.property
  have hl' : l ∈ L ⊔ (T : Subgroup G) := (show L ≤ L ⊔ (T : Subgroup G) from le_sup_left) hl
  exact mul_mem (mul_mem ht hl') (inv_mem ht)

theorem selected_five_block_of_no_characteristic_baumann
    (T : Sylow 2 G) (hTne : (T : Subgroup G) ≠ ⊥)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (L : Subgroup G) (hL : L.IsCComponent)
    (hgen : L ⊔ (T : Subgroup G) = ⊤)
    (hno : ∀ D : Subgroup (baumann (T : Subgroup G)), D.Characteristic →
      (D.map (baumann (T : Subgroup G)).subtype).Normal → D = ⊥)
    (N : Subgroup G) (hLN : L ≤ N)
    (R : Sylow 2 N) (hBR : baumann (T : Subgroup G) ≤ (R : Subgroup N).map N.subtype)
    (hRT : (R : Subgroup N).map N.subtype ≤ T)
    (hfit : generalizedFitting N = pCore 2 N)
    [Normal (L.subgroupOf N)]
    (hprod : L.subgroupOf N ⊔ (R : Subgroup N) = ⊤)
    (eL : ((L.subgroupOf N) ⧸ pCore 2 (L.subgroupOf N)) ≃* alternatingGroup (Fin 5))
    (V : Subgroup N) [V.Normal] [IsElementaryAbelian 2 V]
    (hV : V.map N.subtype = ⁅U,L⁆)
    (p : N →* Equiv.Perm (Fin 5)) (hp : Function.Surjective p)
    (hk : p.ker = centralizer (V : Set N))
    (hLp : (L.subgroupOf N).map p = alternatingGroup (Fin 5))
    (f : Additive V ≃ₗ[ZMod 2] BinaryPermutation.core (Fin 5))
    (he : ∀ g v, f (NormalElementaryQuotient.representation V p hp hk g v) =
      BinaryPermutation.coreRepresentation (Fin 5) g (f v))
    (hJ : ¬ elementaryAbelianMaxJ (R : Subgroup N) ≤ centralizer (V : Set N)) :
    IsBlock L ∧ IsAlternatingBlock L 5 ∧ L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U := by
  let A := L.subgroupOf N
  have hAN : A.map N.subtype = L := map_subgroupOf_eq_of_le hLN
  have hNT : N ⊔ (T : Subgroup G) = ⊤ := top_unique (hgen ▸ sup_le_sup_right hLN _)
  obtain ⟨hb,ha,hm,hs,hu⟩ := FiveBlockSource.external_block_of_no_characteristic_baumann
    (T : Subgroup G) N T.isPGroup' hTne hNT
    (fun D hc hn hnorm => hn (hno D hc hnorm)) R hBR hRT hfit A
    (hL.subgroupOf hLN) hprod eL V p hp hk hLp f.toLinearMap f.surjective he
    (fun v hv _ _ => by
      have hz : v = 0 := f.injective (hv.trans (map_zero f).symm)
      subst v
      exact map_zero _) hJ
  let e : A ≃* L := subgroupOfEquivOfLe hLN
  have hblock : IsBlock L := by
    let := hL.perfect
    exact ⟨inferInstance,RankOne.Solvable.isShort_of_equiv e hb.short,hL.subnormal⟩
  have hpL : IsPPerfect 2 L := by
    let := hL.perfect
    intro Q hQ hpQ
    let := hQ
    let : Group.IsNilpotent (L ⧸ Q) := hpQ.isNilpotent
    apply top_unique
    rw [←solvableResidual_eq_top (G := L)]
    exact solvableResidual_le_of_solvable_quotient Q
  have hsame : (blockU A).map (N.subtype.comp A.subtype) = (blockU L).map L.subtype := by
    rw [←RankOne.Solvable.blockU_map_equiv e,map_map]
    rfl
  rw [hsame,hAN,hV] at hs
  rw [hAN] at hm
  have hid : ⁅(⁅U,L⁆ : Subgroup G),L⁆ = ⁅U,L⁆ :=
    commutator_isPPerfect_idempotent L U hpL (IsElementaryAbelian.isPGroup 2 U) le_normalizer_of_normal
  exact ⟨hblock,RankOne.Solvable.isAlternatingBlock_of_equiv e ha,hm,
    hs.trans hid,(hs.trans hid).le.trans (commutator_le_left U L)⟩

theorem paired_five_block_of_no_characteristic_baumann
    {C : GroupClass.{u}} (h36 : A36Input C) (hG : IsSQTK C G)
    (T : Sylow 2 G) (hP : IsMinimalParabolicOver T ⊤)
    (U : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U] (hU : IsPReduced 2 U)
    (hJ : ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (U : Set G))
    (q : G →* H) (hq : Function.Surjective q) (hk : q.ker = centralizer (U : Set G))
    (hs : ¬ Group.IsSolvable G) (hfit : generalizedFitting G = pCore 2 G)
    (d : SourceTwoFactorCase ((NormalElementaryQuotient.representation U q hq hk).comp
      (offenderSubgroup (NormalElementaryQuotient.representation U q hq hk)).subtype))
    (c : d.MarkedProduct (BinaryPermutation.naturalRepresentation (Fin 5)))
    (hexchange : letI := offenderSubgroup_normal (NormalElementaryQuotient.representation U q hq hk)
      ∃ t : T.mapSurjective hq,
        d.first.map (MulAut.conjNormal (t:H)).toMonoidHom = d.second ∧
        d.second.map (MulAut.conjNormal (t:H)).toMonoidHom = d.first)
    (hno : ∀ D : Subgroup (baumann (T : Subgroup G)), D.Characteristic →
      (D.map (baumann (T : Subgroup G)).subtype).Normal → D = ⊥) :
    ∃ L : Subgroup G, IsBlock L ∧ IsAlternatingBlock L 5 ∧
      L = ⁅L,elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      (blockU L).map L.subtype = ⁅U,L⁆ ∧ (blockU L).map L.subtype ≤ U ∧
      L ⊔ (T : Subgroup G) = ⊤ := by
  let α := NormalElementaryQuotient.representation U q hq hk
  let Y := offenderSubgroup α
  let A := (alternatingGroup (Fin 5)).map (SymmetricFive.Paired.leftFactorMap Y c.action.groupEquiv)
  let := offenderSubgroup_normal α
  obtain ⟨L,hL,hi,⟨eL⟩,hcan,hUL,hBL,hfitN,R,hR⟩ :=
    first_five_component_geometry h36 hG T hP U hU hJ q hq hk hs hfit d c hexchange
  let N := PairedFive.localJoin (T : Subgroup G) L
  let V := PairedFive.localMoved (T : Subgroup G) U L
  have hLN : L ≤ N := le_sup_left
  have hWL : (⁅U,L⁆ : Subgroup G) ≤ L := le_normalizer_iff_commutator_le_right.mp hUL
  have hV : V.map N.subtype = ⁅U,L⁆ := map_subgroupOf_eq_of_le (hWL.trans hLN)
  have hJA : (elementaryAbelianMaxJ (T : Subgroup G)).map q ≤ Y :=
    RankOneBaumann.thompson_image_le_offender_layer T U q hq hk
      (hU.le_pCore.trans (pCore_isPGroup.le_sylow_of_normal T)) Y le_rfl
  have hgen := selected_component_sup_sylow T hP U hU hJ q hq hk Y A hJA
    (five_first_axis_normalized Y c.action.groupEquiv) L hL hcan
  have hTne : (T : Subgroup G) ≠ ⊥ := by
    intro hz
    apply hP.2
    rw [hz]
    exact le_normalizer_of_normal
  obtain ⟨p,hp,hpk,f,hLp,he,hJR⟩ :=
    PairedFive.first_local_action T hP U hU hJ q hq hk d c hexchange L hi hUL hBL R hR
  have hBR : baumann (T : Subgroup G) ≤ (R : Subgroup N).map N.subtype := by
    rw [hR]
    exact le_inf inf_le_left hBL
  have hRT : (R : Subgroup N).map N.subtype ≤ T := by rw [hR]; exact inf_le_left
  have hprod : L.subgroupOf N ⊔ (R : Subgroup N) = ⊤ := by
    apply map_injective N.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hLN,hR,←MonoidHom.range_eq_map,range_subtype]
  let a : L.subgroupOf N ≃* L := subgroupOfEquivOfLe hLN
  let e : ((L.subgroupOf N) ⧸ pCore 2 (L.subgroupOf N)) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans eL
  have hb := selected_five_block_of_no_characteristic_baumann T hTne U L hL hgen hno N hLN
    R hBR hRT hfitN hprod e V hV p hp hpk hLp f he hJR
  exact ⟨L,hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2,hgen⟩
end CFSG.Quasithin.ChapterE.ThompsonAction
