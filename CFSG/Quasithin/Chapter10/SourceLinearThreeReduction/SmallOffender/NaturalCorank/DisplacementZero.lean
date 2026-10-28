module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.Displacement
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.SmallOffender.NaturalCorank.PointGeneration

/-!
# Vanishing of the natural offender displacement

Nonzero displacement supplies a supplement to the opposite moved factor.
Point-centralizer generation then places L inside Mᵍ. A swapping offender
element puts the other component there too, contradicting the cubic-residual
rigidity L₀≤Mᵍ iff g∈M. Hence the whole offender fixes C_W(b).
The earlier outside-M intersection equality is the sole additional input.
Source: Aschbacher--Smith 10.2.12, printed p.754, identity (*).
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem displacement_eq_bot
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {g : G} (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    {t : G} (ht : t ∈ (T : Subgroup G)) (htn : t ∉ normalizer (L : Set G))
    (hinter : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥)
    {b : G}
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅(⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal,
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G)⁆ = ⊥ := by
  have hn := c.nonnormal
  have hcross := m.crossed t ht htn
  have hcent := c.pointCentralizers
  have hg := c.outside
  by_contra hQ
  let V := D.fullModule
  let W := ⁅D.fullModule,L⁆
  let U := W.map (MulAut.conj t).toMonoidHom
  let P := W.map (MulAut.conj g).toMonoidHom
  let A := P ⊓ D.maximalLocal
  let Q := ⁅A,W ⊓ centralizer ({b} : Set G)⁆
  let N := D.maximalLocal.map (MulAut.conj g).toMonoidHom
  have hQV : Q ≤ P ⊓ V :=
    source_nonnormal_offender_displacement_le D hn ht htn hcross hcent hb.1.1 hbn
  have hWV : W ≤ V := le_normalizer_iff_commutator_le_left.mp
    (((le_componentOrbit L T).trans (localOrbit T L).le_normalizer).trans
      D.maximalLocal_normalizes_fullModule)
  have hUV : U ≤ V := (map_mono hWV).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp
      (D.maximalLocal_normalizes_fullModule (le_normalizer_componentOrbit L T ht)))
  have hs := (nontrivial_displacement_supplement D c m ht htn hinter hb hbn hQ).2
  have hQN : ∀ q ∈ Q, q ≠ 1 → centralizer ({q} : Set G) ≤ N := by
    intro q hq hqne
    obtain ⟨w,hw,hew⟩ := (hQV hq).1
    have hwne : w ≠ 1 := by
      intro he
      apply hqne
      rw [←hew,he,map_one]
    rw [←hew]
    change centralizer ({(MulAut.conj g) w} : Set G) ≤ N
    rw [←CentralizerSmallKernelTransport.map_centralizer (MulAut.conj g) w]
    exact map_mono (hcent w hw hwne)
  have hLN : L ≤ N := le_of_supplement_point_centralizers D m Q U N
    (hQV.trans inf_le_right) hUV hs hcross hQN
  obtain ⟨a,ha,han⟩ : ∃ a ∈ A, a ∉ normalizer (W : Set G) := by
    by_contra! hAN
    have hfix := normalizer_fixed_space c m hinter hb.1.1 hbn
    change W ⊓ centralizer ({b} : Set G) ≤
      centralizer ((A ⊓ normalizer (W : Set G) : Subgroup G) : Set G) at hfix
    rw [inf_of_le_left (show A ≤ normalizer (W : Set G) from hAN)] at hfix
    exact hQ (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hfix))
  have hVM : V ≤ D.maximalLocal := D.fullModule_le_orbit.trans (localOrbit T L).le_normalizer
  have haN : a ∈ N := map_mono (hWV.trans hVM) ha.1
  have hLaN : L.map (MulAut.conj a).toMonoidHom ≤ N :=
    (map_mono hLN).trans_eq (mem_normalizer_iff_map_conj_eq.mp (N.le_normalizer haN))
  obtain ⟨s,hsT,hsn,hpair,_⟩ := source_nonnormal_pair D.simpleQTKE D.maximal.1 hn
  have hLa : L.map (MulAut.conj a).toMonoidHom ≠ L := by
    intro he
    apply han
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⁅V,L⁆).map (MulAut.conj a).toMonoidHom = ⁅V,L⁆
    have hm : V.map (MulAut.conj a).toMonoidHom = V :=
      mem_normalizer_iff_map_conj_eq.mp (D.maximalLocal_normalizes_fullModule ha.2)
    rw [map_commutator,hm,he]
  have he := (source_nonnormal_maximal_pair D hn hsT hsn a ha.2).resolve_left hLa
  have hRN : localOrbit T L ≤ N := by
    rw [hpair,←he]
    exact sup_le hLN hLaN
  have hd : 3 ∣ Nat.card (L ⧸ pCore 2 L) := by
    rw [Nat.card_congr m.quotient.toEquiv,Matrix.PSL3Two.card_SL]
    decide
  exact hg ((source_nonnormal_orbit_le_conjugate_maximal_iff D hn hd g).mp hRN)

/-- Identity (*) of the printed proof, on the whole actual offender
intersection, without assuming that intersection normalizes W. -/
theorem offender_fixed_space_eq
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    {g : G} (c : Configuration T D g) (m : SourceLinearThreeGeometry T D)
    (hinter : ⁅D.fullModule,L⁆ ⊓
      (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom = ⊥)
    {b : G}
    (hb : b ∈ (⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal ⊓
      normalizer ((⁅D.fullModule,L⁆ : Subgroup G) : Set G))
    (hbn : b ∉ centralizer (L.map (MulAut.conj g).toMonoidHom : Set G)) :
    ⁅D.fullModule,L⁆ ⊓ centralizer
      (((⁅D.fullModule,L⁆).map (MulAut.conj g).toMonoidHom ⊓ D.maximalLocal : Subgroup G) : Set G) =
      ⁅D.fullModule,L⁆ ⊓ centralizer ({b} : Set G) := by
  obtain ⟨t,ht,htn⟩ := SetLike.not_le_iff_exists.mp c.nonnormal
  have hzero := displacement_eq_bot D c m ht htn hinter hb hbn
  apply le_antisymm
  · exact inf_le_inf_left _ (centralizer_le (Set.singleton_subset_iff.mpr hb.1))
  · exact le_inf inf_le_left
      (le_centralizer_iff.mpr (commutator_eq_bot_iff_le_centralizer.mp hzero))

end CFSG.Quasithin.Chapter10.SmallOffender.NaturalCorank
