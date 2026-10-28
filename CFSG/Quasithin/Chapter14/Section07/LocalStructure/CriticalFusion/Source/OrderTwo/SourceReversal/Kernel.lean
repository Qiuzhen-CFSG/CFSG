module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.ActorPlacement
public import CFSG.Quasithin.Chapter14.Section03.Prelim.ThompsonSource.Marking
public import Theory.SpecificGroups.SymmetricFive.AutomorphismRank

/-!
# The actual H-neighborhood kernel in the two-core

The original natural action makes the order of LT prime to five: its
kernel is a two-group and its quotient is SL₃(2) of order168. Any H-normal
subgroup inside LT therefore has trivial image in the original S₅ quotient,
since every nontrivial normal subgroup of S₅ contains A₅. Apply this to the
radius-one kernel at H. This detects the neighbor required by F.9.17 from
the actual positive critical image, with no kernel identity assumed.

Source: Aschbacher–Smith F.9.17 and14.7.39, pp.324 and1060.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
open Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G} {L V:Subgroup G}
 {F:InvariantFlag T V 3} {W:Type u} [AddCommGroup W] [Module (ZMod 2) W]

theorem five_not_dvd_LT (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    ¬5∣Nat.card ↥(L⊔(T:Subgroup G)) := by
  obtain ⟨e,q,hq,hq2,ha,hker,hT,hR⟩ :=
    Chapter14.Section03.ThompsonSource.exists_marking d.natural F structural
  obtain ⟨n,hn⟩ := hq2.exists_card_eq
  have hc := q.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hq,Nat.card_congr topEquiv.toEquiv,
    Matrix.PSL3Two.card_SL,hn] at hc
  rw [←hc]
  intro hdiv
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp hdiv with hdiv|hdiv
  · exact (by decide : ¬5∣2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5)) hdiv)
  · norm_num at hdiv

theorem normal_subgroup_le_core (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u})
    (N:Subgroup G) (hNH:N≤F.H) (hNLT:N≤L⊔(T:Subgroup G))
    (hn:F.H≤normalizer (N:Set G)) : N≤F.H.pCoreIn 2 := by
  let P := (N.subgroupOf F.H).map d.qH
  let _ : (N.subgroupOf F.H).Normal := normal_subgroupOf_of_le_normalizer hn
  let _ : P.Normal := Subgroup.Normal.map inferInstance d.qH d.qH_surjective
  have hP : P=⊥ := by
    by_contra hne
    have hA : alternatingGroup (Fin 5) ≤ P :=
      Equiv.Perm.alternatingGroup_le_of_normal (by simp) ((nontrivial_iff_ne_bot P).mpr hne)
    have hc : Nat.card (alternatingGroup (Fin 5))=60 := by
      rw [nat_card_alternatingGroup,Nat.card_fin]; decide
    have h5 : 5∣Nat.card P := dvd_trans (by rw [hc]; decide) (card_dvd_of_le hA)
    have hN : Nat.card (N.subgroupOf F.H)=Nat.card N :=
      Nat.card_congr (subgroupOfEquivOfLe hNH).toEquiv
    have hd : Nat.card P∣Nat.card (N.subgroupOf F.H) := card_map_dvd _ _
    rw [hN] at hd
    exact five_not_dvd_LT d structural (h5.trans (hd.trans (card_dvd_of_le hNLT)))
  intro n hn
  have h : d.qH ⟨n,hNH hn⟩=1 := mem_bot.mp (hP ▸ mem_map_of_mem d.qH hn)
  have hk := MonoidHom.mem_ker.mpr h
  rw [d.qH_ker] at hk
  exact hk

theorem H_kernel_le_core (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222 KnownSimple.IsKnownSimple.{u}) :
    (ballKernel (geometryFamily (L:=L) F) (base (geometryFamily (L:=L) F) true) 1).map
      (GeometryGroup T L F).subtype ≤ F.H.pCoreIn 2 := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L:=L) F
  let B := ballKernel Ω (base Ω true) 1
  apply normal_subgroup_le_core d structural (B.map K.subtype)
  · have hh := map_mono (f:=K.subtype) (ballKernel_le_stabilizer Ω (base Ω true) 1)
    exact hh.trans_eq (ChapterF.Section07.Geometry.base_stabilizer_map_true _ _)
  · have ha : (graph Ω).Adj (base Ω true) (base Ω false) :=
      ⟨by change true≠false; decide,CosetGeometry.incident_base Ω true false⟩
    have hh := map_mono (f:=K.subtype) ((ballKernel_one_le_edge Ω ha).trans inf_le_right)
    exact hh.trans_eq (ChapterF.Section07.Geometry.base_stabilizer_map_false _ _)
  · intro h hh
    let a:K := ⟨h,mem_sup_right hh⟩
    have ha:a∈stabilizer Ω (base Ω true) := by
      simpa only [stabilizer,base,CosetGeometry.stabilizer_base] using
        (show a∈Ω true from hh)
    exact le_normalizer_map K.subtype (mem_map_of_mem K.subtype
      (stabilizer_le_normalizer_ballKernel Ω (base Ω true) 1 ha))
end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
