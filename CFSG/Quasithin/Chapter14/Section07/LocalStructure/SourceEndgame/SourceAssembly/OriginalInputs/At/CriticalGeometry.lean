module
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.SourceEndgame.SourceAssembly.OriginalInputs.At.Reciprocal
public import CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.OrderTwo.SourceReversal.Kernel

/-!
# Critical actor placement and neighborhood kernels at the original G,T

The original span fixes its critical ball. Translating the terminal tail
places Uα in the first-neighborhood kernel at LT, hence in Q and R₁.
The natural action has a two-group kernel and image SL₃(2), so LT has no
factor five. An H-normal subgroup inside LT therefore has trivial S₅
image. This puts the other neighborhood kernel in O₂(H).

These are the literal placement and escape inputs to the selected-path
construction and reciprocal quotient. Only Structural1222At at the same
G,T is used. Its source producer remains qt-d-1222-source, with final
14.7.75 discharge owned by qt-d-14775-source.
Source: AS Notation 14.7.1, 14.7.39 and 14.7.66; F.9.17.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source
open Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
  {F : InvariantFlag T V 3} {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The stronger placement in the literal two-core Q. -/
theorem Data.source_critical_le_Q_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) : c.Uα ≤ Q T L := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L := L) F
  let r : K := inclusion (le_sup_right : F.H ≤ K) c.rechoice
  let k : K := c.gammaConjugator*r
  let w := k⁻¹ • base Ω true
  have hb := c.three_le
  have hd : (graph Ω).dist w (base Ω false) ≤ c.b-2 := by
    have hh := SimpleGraph.dist_le (c.path.drop 2)
    rw [SimpleGraph.Walk.drop_length,c.length] at hh
    have hw : w = r⁻¹ • (c.gammaConjugator⁻¹ • base Ω true) := by
      simp only [w,k,mul_inv_rev,mul_smul]
    rw [hw,←c.alignment,CosetGeometry.RankTwo.dist_smul,SimpleGraph.dist_comm]
    exact hh
  have hle := ChapterF.Section07.Track.ballKernel_le_of_dist_add_le Ω
    (ChapterF.Section07.Geometry.family_generates _ _) (m:=1) (n:=c.b-1)
    (show (graph Ω).dist w (base Ω false)+1 ≤ c.b-1 by omega)
  intro x hx
  obtain ⟨u,hu,he⟩ := hx
  obtain ⟨u',hu',hu'e⟩ := d.source_span_ballKernel c hu
  have hk : k⁻¹*u'*k ∈ ballKernel Ω w (c.b-1) := by
    simpa only [inv_inv] using (conj_mem_ballKernel_iff Ω k⁻¹ u' (base Ω true) (c.b-1)).mpr hu'
  have hQ := d.base_kernel_le_Q_at structural
    (mem_map_of_mem K.subtype (hle hk))
  have heq : K.subtype (k⁻¹*u'*k) = x := by
    rw [←he]
    change (c.conjugator)⁻¹ * (u':G) * c.conjugator =
      (MulAut.conj c.conjugator⁻¹) u
    rw [←hu'e]
    simp
  exact heq ▸ hQ

/-- The source R₁ placement follows by restricting the original two-core. -/
theorem Data.source_critical_le_Ri_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F) : c.Uα ≤ F.Ri L 1 := by
  have hQT : Q T L ≤ (T:Subgroup G) :=
    (pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)).trans_eq
      (map_subgroupOf_eq_of_le le_sup_right)
  have hle : F.Li L 1 ⊔ (T:Subgroup G) ≤ L ⊔ (T:Subgroup G) :=
    sup_le_sup ((F.Li_le L 1).trans inf_le_left) le_rfl
  exact (d.source_critical_le_Q_at structural c).trans
    ((le_inf (hQT.trans le_sup_right) le_rfl).trans (inf_pCoreIn_le_of_le 2 hle))

/-- The placement field is constructed from the path; only the earlier global
quotient/Sylow facts remain. -/
theorem Data.source_earlierImages_at (d : Data T L V F W)
    (structural : Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
    (c : CriticalPath (L := L) F)
    (himage : star F (Q T L) = star F (F.Ri L 1))
    (hsylow : Chapter1.IsSylowIn 2 (star F (F.Ri L 1)) (star F (K F))) :
    c.EarlierImages := ⟨d.source_critical_le_Ri_at structural c,himage,hsylow⟩

end CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source

public section
open Subgroup
namespace CFSG.Quasithin.Chapter14.Section07.LocalStructure.CriticalFusion.Source.SourceReversal
open Chapter12.Section08 Subgroup.CosetGeometry.RankTwo
universe u
variable {G:Type u} [Group G] [Finite G] {T:Sylow 2 G} {L V:Subgroup G}
 {F:InvariantFlag T V 3} {W:Type u} [AddCommGroup W] [Module (ZMod 2) W]

theorem five_not_dvd_LT_at (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    ¬5∣Nat.card ↥(L⊔(T:Subgroup G)) := by
  let := d.natural.chosen.elementary
  obtain ⟨e,_,_⟩ := Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.coordinates
    (by simpa using d.natural.seed_card)
    ((F.Vi 1).subgroupOf V) ((F.Vi 2).subgroupOf V)
    (by rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 1)).toEquiv];
        simpa using F.card 1 (by decide))
    (by rw [Nat.card_congr (subgroupOfEquivOfLe (F.le_seed 2)).toEquiv];
        simpa using F.card 2 (by decide))
    (subgroupOf_mono _ (F.monotone (by decide : 1 ≤ 2)))
  let f := setupSeedAction (L ⊔ (T : Subgroup G)) V
    (sup_le d.natural.chosen.normalizes (d.natural.sylow_normalizes_seed_at structural))
  let q := Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut.symm.toMonoidHom.comp
    ((MulAut.congr e.symm).toMonoidHom.comp f)
  have hq : Function.Surjective q :=
    Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut.symm.surjective.comp
      ((MulAut.congr e.symm).surjective.comp (d.natural.full_LT_action_at structural))
  have hq2 : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [MonoidHom.ker_comp_of_injective _ _
      Matrix.PSL3Two.MarkedAutomorphisms.NaturalFlag.slAut.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ (MulAut.congr e.symm).injective]
    exact d.natural.action_kernel_isPGroup_at structural
  obtain ⟨n,hn⟩ := hq2.exists_card_eq
  have hc := q.ker.card_mul_index
  rw [index_ker,MonoidHom.range_eq_top.mpr hq,Nat.card_congr topEquiv.toEquiv,
    Matrix.PSL3Two.card_SL,hn] at hc
  rw [←hc]
  intro hdiv
  rcases (Nat.Prime.dvd_mul (by decide : Nat.Prime 5)).mp hdiv with hdiv|hdiv
  · exact (by decide : ¬5∣2) ((Nat.Prime.dvd_of_dvd_pow (by decide : Nat.Prime 5)) hdiv)
  · norm_num at hdiv

theorem normal_subgroup_le_core_at (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T)
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
    exact five_not_dvd_LT_at d structural (h5.trans (hd.trans (card_dvd_of_le hNLT)))
  intro n hn
  have h : d.qH ⟨n,hNH hn⟩=1 := mem_bot.mp (hP ▸ mem_map_of_mem d.qH hn)
  have hk := MonoidHom.mem_ker.mpr h
  rw [d.qH_ker] at hk
  exact hk

theorem H_kernel_le_core_at (d:Data T L V F W)
    (structural:Chapter12.Section02.Structural1222At KnownSimple.IsKnownSimple T) :
    (ballKernel (geometryFamily (L:=L) F) (base (geometryFamily (L:=L) F) true) 1).map
      (GeometryGroup T L F).subtype ≤ F.H.pCoreIn 2 := by
  let K := GeometryGroup T L F
  let Ω := geometryFamily (L:=L) F
  let B := ballKernel Ω (base Ω true) 1
  apply normal_subgroup_le_core_at d structural (B.map K.subtype)
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
