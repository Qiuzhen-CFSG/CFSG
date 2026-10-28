module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.MaximizingParabolic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Paths
public import Theory.SpecificGroups.SymplecticFour.PlanePointProjection
public import Theory.GroupTheory.PResidual.PerfectImage

/-!
# The rank-one Sylow projection for a contained critical endpoint

For the actual endpoint image of order at least q² inside the chosen plane,
select a different point in that plane using the trace-annihilator calculation.
Lift its coordinate change to the original vertex residual. In that same
marking the endpoint, joined with the full point-parabolic two-core, is an
actual Sylow two-subgroup of the full parabolic preimage. The original Q-kernel
is retained throughout, as are all central attachments.

This discharges condition (*) on MS93 p.916 in the contained large-image
branch of (5.5). Extending the quotient path, proving the neighboring-mover
crossing and the individual/paired generation alternative remain necessary;
this selection alone does not give the final distance-two witness.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource MSCentralOrbit
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

omit [Finite F] [CharP F 2] in
/-- The literal critical endpoint supplies source (5.5)'s Sylow projection
at a different quotient point. The chosen lift belongs to the original
residual and preserves the whole original vertex quotient kernel. -/
theorem Input.replacement_contained_endpoint_sylow_projection
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (B : BinaryField) (hB : B.degree = n)
    (f : stabilizer d.radical a →* Sp B.Carrier) (hf : Function.Surjective f)
    (hfQ : f.ker.map (stabilizer d.radical a).subtype = Q d.radical a)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z))
    (hcontained : ((Z d.radical z).subgroupOf (stabilizer d.radical a)).map f ≤
      (CentralRootGeometry.wing true).map unipotent.subtype) :
    ∃ g : stabilizer d.radical a, g.val ∈ Ltilde d.radical a ∧
      f g ∈ planeLocal ∧ f g ∉ pointParabolic ∧
      let f' := (MulAut.conj (f g)).toMonoidHom.comp f
      let A := (Z d.radical z).subgroupOf (stabilizer d.radical a)
      let P := pointParabolic.comap f'
      Function.Surjective f' ∧ f'.ker = f.ker ∧
      A.map f' ≤ (CentralRootGeometry.wing true).map unipotent.subtype ∧
      ((A.map f').subgroupOf pointLocal).map pointQuotient =
        Matrix.SpecialLinearGroup.upperUnipotent B.Carrier ∧
      ∃ T : Sylow 2 P,
        (T : Subgroup P).map P.subtype = A ⊔ P.pCoreIn 2 := by
  let S := stabilizer d.radical a
  let A := (Z d.radical z).subgroupOf S
  let L := (Ltilde d.radical a).subgroupOf S
  let := finite_stabilizer d.radical a
  have hzS := path.endpoint_Z_le_start_stabilizer (by omega : 0 < geometry.b d.radical)
  have hc : Nat.card B.Carrier^2 ≤ Nat.card (A.map f) := by
    rw [←relIndex_ker]
    have hh := relIndex_map_map_of_injective f.ker A S.subtype_injective
    rw [hfQ,map_subgroupOf_eq_of_le hzS] at hh
    rw [←hh,B.card_eq,hB,←h.field_card]
    exact hlarge
  obtain ⟨u,hu,hnu,hAu,himage,hjoin⟩ := PlanePointProjection.exists_sylow_core_join
    B.card_eq (by rw [hB]; exact h.nonbinary) (A.map f) hcontained hc
  have hq : 2 < Nat.card B.Carrier := by
    rw [B.card_eq,hB]
    exact lt_of_lt_of_le (by decide : 2 < 2^2) (Nat.pow_le_pow_right (by decide) h.nonbinary)
  have hL : L.map f=⊤ := by
    have he : L=pResidual 2 S := comap_map_eq_self_of_injective S.subtype_injective _
    rw [he,map_pResidual_of_surjective 2 f hf]
    let : Group.IsPerfect (Sp B.Carrier) := perfect_of_card_gt_two hq
    exact pResidual_eq_top_of_isPerfect 2
  obtain ⟨g,hg,hfg⟩ := (show u ∈ L.map f by rw [hL]; trivial)
  let f' := (MulAut.conj (f g)).toMonoidHom.comp f
  let P := pointParabolic.comap f'
  have hf' : Function.Surjective f' := (MulAut.conj (f g)).surjective.comp hf
  have hmap : A.map f' = (A.map f).map (MulAut.conj u).toMonoidHom := by
    rw [Subgroup.map_map]
    rw [←hfg]
  have hker : f'.ker = f.ker := by
    ext y
    change (MulAut.conj (f g)) (f y)=1 ↔ f y=1
    exact (MulAut.conj (f g)).map_eq_one_iff
  have hQeq : f.ker = (Q d.radical a).subgroupOf S := by
    rw [←hfQ]
    exact (comap_map_eq_self_of_injective S.subtype_injective _).symm
  have hk : IsPGroup 2 f'.ker := by
    rw [hker,hQeq]
    exact (Q_isPGroup d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) a path.start_color).comap_subtype
  have hcore : P.pCoreIn 2 = (pointParabolic.pCoreIn 2).comap f' := by
    have hh := inf_comap_pCoreIn_eq_of_ker_isPGroup 2 f' P hk
    rw [map_comap_eq_self_of_surjective hf'] at hh
    exact hh.symm.trans (inf_eq_right.mpr (comap_mono (pCoreIn_le 2 _)))
  have hjoin' : (A ⊔ P.pCoreIn 2).map f' = unipotent := by
    rw [Subgroup.map_sup,hmap,hcore,map_comap_eq_self_of_surjective hf']
    exact hjoin
  have hkjoin : f'.ker ≤ A ⊔ P.pCoreIn 2 := by
    apply le_trans _ le_sup_right
    rw [hcore]
    exact ker_le_comap _ _
  have hfull : A ⊔ P.pCoreIn 2 = unipotent.comap f' := by
    rw [←hjoin',comap_map_eq_self hkjoin]
  let T₀ : Sylow 2 S := (unipotentSylow B.card_eq (by rw [hB]; exact lt_trans Nat.zero_lt_one h.nonbinary)).comapOfKerIsPGroup f' hk
    (by rw [MonoidHom.range_eq_top.mpr hf']; exact le_top)
  have hTP : (T₀ : Subgroup S) ≤ P :=
    comap_mono (show unipotent ≤ pointParabolic from unipotent_le_borel.trans inf_le_left)
  refine ⟨g,hg,by rwa [hfg],by rwa [hfg],hf',hker,?_,?_,T₀.subtype hTP,?_⟩
  · rwa [hmap]
  · rwa [hmap]
  · rw [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTP,hfull]
    rfl

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
