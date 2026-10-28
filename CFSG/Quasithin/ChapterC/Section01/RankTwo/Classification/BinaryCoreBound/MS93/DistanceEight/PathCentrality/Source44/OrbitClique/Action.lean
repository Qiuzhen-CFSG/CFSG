module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Selection.Inside.Recognition.Model.Star
public import Theory.SpecificGroups.PSL3Two.PointDoubleCoset

/-!
# Adjacency of the seven conjugate seeds

The point stabilizer in the actual SL3(2) has exactly two double cosets.
Conjugating the specified involution to the coordinate swap turns its
small escaping displacement into the intersection-index bound for every
pair of conjugate seeds. All maps retain the right-conjugation convention
of the local source construction.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (1.6), printed pp.845--847; used in (4.4.1)(2), p.891.
-/

public section
open Subgroup Matrix
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
open LocalCommutator.CriticalCase.Inside.Recognition
open Escape.Initial.Natural.Splitting
namespace OrbitClique
variable {E : Type*} [Group E]

 theorem conjugate_map (ρ : SL →* MulAut E) (W : Subgroup E) (g h : SL) :
    (actionConjugate ρ W g).map (ρ h).toMonoidHom = actionConjugate ρ W (g*h⁻¹) := by
  simpa only [actionConjugate,inv_inv] using actionConjugate_mul ρ W g h⁻¹

 theorem conjugate_cancel (ρ : SL →* MulAut E) (W : Subgroup E) (g : SL) :
    (actionConjugate ρ W g).map (ρ g).toMonoidHom=W := by
  rw [conjugate_map,mul_inv_cancel,actionConjugate_one]

 theorem pair_relIndex (ρ : SL →* MulAut E) (W : Subgroup E) (g h : SL) :
    (actionConjugate ρ W g).relIndex (actionConjugate ρ W h) =
      (actionConjugate ρ W (g*h⁻¹)).relIndex W := by
  have hh := relIndex_map_map_of_injective (f:=(ρ h).toMonoidHom)
    (actionConjugate ρ W g) (actionConjugate ρ W h) (ρ h).injective
  rw [conjugate_map,conjugate_cancel] at hh
  exact hh.symm

 theorem conjugate_seed_fixed (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ)
    {k : SL} (hk : k∈markedPointStabilizer d.marking d.point) :
    actionConjugate ρ d.seed k=d.seed := d.invariant _ ((markedPointStabilizer _ _).inv_mem hk)

 theorem uniform_index (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ)
    (e : SL ≃* SL) (he : ∀ k, k∈PSL3Two.pointParabolicSL ↔
      e k∈markedPointStabilizer d.marking d.point)
    (g : SL) (hg : g∉PSL3Two.pointParabolicSL) :
    (actionConjugate ρ d.seed (e g)).relIndex d.seed =
      (actionConjugate ρ d.seed (e PSL3Two.PointDoubleCoset.swap)).relIndex d.seed := by
  obtain ⟨a,ha,b,hb,hg⟩ := PSL3Two.PointDoubleCoset.decomposition g hg
  rw [hg,map_mul,map_mul,← actionConjugate_mul,← actionConjugate_mul,
    conjugate_seed_fixed ρ d ((he a).mp ha)]
  have hh := relIndex_map_map_of_injective (f:=(ρ (e b)⁻¹).toMonoidHom)
    (actionConjugate ρ d.seed (e PSL3Two.PointDoubleCoset.swap)) d.seed (ρ (e b)⁻¹).injective
  have hW : d.seed.map (ρ (e b)⁻¹).toMonoidHom=d.seed :=
    conjugate_seed_fixed ρ d ((he b).mp hb)
  rw [hW] at hh
  exact hh

 theorem involution_conjugator (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ)
    (e : SL ≃* SL) : ∃ n : SL, n*d.involution*n⁻¹=e PSL3Two.PointDoubleCoset.swap := by
  have ht : orderOf d.involution=2 := orderOf_eq_prime d.involution_sq d.involution_ne_one
  have hs : orderOf (e PSL3Two.PointDoubleCoset.swap)=2 := by
    rw [e.orderOf_eq]
    apply orderOf_eq_prime PSL3Two.PointDoubleCoset.swap_square
    intro hh
    exact PSL3Two.PointDoubleCoset.swap_not_mem (hh ▸ PSL3Two.pointParabolicSL.one_mem)
  obtain ⟨a,ha⟩ := PSL3Two.involutions_conjugate (PSL3Two.equiv d.involution)
    (PSL3Two.equiv (e PSL3Two.PointDoubleCoset.swap))
    ((PSL3Two.equiv.orderOf_eq _).trans ht) ((PSL3Two.equiv.orderOf_eq _).trans hs)
  refine ⟨PSL3Two.equiv.symm a,PSL3Two.equiv.injective ?_⟩
  simpa only [map_mul,map_inv,MulEquiv.apply_symm_apply,MulAut.conj_apply] using ha

 theorem mem_rightConjugate_iff (K : Subgroup SL) (t g : SL) :
    t∈NormalizerTransfer.rightConjugate K g ↔ g*t*g⁻¹∈K := by
  constructor
  · rintro ⟨k,hk,rfl⟩
    change g*(g⁻¹*k*(g⁻¹)⁻¹)*g⁻¹∈K
    have heq : g*(g⁻¹*k*(g⁻¹)⁻¹)*g⁻¹=k := by group
    rw [heq]
    exact hk
  · intro hh
    refine ⟨g*t*g⁻¹,hh,?_⟩
    change g⁻¹*(g*t*g⁻¹)*(g⁻¹)⁻¹=t
    group

 theorem map_reflected_pair (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ)
    (e : SL ≃* SL) (n : SL) (hn : n*d.involution*n⁻¹=e PSL3Two.PointDoubleCoset.swap) :
    (((actionConjugate ρ d.seed n).map (ρ d.involution).toMonoidHom).map
      (ρ n).toMonoidHom) = actionConjugate ρ d.seed (e PSL3Two.PointDoubleCoset.swap) := by
  have hi : (e PSL3Two.PointDoubleCoset.swap)⁻¹=e PSL3Two.PointDoubleCoset.swap := by
    apply inv_eq_of_mul_eq_one_left
    simp only [← pow_two,← map_pow,PSL3Two.PointDoubleCoset.swap_square,map_one]
  rw [actionConjugate,Subgroup.map_map,Subgroup.map_map,actionConjugate]
  congr 1
  ext w
  change ρ n (ρ d.involution (ρ n⁻¹ w))=ρ (e PSL3Two.PointDoubleCoset.swap)⁻¹ w
  rw [hi]
  rw [← MulAut.mul_apply,← map_mul,← MulAut.mul_apply,← map_mul,hn]


 theorem swap_moves_seed (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ)
    (hseed : d.seed≠⊤) (e : SL ≃* SL)
    (he : ∀ k, k∈PSL3Two.pointParabolicSL ↔ e k∈markedPointStabilizer d.marking d.point) :
    actionConjugate ρ d.seed (e PSL3Two.PointDoubleCoset.swap)≠d.seed := by
  let H := (MulAction.stabilizer (MulAut E) d.seed).comap (ρ.comp e.toMonoidHom)
  have hPH : PSL3Two.pointParabolicSL≤H := by
    intro x hx
    change d.seed.map (ρ (e x)).toMonoidHom=d.seed
    exact d.invariant _ ((he x).mp hx)
  have hntop : H≠⊤ := by
    intro htop
    apply hseed
    apply top_unique
    rw [← d.generates]
    apply iSup_le
    intro g
    have hh : e.symm g⁻¹∈H := htop ▸ mem_top _
    change d.seed.map (ρ (e (e.symm g⁻¹))).toMonoidHom=d.seed at hh
    simpa only [MulEquiv.apply_symm_apply,actionConjugate] using hh.le
  have hH : PSL3Two.pointParabolicSL=H := eq_of_le_of_not_lt hPH
    (fun h => hntop (PSL3Two.isCoatom_pointParabolicSL.2 _ h))
  intro hfix
  apply PSL3Two.PointDoubleCoset.swap_not_mem
  rw [hH]
  change d.seed.map (ρ (e PSL3Two.PointDoubleCoset.swap)).toMonoidHom=d.seed
  have hi : (e PSL3Two.PointDoubleCoset.swap)⁻¹=e PSL3Two.PointDoubleCoset.swap := by
    apply inv_eq_of_mul_eq_one_left
    simp only [← pow_two,← map_pow,PSL3Two.PointDoubleCoset.swap_square,map_one]
  simpa only [actionConjugate,hi] using hfix

variable [Finite E] [IsElementaryAbelian 2 E]

 theorem all_pair_indices_le_two (ρ : SL →* MulAut E) (d : EscapingConfiguration ρ) :
    ∀ g h : SL, (actionConjugate ρ d.seed g).relIndex (actionConjugate ρ d.seed h)≤2 := by
  obtain ⟨e,he⟩ := Star.exists_point_marking d.marking d.point d.point_ne_zero
  obtain ⟨n,hn⟩ := involution_conjugator ρ d e
  have hescape : d.involution∉NormalizerTransfer.rightConjugate
      (markedPointStabilizer d.marking d.point) n := by
    rw [mem_rightConjugate_iff,hn]
    exact fun hh => PSL3Two.PointDoubleCoset.swap_not_mem ((he _).mpr hh)
  have hsmall := escaping_image_relIndex_le_two ρ d n hescape
  have hh := relIndex_map_map_of_injective (f:=(ρ n).toMonoidHom)
    ((actionConjugate ρ d.seed n).map (ρ d.involution).toMonoidHom)
    (actionConjugate ρ d.seed n) (ρ n).injective
  rw [map_reflected_pair ρ d e n hn,conjugate_cancel] at hh
  have href : (actionConjugate ρ d.seed (e PSL3Two.PointDoubleCoset.swap)).relIndex d.seed≤2 :=
    hh ▸ hsmall
  have hbase (g : SL) : (actionConjugate ρ d.seed g).relIndex d.seed≤2 := by
    rw [← e.apply_symm_apply g]
    by_cases hg : e.symm g∈PSL3Two.pointParabolicSL
    · rw [conjugate_seed_fixed ρ d ((he _).mp hg),relIndex_self]
      decide
    · rw [uniform_index ρ d e he (e.symm g) hg]
      exact href
  intro g h
  rw [pair_relIndex]
  exact hbase _

end OrbitClique
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.Source44
