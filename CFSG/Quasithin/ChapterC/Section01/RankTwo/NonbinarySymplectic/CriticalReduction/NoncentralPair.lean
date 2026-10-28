module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.InnerAction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootImage
public import Theory.SpecificGroups.SymplecticFour.RootSubgroup.TwoNormalizer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.SectionFive.NoncentralPair

/-!
# Large critical images forced by a noncentral radius commutator

The center vertex kernel normalizes both endpoint seeds. If their critical
image were smaller than q², reciprocal comparison would identify a full long
root. The inner vertex marking sends the center kernel to a two-subgroup
normalizing that root, hence centralizing it. The mixed triple commutator
would vanish. Thus failure of radius centrality selects a critical pair of
image order at least q². Graph conjugation supplies the same pair based at
the original vertex, retaining its literal relative index.

This is the selection in MS93 (5.2)(ii), printed p.914. The chief-factor
argument excluding the selected noncentral case is still required.
-/

public noncomputable section
open Subgroup Representation Representation.OneCohomology Theory.GroupTheory
open Theory.SpecificGroups.SymplecticFour
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every two-subgroup normalizing a small critical seed centralizes its image
in the opposite vertex quotient. -/
theorem Input.replacement_small_critical_commutator_le_kernel
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (P : Subgroup (FreeAmalgam d.radical)) (hP : IsPGroup 2 P)
    (hPS : P ≤ stabilizer d.radical z)
    (hn : P ≤ normalizer (Z d.radical a : Set (FreeAmalgam d.radical)))
    (hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F ^ 2) :
    ⁅Z d.radical a,P⁆ ≤ Q d.radical z := by
  obtain ⟨E,hE,f,hf,hfQ,π,hπ,hπker,hact⟩ :=
    h.replacement_inner_natural_action d geometry hb path.end_color
  have hEF : Nat.card E.Carrier = Nat.card F := by rw [E.card_eq,hE,h.field_card]
  have hAS : Z d.radical a ≤ stabilizer d.radical z :=
    Z_le_stabilizer_of_dist_le a (geometry.exists_critical a path.start_color) path.critical.1.le
  let δ := f.comp (inclusion hAS)
  have hcard : Nat.card δ.range = (Q d.radical z).relIndex (Z d.radical a) :=
    quotient_image_card _ _ _ hAS f hfQ
  have hδact (x : Z d.radical a) (u : U d.radical z) :
      π ⟨x.val*u.val*x.val⁻¹,
        (mem_normalizer_iff.mp (critical_actor_normalizes_moving path x.property) u.val).mp u.property⟩ =
        Multiplicative.ofAdd (δ x • (π u).toAdd) := hact (inclusion hAS x) u
  obtain ⟨hc,hd,hquad⟩ := h.replacement_small_critical_root_image d hEF path
    (by omega) π hπ δ hcard hδact hsmall
  let ψ := f.comp (inclusion hPS)
  have hn' : ψ.range ≤ normalizer (δ.range : Set (Sp E.Carrier)) := by
    apply le_normalizer_iff.mpr
    rintro _ ⟨y,rfl⟩ _ ⟨x,rfl⟩
    let w : Z d.radical a := ⟨y.val*x.val*y.val⁻¹,
      (mem_normalizer_iff.mp (hn y.property) x.val).mp x.property⟩
    refine ⟨w,?_⟩
    change f (inclusion hAS w) =
      f (inclusion hPS y)*f (inclusion hAS x)*(f (inclusion hPS y))⁻¹
    rw [←map_inv,←map_mul,←map_mul]
    congr 1
  have hp' : IsPGroup 2 ψ.range := hP.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hcent := two_subgroup_normalizing_displacement_line_centralizes δ.range ψ.range hp' hn' hc hd hquad
  apply commutator_le.mpr
  intro x hx y hy
  let xx := inclusion hAS ⟨x,hx⟩
  let yy := inclusion hPS ⟨y,hy⟩
  have hcomm : f xx*f yy=f yy*f xx := hcent ⟨⟨y,hy⟩,rfl⟩ _ ⟨⟨x,hx⟩,rfl⟩
  have hk : ⁅xx,yy⁆ ∈ f.ker := by
    change f ⁅xx,yy⁆ = 1
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  exact hfQ ▸ (mem_map_of_mem (stabilizer d.radical z).subtype hk)

/-- Failure of radius centrality selects an actual critical pair whose forward
image has order at least q², with the original center vertex retained. -/
theorem Input.replacement_noncentral_critical_pair_large_image
    (geometry : Geometry d.radical) (hb : geometry.b d.radical = 4)
    (a : Vertex d.radical) (ha : color d.radical a = false)
    (hn : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤
      centralizer (V d.radical a : Set (FreeAmalgam d.radical))) :
    ∃ u z, color d.radical u = false ∧ color d.radical z = false ∧
      (cosetGraph d.radical).dist u a = 2 ∧ (cosetGraph d.radical).dist z a = 2 ∧
      ⁅⁅Z d.radical u,Q d.radical a⁆,Z d.radical z⁆ ≠ ⊥ ∧
      Nat.card F ^ 2 ≤ (Q d.radical z).relIndex (Z d.radical u) ∧
      ∃ hu : color d.radical u = false,
        CriticalPair d.radical u z (geometry.exists_critical u hu) := by
  obtain ⟨u,z,hu,hz,hua,hza,htrip,hu',hcrit⟩ :=
    SectionFive.exists_noncentral_critical_pair d.radical geometry hb a ha hn
  refine ⟨u,z,hu,hz,hua,hza,htrip,?_,hu',hcrit⟩
  by_contra! hsmall
  let path : CriticalPath d.radical geometry u z := CriticalPath.ofPair hu' hcrit
  have hPz : Q d.radical a ≤ stabilizer d.radical z :=
    Q_le_stabilizer_of_dist_le_two a z ha hz (by rw [SimpleGraph.dist_comm]; exact hza.le)
  have hPu : Q d.radical a ≤ stabilizer d.radical u :=
    Q_le_stabilizer_of_dist_le_two a u ha hu (by rw [SimpleGraph.dist_comm]; exact hua.le)
  have hc := h.replacement_small_critical_commutator_le_kernel d path (by omega)
    (Q d.radical a)
    (Q_isPGroup d.radical (h.replacement_two_group d) (h.replacement_core_le d) a ha)
    hPz (hPu.trans (Z_normalized d.radical u)) hsmall
  apply htrip
  apply le_bot_iff.mp
  exact (commutator_mono hc le_rfl).trans (by
    rw [commutator_comm,geometry.centralizes z hz])

/-- Conjugating the selected critical pair gives an actual path based at alpha
with the same large relative image index. -/
theorem Input.replacement_noncentral_base_large_critical_path
    (geometry : Geometry d.radical) (hb : geometry.b d.radical = 4)
    (hn : ¬ ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
      centralizer (V d.radical (alpha d.radical) : Set (FreeAmalgam d.radical))) :
    ∃ z, ∃ _path : CriticalPath d.radical geometry (alpha d.radical) z,
      Nat.card F ^ 2 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)) := by
  obtain ⟨u,z,hu,_,_,_,_,hlarge,hu',hcrit⟩ :=
    h.replacement_noncentral_critical_pair_large_image d geometry hb (alpha d.radical) rfl hn
  obtain ⟨g,hug⟩ := exists_mVertex_of_color d.radical hu
  have hf : act d.radical g⁻¹ u = alpha d.radical := by
    rw [hug,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hfcol : color d.radical (act d.radical g⁻¹ u) = false := by rw [hf]; rfl
  have hpair : CriticalPair d.radical (alpha d.radical) (act d.radical g⁻¹ z)
      (geometry.exists_critical (alpha d.radical) rfl) := by
    simpa only [hf] using (criticalPair_act_iff d.radical g⁻¹ u z
      (geometry.exists_critical u hu')
      (geometry.exists_critical (act d.radical g⁻¹ u) hfcol)).mpr hcrit
  refine ⟨act d.radical g⁻¹ z,CriticalPath.ofPair rfl hpair,?_⟩
  rw [←hf,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
  exact hlarge

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
