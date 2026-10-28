module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Sp4Four.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.Elementary
public import Theory.GroupTheory.SmallMoverFamily

/-!
# The literal small-mover family on every Sp4(4) MS edge

The original moving layer is [omegaOrbit R,O²(M)]. Its common-edge embedding
is exactly U_alpha. Transporting maximum-order small movers through that
embedding proves their existence and shows that each contains the actual
neighborhood kernel Q_alpha. Their join consequently lies between Q_alpha
and the actual replacement radical T_beta. The radical is arbitrary.

This establishes the definitions and quotient saturation in MS93 (5.0),
printed p.912. The source pushing-up exclusion (5.1) and generating witnesses
(5.5)--(5.6) require further local mathematics; they are not assumptions here.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
variable {M : Type*} [Group M] [Finite M] (R : Subgroup M)
abbrev SmallMover (a t : Vertex R) (E : Subgroup (FreeAmalgam R)) : Prop :=
  Subgroup.SmallMover.Admissible (U R a) (Q R a) (Q R t) 16 E
abbrev MaximalMovers (a t : Vertex R) : Set (Subgroup (FreeAmalgam R)) :=
  Subgroup.SmallMover.Maximal (U R a) (Q R a) (Q R t) 16
noncomputable abbrev J (a t : Vertex R) : Subgroup (FreeAmalgam R) :=
  Subgroup.SmallMover.join (U R a) (Q R a) (Q R t) 16
noncomputable abbrev initialLayer : Subgroup M :=
  ⁅MSCentralOrbit.omegaOrbit R,pResidual 2 M⁆
theorem initialLayer_map : (initialLayer R).map (embedM R) = U R (alpha R) := by
  rw [U,MSCentralOrbit.Z_alpha_eq_omegaOrbit,Ltilde_alpha,←map_commutator]

theorem initialLayer_centralizes_core (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R) :
    initialLayer R ≤ centralizer (pCore 2 M : Set M) := by
  intro u hu v hv
  apply embedM_injective R
  have hU : embedM R u ∈ U R (alpha R) := initialLayer_map R ▸ mem_map_of_mem _ hu
  have hQ : embedM R v ∈ Q R (alpha R) := by
    rw [Q_alpha R hp hQR]
    exact mem_map_of_mem _ hv
  have h := (commutator_eq_bot_iff_le_centralizer.mp
    (Z_centralizes_Q R (alpha R) rfl)) (DistanceEight.U_le_Z R _ hU) (embedM R v) hQ
  simpa only [map_mul] using h

theorem edge_coordinates (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) :
    ∃ i : M →* FreeAmalgam R, Function.Injective i ∧
      i.range = stabilizer R a ∧ R.map i = Q R t ∧
      (pCore 2 M).map i = Q R a ∧ (initialLayer R).map i = U R a := by
  obtain ⟨g,hg | hg⟩ := (adjacent_iff_exists_common R a t).mp hat
  · rcases hg with ⟨rfl,rfl⟩
    let i := (MulAut.conj g⁻¹).toMonoidHom.comp (embedM R)
    refine ⟨i,(MulAut.conj g⁻¹).injective.comp (embedM_injective R),?_,?_,?_,?_⟩
    · have h := stabilizer_act R g (alpha R)
      dsimp only [i]
      rw [MonoidHom.range_comp]
      change (Mbar R).map (MulAut.conj g⁻¹).toMonoidHom = _
      simpa only [alpha,act_mVertex,one_mul,stabilizer_m_base] using h.symm
    · have h := Q_act R g (beta R)
      rw [Q_beta] at h
      simpa only [beta,act_hVertex,one_mul,Q_beta,map_map] using h.symm
    · have h := Q_act R g (alpha R)
      rw [Q_alpha R hp hQR] at h
      simpa only [alpha,act_mVertex,one_mul,Q_alpha R hp hQR,map_map] using h.symm
    · have h := U_act R g (alpha R)
      rw [←initialLayer_map R] at h
      simpa only [alpha,act_mVertex,one_mul,map_map] using h.symm
  · rw [hg.1] at ha
    cases ha

theorem maximalMovers_nonempty (a t : Vertex R) : (MaximalMovers R a t).Nonempty := by
  let : Finite (stabilizer R t) := finite_stabilizer R t
  let : Finite (Q R t) := Finite.of_injective (inclusion (show Q R t ≤ stabilizer R t from
    fun _ h => h.1)) (inclusion_injective _)
  exact Subgroup.SmallMover.maximal_nonempty _ _ _ 16 (by decide)

theorem maximalMovers_contains_Q (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t)
    {E : Subgroup (FreeAmalgam R)} (hE : E ∈ MaximalMovers R a t) : Q R a ≤ E := by
  obtain ⟨i,hi,hir,hiR,hiQ,hiU⟩ := edge_coordinates R hp hQR ha hat
  have hEr : E ≤ i.range := hE.1.1.trans (hiR ▸ map_le_range i R)
  have he : (E.comap i).map i = E := map_comap_eq_self hEr
  have hf : E.comap i ∈ Subgroup.SmallMover.Maximal (initialLayer R) (pCore 2 M) R 16 := by
    apply (Subgroup.SmallMover.maximal_map_iff i hi _ _ _ _ 16).mp
    rw [hiU,hiQ,hiR,he]
    exact hE
  have hk := Subgroup.SmallMover.maximal_contains_kernel (initialLayer R) (pCore 2 M) R
    16 hQR (initialLayer_centralizes_core R hp hQR) hf
  have hm := map_mono (f := i) hk
  rwa [hiQ,he] at hm

theorem Q_le_J (hp : IsPGroup 2 R) (hQR : pCore 2 M ≤ R)
    {a t : Vertex R} (ha : color R a = false) (hat : Adjacent R a t) : Q R a ≤ J R a t := by
  obtain ⟨E,hE⟩ := maximalMovers_nonempty R a t
  exact (maximalMovers_contains_Q R hp hQR ha hat hE).trans (le_sSup hE)

omit [Finite M] in
theorem J_le_radical (a t : Vertex R) : J R a t ≤ Q R t :=
  Subgroup.SmallMover.join_le _ _ _ _
end CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.LocalPackage
