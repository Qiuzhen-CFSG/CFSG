module
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.NoncentralPair
public import CFSG.Quasithin.ChapterC.Section01.NaturalSixControl.SymplecticSetup.EdgeCentrality

/-!
# Chief-factor control on the actual symplectic radius

The literal source embedding transfers the finite S6 chief-factor budget to
the radius and its kernel commutator. On a critical path of length four, the
proved radius-image estimate discharges the index-eight premise. An even
involution in the endpoint image and the marked endpoint commutator bound
then imply radius centrality through the abelian edge argument.

Failure of centrality selects a genuine critical pair with image at least
four. Graph conjugation places that pair at the original vertex, retaining
its literal quotient index. The marked-image and reverse-actor modules supply
the two remaining local inputs in the final radius-centrality assembly.

Source: Meierfrankenfeld--Stellmacher (1993), (5.2), printed pp.914--915.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
variable {M : Type*} [Group M] [Finite M]
  {L R W : Subgroup M} [L.Normal] [W.Normal] (s : Source L R W)

omit [Finite M] in
private theorem normalized_comap_normal (J : Subgroup (FreeAmalgam R))
    (hJ : stabilizer R (alpha R) ≤ normalizer (J : Set (FreeAmalgam R))) :
    (J.comap (embedM R)).Normal := by
  constructor
  intro n hn g
  change embedM R (g*n*g⁻¹) ∈ J
  rw [map_mul,map_mul,map_inv]
  exact (le_normalizer_iff.mp hJ (embedM R g)
    (by change embedM R g ∈ stabilizer R (mVertex R 1); rw [stabilizer_m_base]; exact ⟨g,rfl⟩)) _ hn

/-- The S6 chief-factor dichotomy on the literal radius, transported through
its source embedding. -/
theorem radius_residual_dichotomy_of_index
    (hb : 2 < s.geometry.b R) (hq : Function.Surjective s.projection)
    (A K : Subgroup (FreeAmalgam R))
    (hA : A ≤ stabilizer R (alpha R))
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ (A.comap (embedM R)).map s.projection)
    (hc : ⁅V R (alpha R) ⊓ K,A⁆ ≤ Z R (alpha R))
    (hindex : K.relIndex (V R (alpha R)) ≤ 8) :
    ⁅⁅V R (alpha R),Q R (alpha R)⁆,Ltilde R (alpha R)⁆ ≤ Z R (alpha R) ∨
      ⁅V R (alpha R),Ltilde R (alpha R)⁆ ≤
        ⁅V R (alpha R),Q R (alpha R)⁆ ⊔ Z R (alpha R) := by
  let f := embedM R
  let V₀ := (V R (alpha R)).comap f
  let Z₀ := (Z R (alpha R)).comap f
  let A₀ := A.comap f
  let K₀ := K.comap f
  let : V₀.Normal := normalized_comap_normal _ (V_normalized (alpha R))
  let : Z₀.Normal := normalized_comap_normal _ (Z_normalized R (alpha R))
  have hVQ : V R (alpha R) ≤ Q R (alpha R) := V_le_Q R rfl hb
  have hVrange : V R (alpha R) ≤ f.range :=
    (hVQ.trans (fun _ hx => hx.1)).trans_eq (stabilizer_m_base R)
  have hZV : Z R (alpha R) ≤ V R (alpha R) := by
    apply le_iSup_of_le (alpha R)
    exact le_iSup_of_le (by simp) le_rfl
  have hVm : V₀.map f = V R (alpha R) := by
    rw [map_comap_eq,inf_eq_right.mpr hVrange]
  have hZm : Z₀.map f = Z R (alpha R) := by
    rw [map_comap_eq,inf_eq_right.mpr (hZV.trans hVrange)]
  have hAm : A₀.map f = A := by
    rw [map_comap_eq]
    exact inf_eq_right.mpr (hA.trans_eq (stabilizer_m_base R))
  have hVker : V₀ ≤ s.projection.ker := by
    rw [s.projection_kernel]
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [hVm,←Q_alpha R s.two_group s.core_le]
    exact hVQ
  have hp : IsPGroup 2 s.projection.ker := by
    rw [s.projection_kernel]
    exact pCore_isPGroup
  have hc₀ : ⁅V₀ ⊓ K₀,A₀⁆ ≤ Z₀ := by
    apply (map_le_map_iff_of_injective (embedM_injective R)).mp
    rw [map_commutator,Subgroup.map_inf _ _ _ (embedM_injective R),hVm,hAm,hZm]
    exact (commutator_mono (inf_le_inf_left _ (map_comap_le _ _)) le_rfl).trans hc
  have hi₀ : K₀.relIndex V₀ ≤ 8 := by
    rw [relIndex_comap,hVm]
    exact hindex
  have hh := NoncentralChiefRefinement.SymmetricSixBudget.kernel_commutator_residual_dichotomy_of_index
    s.projection hq hp V₀ Z₀ (comap_mono hZV) hVker A₀ a ha heven haA K₀ hc₀ hi₀
  have hQm : s.projection.ker.map f = Q R (alpha R) := by
    rw [s.projection_kernel,Q_alpha R s.two_group s.core_le]
  have hLm : (pResidual 2 M).map f = Ltilde R (alpha R) := (Ltilde_alpha R).symm
  rcases hh with hh | hh
  · left
    have hh := map_mono (f := f) hh
    rwa [map_commutator,map_commutator,hVm,hQm,hLm,hZm] at hh
  · right
    have hh := map_mono (f := f) hh
    rwa [map_commutator,Subgroup.map_sup,map_commutator,hVm,hLm,hQm,hZm] at hh

/-- On the actual critical path, the source radius estimate discharges the
index-eight premise of the chief-factor argument. -/
theorem critical_radius_residual_dichotomy
    (t : Theory.SpecificGroups.SymmetricSix.BinaryFlags.S)
    (hR : R.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ ((Z R e).comap (embedM R)).map s.projection)
    (hc : ⁅V R (alpha R) ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R e⁆ ≤ Z R (alpha R)) :
    ⁅⁅V R (alpha R),Q R (alpha R)⁆,Ltilde R (alpha R)⁆ ≤ Z R (alpha R) ∨
      ⁅V R (alpha R),Ltilde R (alpha R)⁆ ≤
        ⁅V R (alpha R),Q R (alpha R)⁆ ⊔ Z R (alpha R) := by
  apply s.radius_residual_dichotomy_of_index (by omega)
    (s.projection_surjective_of_radical_image_le_conjugate t
      (by simpa only [Model.pointCore_eq_exceptional] using hR))
    (Z R e) (Q R (p.walk.getVert (p.walk.length-2)))
    (critical_Z_le_stabilizer R s.geometry (alpha R) rfl s.criticalDistance_pos p.critical)
    a ha heven haA hc
  exact s.critical_radius_image_index_le_eight t hR hb p

/-- The marked critical-path inputs now imply actual radius centrality. -/
theorem critical_radius_central_of_marked_actor
    (t : Theory.SpecificGroups.SymmetricSix.BinaryFlags.S)
    (hR : R.map s.projection ≤
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map (MulAut.conj t).toMonoidHom)
    (hb : s.geometry.b R = 4) {e : Vertex R}
    (p : CriticalPath R s.geometry (alpha R) e)
    (a : Equiv.Perm (Fin 6)) (ha : orderOf a = 2)
    (heven : a ∈ alternatingGroup (Fin 6))
    (haA : a ∈ ((Z R e).comap (embedM R)).map s.projection)
    (hc : ⁅V R (alpha R) ⊓ Q R (p.walk.getVert (p.walk.length-2)),Z R e⁆ ≤ Z R (alpha R)) :
    ⁅V R (alpha R),Q R (alpha R)⁆ ≤ centralizer (V R (alpha R) : Set (FreeAmalgam R)) :=
  s.radius_commutator_central_of_residual_dichotomy (by omega)
    (s.critical_radius_residual_dichotomy t hR hb p a ha heven haA hc)

/-- Noncentrality supplies a large-image critical path based at the original
vertex, using the actual graph conjugation. -/
theorem exists_base_large_critical_path
    (hb : s.geometry.b R = 4)
    (hn : ¬ ⁅V R (alpha R),Q R (alpha R)⁆ ≤
      centralizer (V R (alpha R) : Set (FreeAmalgam R))) :
    ∃ e, ∃ _p : CriticalPath R s.geometry (alpha R) e,
      4 ≤ (Q R e).relIndex (Z R (alpha R)) := by
  obtain ⟨d,e,hd,_,_,_,_,hlarge,hd',hpair⟩ :=
    s.exists_noncentral_critical_pair_large_image hb (alpha R) rfl hn
  obtain ⟨g,hdg⟩ := exists_mVertex_of_color R hd
  have hf : act R g⁻¹ d = alpha R := by
    rw [hdg,act_mVertex]
    simp only [mul_inv_cancel]
    rfl
  have hfcol : color R (act R g⁻¹ d) = false := by rw [hf]; rfl
  have hcrit : CriticalPair R (alpha R) (act R g⁻¹ e)
      (s.geometry.exists_critical (alpha R) rfl) := by
    simpa only [hf] using (criticalPair_act_iff R g⁻¹ d e
      (s.geometry.exists_critical d hd')
      (s.geometry.exists_critical (act R g⁻¹ d) hfcol)).mpr hpair
  refine ⟨act R g⁻¹ e,CriticalPath.ofPair rfl hcrit,?_⟩
  rw [←hf,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj (g⁻¹)⁻¹).injective]
  exact hlarge
end CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup.Source
