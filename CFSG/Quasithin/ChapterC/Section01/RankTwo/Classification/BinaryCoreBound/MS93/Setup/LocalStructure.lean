module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Critical

/-!
# Exact local subgroup structure of the MS93 tree

The neighborhood kernel is normal in its vertex stabilizer and contains
every normal subgroup lying in an edge stabilizer. Local transitivity gives
this maximality directly. Transporting an edge to the distinguished edge
reduces common normality to the characteristic-kernel theorem. The same
theorem makes the action faithful. The vertex groups are finite even though
the amalgam and its vertex set need not be finite.

Source: Meierfrankenfeld--Stellmacher (1993), 2.0 and 2.1(i)--(iii), pp.854--855.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93
variable {M : Type*} [Group M] (R : Subgroup M)

/-- Each first-neighborhood kernel is normalized by its vertex group. -/
theorem Q_normalized (a : Vertex R) :
    stabilizer R a ≤ normalizer (Q R a : Set (FreeAmalgam R)) := by
  intro g hg
  rw [mem_normalizer_iff_map_conj_eq]
  change (Q R a).map (MulAut.conj g).toMonoidHom = Q R a
  have hh := Q_act R g⁻¹ a
  have hga : act R g⁻¹ a = a := (stabilizer R a).inv_mem hg
  simpa only [hga, inv_inv] using hh.symm

/-- Normality is relative to the actual vertex stabilizer. -/
theorem Q_normal (a : Vertex R) : ((Q R a).subgroupOf (stabilizer R a)).Normal :=
  normal_subgroupOf_of_le_normalizer (Q_normalized R a)

/-- Source 2.1(ii): the kernel is the largest local normal subgroup in an edge. -/
theorem le_Q_of_normal_edge [Finite M] (a t : Vertex R) (hat : Adjacent R a t)
    (N : Subgroup (FreeAmalgam R)) (hN : N ≤ stabilizer R a ⊓ stabilizer R t)
    (hNorm : (N.subgroupOf (stabilizer R a)).Normal) : N ≤ Q R a := by
  have hn : stabilizer R a ≤ normalizer (N : Set (FreeAmalgam R)) :=
    (normal_subgroupOf_iff_le_normalizer (hN.trans inf_le_left)).mp hNorm
  intro x hx
  refine ⟨(hN hx).1, ?_⟩
  intro u hau
  obtain ⟨g, hg, hgu⟩ := stabilizer_transitive_neighbors R a hat hau
  rw [← hgu, stabilizer_act]
  refine ⟨g * x * g⁻¹, (hN (le_normalizer_iff.mp hn g hg x hx)).2, ?_⟩
  simp [mul_assoc]

/-- An element fixing the whole tree is identity under source (P). -/
theorem faithful_of_characteristic (hP : MSCharacteristicCondition R)
    (x : FreeAmalgam R) (hx : ∀ a, act R x a = a) : x = 1 := by
  have hh : x ∈ actionKernel R := hx
  rw [actionKernel_eq_bot_of_characteristic R hP] at hh
  exact hh

/-- Source 2.1(iii), transported through the actual edge embeddings. -/
theorem no_common_normal_at_edge (hP : MSCharacteristicCondition R)
    (a t : Vertex R) (ha : color R a = false) (hat : Adjacent R a t)
    (N : Subgroup (FreeAmalgam R)) (hN : N ≤ stabilizer R a ⊓ stabilizer R t)
    (hNa : (N.subgroupOf (stabilizer R a)).Normal)
    (hNt : (N.subgroupOf (stabilizer R t)).Normal) : N = ⊥ := by
  have hna := (normal_subgroupOf_iff_le_normalizer (hN.trans inf_le_left)).mp hNa
  have hnt := (normal_subgroupOf_iff_le_normalizer (hN.trans inf_le_right)).mp hNt
  obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := (adjacent_iff_exists_common R a t).mp hat
  · let e := (MulAut.conj g⁻¹).toMonoidHom
    have hS : N.comap e ≤ Sbar R := by
      rw [← Mbar_inf_Hbar]
      rw [stabilizer_mVertex, stabilizer_hVertex, ← Subgroup.map_inf _ _ _
        (MulAut.conj g⁻¹).injective] at hN
      have hh := comap_mono (f := e) hN
      rwa [comap_map_eq_self_of_injective (MulAut.conj g⁻¹).injective] at hh
    have hM : Mbar R ≤ normalizer (N.comap e : Set (FreeAmalgam R)) := by
      rw [← comap_normalizer_eq_of_surjective N (MulAut.conj g⁻¹).surjective]
      apply map_le_iff_le_comap.mp
      simpa only [stabilizer_mVertex] using hna
    have hH : Hbar R ≤ normalizer (N.comap e : Set (FreeAmalgam R)) := by
      rw [← comap_normalizer_eq_of_surjective N (MulAut.conj g⁻¹).surjective]
      apply map_le_iff_le_comap.mp
      simpa only [stabilizer_hVertex] using hnt
    have hb := no_nontrivial_common_invariant_of_characteristic R hP (N.comap e) hS
      (le_normalizer_iff.mp hM) (le_normalizer_iff.mp hH)
    have hh := congrArg (Subgroup.map e) hb
    simpa only [map_comap_eq, MonoidHom.range_eq_top_of_surjective e
      (MulAut.conj g⁻¹).surjective, top_inf_eq, Subgroup.map_bot] using hh
  · cases ha

variable [Finite M]

/-- The actual holomorph embeds into the finite set of an element and a function. -/
theorem finite_holomorph : Finite (Holomorph R) := by
  apply Finite.of_injective (fun h : Holomorph R => (h.left, fun r : R => h.right r))
  intro x y hxy
  apply SemidirectProduct.ext (congrArg Prod.fst hxy)
  apply DFunLike.ext
  intro r
  exact congrFun (congrArg Prod.snd hxy) r

/-- Finiteness is local, without a finite completion of the free amalgam. -/
theorem finite_stabilizer (a : Vertex R) : Finite (stabilizer R a) := by
  have : Finite (Holomorph R) := finite_holomorph R
  have : Finite (Mbar R) := Finite.of_surjective (embedM R).rangeRestrict
    (embedM R).rangeRestrict_surjective
  have : Finite (Hbar R) := Finite.of_surjective (embedH R).rangeRestrict
    (embedH R).rangeRestrict_surjective
  obtain ⟨g, hg⟩ | ⟨g, hg⟩ := stabilizer_conjugate_factor R a
  · rw [hg]
    exact Finite.of_equiv (Mbar R)
      ((Mbar R).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv
  · rw [hg]
    exact Finite.of_equiv (Hbar R)
      ((Hbar R).equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).toEquiv

/-- The M-vertex kernels are actual two-groups. -/
theorem Q_isPGroup (hp : IsPGroup 2 R) (hc : pCore 2 M ≤ R)
    (a : Vertex R) (ha : color R a = false) : IsPGroup 2 (Q R a) := by
  obtain ⟨g, rfl⟩ := exists_mVertex_of_color R ha
  have hh := Q_act R g (alpha R)
  simp only [alpha, act_mVertex, one_mul] at hh
  rw [hh]
  change IsPGroup 2 ((Q R (alpha R)).map _)
  rw [Q_alpha R hp hc]
  exact (pCore_isPGroup.map (embedM R)).map _

end CFSG.Quasithin.ChapterC.BinaryMS.MS93
