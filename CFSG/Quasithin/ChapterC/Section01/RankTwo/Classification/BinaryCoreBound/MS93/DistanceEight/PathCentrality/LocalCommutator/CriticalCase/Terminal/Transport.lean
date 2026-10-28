module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Inequality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase.Normalizer

/-!
# Natural-section transport for the terminal replacement in MS93 (4.4.1)

The final replacement takes (delta,c) in the orbit of (c,d), where d is the
backward vertex. It is the reversed pair (c,delta) that inherits failure of
HasNaturalSection from (d,c). Since the center changes, equality of orbit
spans under the old stabilizer is insufficient.

We transport every field of the expanded section through the conjugation
isomorphism between stabilizers. This includes relative normality, the
actual elementary quotient, the fixed/moving decomposition, and the same
natural coordinates with their conjugation formula. The final theorem
applies this transport to the precise reversed source pair.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.4.1), final paragraph, printed p.892; section notation on p.881.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
open Escape

private theorem map_relative_kernel {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (H N : Subgroup G) :
    (N.subgroupOf H).map (e.subgroupMap H).toMonoidHom =
      (N.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom) := by
  ext x
  rw [mem_map_equiv]
  change e.symm x.val ∈ N ↔ x.val ∈ N.map e.toMonoidHom
  exact mem_map_equiv.symm

private theorem map_fixed_preimage {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) (H L N : Subgroup G) [N.Normal]
    [(N.map e.toMonoidHom).Normal] :
    (centralizerModulo H L N).map e.toMonoidHom =
      centralizerModulo (H.map e.toMonoidHom) (L.map e.toMonoidHom)
        (N.map e.toMonoidHom) := by
  ext y
  simp only [mem_map_equiv, mem_centralizerModulo_iff, map_commutatorElement]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun l hl => h (e.symm l) hl⟩
  · rintro ⟨hy, h⟩
    refine ⟨hy, fun l hl => ?_⟩
    simpa only [e.symm_apply_apply] using h (e l) (by simpa using hl)

/-- Transport all clauses of the expanded natural-section condition through
an isomorphism of the acting groups, including the original coordinate action. -/
noncomputable def singleNaturalSection_map {G K : Type*} [Group G] [Group K]
    (e : G ≃* K) {π : G →* SL} {Q L H N : Subgroup G}
    (s : SingleNaturalSection π Q L H N) :
    SingleNaturalSection (π.comp e.symm.toMonoidHom)
      (Q.map e.toMonoidHom) (L.map e.toMonoidHom)
      (H.map e.toMonoidHom) (N.map e.toMonoidHom) := by
  letI := s.normal_group
  letI := s.normal_kernel
  letI := s.radical_normal
  letI : (H.map e.toMonoidHom).Normal := s.normal_group.map _ e.surjective
  letI : (N.map e.toMonoidHom).Normal := s.normal_kernel.map _ e.surjective
  letI : ((radicalPreimage Q H N).map e.toMonoidHom).Normal :=
    s.radical_normal.map _ e.surjective
  have hr : radicalPreimage (Q.map e.toMonoidHom) (H.map e.toMonoidHom)
      (N.map e.toMonoidHom) = (radicalPreimage Q H N).map e.toMonoidHom := by
    simp only [radicalPreimage, Subgroup.map_sup, map_commutator]
  have hm : movingPreimage (Q.map e.toMonoidHom) (H.map e.toMonoidHom)
      (N.map e.toMonoidHom) = (movingPreimage Q H N).map e.toMonoidHom := by
    simp only [movingPreimage, hr, Subgroup.map_sup, map_commutator, map_top_of_surjective e.toMonoidHom e.surjective]
  have hnr : (radicalPreimage (Q.map e.toMonoidHom) (H.map e.toMonoidHom)
      (N.map e.toMonoidHom)).Normal := hr ▸ inferInstance
  refine {
    projection_surjective := s.projection_surjective.comp e.symm.surjective
    projection_kernel := ?_
    kernel_le := map_mono s.kernel_le
    normal_group := inferInstance
    normal_kernel := inferInstance
    elementary := ?_
    radical_normal := hnr
    triple_le := ?_
    decomposition := ?_
    intersection := ?_
    natural := ?_ }
  · ext x
    change π (e.symm x) = 1 ↔ x ∈ Q.map e.toMonoidHom
    rw [mem_map_equiv, ← s.projection_kernel]
    rfl
  · let := s.elementary
    let q := QuotientGroup.congr (N.subgroupOf H)
      ((N.map e.toMonoidHom).subgroupOf (H.map e.toMonoidHom))
      (e.subgroupMap H) (map_relative_kernel e H N)
    exact IsElementaryAbelian.of_surjective q.toMonoidHom q.surjective
  · rw [← map_commutator, ← map_commutator]
    exact map_mono s.triple_le
  · let := hnr
    have hf := map_fixed_preimage e H ⊤ (radicalPreimage Q H N)
    rw [map_top_of_surjective e.toMonoidHom e.surjective] at hf
    simp only [hm, hr, ← hf, ← Subgroup.map_sup, ← s.decomposition]
  · let := hnr
    have hf := map_fixed_preimage e H ⊤ (radicalPreimage Q H N)
    rw [map_top_of_surjective e.toMonoidHom e.surjective] at hf
    simp only [hm, hr, ← hf, ← map_inf _ _ e.toMonoidHom e.injective, s.intersection]
  · rw [hm, hr]
    let k := e.subgroupMap (movingPreimage Q H N)
    refine {
      marking := s.natural.marking
      coordinates := s.natural.coordinates.comp k.symm.toMonoidHom
      surjective := s.natural.surjective.comp k.symm.surjective
      kernel := ?_
      normalized := ?_
      action := ?_ }
    · ext x
      change s.natural.coordinates (k.symm x) = 1 ↔
        x.val ∈ (radicalPreimage Q H N).map e.toMonoidHom
      rw [mem_map_equiv]
      exact Iff.of_eq (congrArg (fun A : Subgroup (movingPreimage Q H N) =>
        k.symm x ∈ A) s.natural.kernel)
    · calc
        ⊤ = (⊤ : Subgroup G).map e.toMonoidHom :=
          (map_top_of_surjective e.toMonoidHom e.surjective).symm
        _ ≤ (normalizer (movingPreimage Q H N : Set G)).map e.toMonoidHom :=
          map_mono s.natural.normalized
        _ ≤ _ := le_normalizer_map _
    · intro l _ x y hy
      exact s.natural.action (e.symm l) (mem_top _) (k.symm x) (k.symm y)
        (by change e.symm y.val = e.symm l * e.symm x.val * (e.symm l)⁻¹
            simpa only [map_mul, map_inv] using congrArg e.symm hy)


variable {M : Type*} [Group M] {R : Subgroup M}

private def stabilizerConj (g : FreeAmalgam R) (c : Vertex R) :
    stabilizer R c ≃* stabilizer R (act R g c) :=
  ((MulAut.conj g⁻¹).subgroupMap (stabilizer R c)).trans
    (MulEquiv.subgroupCongr (stabilizer_act R g c).symm)

private theorem map_stabilizer_subgroup (g : FreeAmalgam R) (c : Vertex R)
    (A : Subgroup (FreeAmalgam R)) :
    (A.subgroupOf (stabilizer R c)).map (stabilizerConj g c).toMonoidHom =
      (A.map (MulAut.conj g⁻¹).toMonoidHom).subgroupOf (stabilizer R (act R g c)) := by
  ext x
  rw [mem_map_equiv]
  change (MulAut.conj g⁻¹).symm x.val ∈ A ↔
    x.val ∈ A.map (MulAut.conj g⁻¹).toMonoidHom
  exact mem_map_equiv.symm

/-- Move the center, numerator and denominator together, retaining the literal
quotient kernel and the conjugation formula for the natural coordinates. -/
noncomputable def naturalSectionAt_act (g : FreeAmalgam R) {c : Vertex R}
    {A N : Subgroup (FreeAmalgam R)} (s : NaturalSectionAt c A N) :
    NaturalSectionAt (act R g c)
      (A.map (MulAut.conj g⁻¹).toMonoidHom)
      (N.map (MulAut.conj g⁻¹).toMonoidHom) := by
  let e := stabilizerConj g c
  refine {
    local_group := by rw [stabilizer_act]; exact map_mono s.local_group
    kernel_le := map_mono s.kernel_le
    projection := s.projection.comp e.symm.toMonoidHom
    module_section := ?_ }
  have h := singleNaturalSection_map e s.module_section
  simpa only [e, map_stabilizer_subgroup, map_pResidual, ← Q_act] using h

/-- Simultaneous conjugation carries the local orbit span to the span at the
conjugated center. The action is the project's right action. -/
theorem localZSpan_act (g : FreeAmalgam R) (a c : Vertex R) :
    localZSpan R (act R g a) (act R g c) =
      (localZSpan R a c).map (MulAut.conj g⁻¹).toMonoidHom := by
  have one_way (g : FreeAmalgam R) (a c : Vertex R) :
      localZSpan R (act R g a) (act R g c) ≤
        (localZSpan R a c).map (MulAut.conj g⁻¹).toMonoidHom := by
    apply iSup_le
    intro h
    let k : stabilizer R c := (stabilizerConj g c).symm h
    have hk : (k : FreeAmalgam R) = g * h * g⁻¹ := by
      simp [k, stabilizerConj, MulEquiv.subgroupMap_symm_apply, MulAut.conj_apply]
      rfl
    have hact : act R h (act R g a) = act R g (act R k a) := by
      simp only [← act_mul, hk, inv_mul_cancel_right]
    rw [hact, Z_act]
    exact map_mono (le_iSup (fun j : stabilizer R c => Z R (act R j a)) k)
  apply le_antisymm (one_way g a c)
  have h := map_mono (f := (MulAut.conj g⁻¹).toMonoidHom)
    (one_way g⁻¹ (act R g a) (act R g c))
  have hi : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id (FreeAmalgam R) := by
    apply MonoidHom.ext
    intro x
    simp [MulAut.conj_apply, mul_assoc]
  simpa only [← act_mul, mul_inv_cancel, act_one, inv_inv, map_map, hi,
    Subgroup.map_id] using h

/-- The full section condition is invariant when both vertices are conjugated. -/
theorem hasNaturalSection_act_iff (g : FreeAmalgam R) (a c : Vertex R) :
    HasNaturalSection R (act R g a) (act R g c) ↔ HasNaturalSection R a c := by
  have transport (g : FreeAmalgam R) (a c : Vertex R)
      (h : HasNaturalSection R a c) :
      HasNaturalSection R (act R g a) (act R g c) := by
    obtain ⟨s⟩ := h
    have s' := naturalSectionAt_act g s
    rw [← localZSpan_act, ← Z_act] at s'
    exact ⟨s'⟩
  constructor
  · intro h
    simpa only [← act_mul, mul_inv_cancel, act_one] using
      transport g⁻¹ (act R g a) (act R g c) h
  · exact transport g a c

/-- In the final source replacement (delta,c) is in the orbit of (c,d).
The reversed pair (c,delta) consequently inherits failure of the full section
condition from (d,c), with its center changed by the same conjugator. -/
theorem reversed_replacement_not_natural {geometry : Geometry R} {a c : Vertex R}
    (w : BackwardWitness R geometry a c) (hnone : ¬ HasNaturalSection R a c)
    {delta : Vertex R} {g : FreeAmalgam R}
    (hcenter : act R g c = delta) (hbackward : act R g w.backward = c) :
    ¬ HasNaturalSection R c delta := by
  have hn : ¬ HasNaturalSection R w.backward c :=
    fun h => hnone (w.hasNaturalSection_iff.mp h)
  simpa only [hcenter, hbackward] using
    (mt (hasNaturalSection_act_iff g w.backward c).mp hn)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality.LocalCommutator.CriticalCase
