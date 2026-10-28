module

public import CFSG.Quasithin.Chapter13.Section02.A5Local.ThompsonOdd
public import CFSG.Quasithin.Chapter3.Section01.Source318Movement
public import CFSG.Quasithin.Chapter3.Section01.Source318Complete
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.Local

/-!
# The independent Thompson branch of original outside centralization

The original Context supplies Hypothesis 3.1.5 on LT and each H in
H*(T,N_G(L)). Source 3.1.8(3) then shows that a moving outside subgroup
forces J(T) to move V. Thus the Thompson-centralizing branch of 13.2.7
centralizes the whole Sylow omega-center. In the remaining branch the
literal local actor is S₅ and Baum(T) fixes precisely the original plane.

No outside-centralization theorem, Baumann normalizer bound, solvability
or nonsingular centralizer bound is used. Source: Aschbacher--Smith
13.2.4(2) and the opening of 13.2.7, printed pp.879--880; 3.1.8(3), p.576.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section06.CentralizerReduction
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)
include d

/-- The literal original outside pair satisfies the earlier qrc hypotheses. -/
theorem qrc_hypotheses
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    Chapter3.QrcHypotheses T (normalizer (L : Set G)) (L ⊔ (T : Subgroup G)) H V := by
  have hc : (T : Subgroup G).subgroupOf (L ⊔ (T : Subgroup G)) ⊓
      centralizer (V.subgroupOf (L ⊔ (T : Subgroup G)) :
        Set (L ⊔ (T : Subgroup G) : Subgroup G)) =
      pCore 2 (L ⊔ (T : Subgroup G) : Subgroup G) := by
    apply map_injective (L ⊔ (T : Subgroup G)).subtype_injective
    rw [map_inf _ _ _ (L ⊔ (T : Subgroup G)).subtype_injective,
      map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right),
      map_centralizer_subtype,
      map_subgroupOf_eq_of_le (d.chosen.le_sylow.trans le_sup_right),
      ← inf_assoc, inf_eq_left.mpr (show (T : Subgroup G) ≤ L ⊔ (T : Subgroup G) from le_sup_right)]
    exact d.sylow_centralizer d.normalizes_L
  have h := Chapter3.qrcHypotheses_of_reduced_join T (normalizer (L : Set G)) L H
    d.twoPerfect L.le_normalizer (normal_subgroupOf_of_le_normalizer le_rfl)
    (sup_le L.le_normalizer d.normalizes_L) hH (V.subgroupOf (L ⊔ (T : Subgroup G)))
    d.reduced hc
  rwa [map_subgroupOf_eq_of_le (d.chosen.le_sylow.trans le_sup_right)] at h

/-- Movement of the whole Sylow omega-center forces the original Thompson
subgroup to move V, independently of 13.2.7 and the Baumann bound. -/
theorem thompson_moves_of_omega_movement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G) := by
  apply (qrc_hypotheses d hH).thompson_moves_of_noncentral_omega d.hypothesis.qtke
    (SourceAssembly.maximal_normalizer d) d.unique_maximal_overgroup d.chosen.ne_bot
  intro hz
  apply hZ
  intro h hh z hzΩ
  obtain ⟨z', hz', he⟩ := hz hzΩ
  subst z
  exact congrArg H.subtype (((mem_center_iff.mp hz') ⟨h,hh⟩).symm)

/-- The full conclusion of 13.2.7 in the Thompson-centralizing branch. -/
theorem outside_centralizes_of_thompson_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  by_contra hZ
  exact thompson_moves_of_omega_movement d hH hZ hJ

/-- A moving original outside group forces the full symmetric-five action. -/
theorem localActor_surjective_of_omega_movement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Function.Surjective d.localActor :=
  d.localActor_surjective_of_thompson_moves (thompson_moves_of_omega_movement d hH hZ)

/-- The noncentral branch of 13.2.4 has the original fixed plane, without
assuming any later outside-group structure. -/
theorem baumann_fixed_plane_of_omega_movement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    V ⊓ centralizer (ChapterB.baumann (T : Subgroup G) : Set G) = V₂ := by
  apply (SourceAssembly.baumann_alternatives d).resolve_left
  intro hb
  exact thompson_moves_of_omega_movement d hH hZ
    ((ChapterB.elementaryAbelianMaxJ_le_baumann _).trans (hb.trans inf_le_right))

/-- The source plane is fixed by J(T) in every moving outside configuration. -/
theorem thompson_fixes_plane_of_omega_movement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    V₂ ≤ centralizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) := by
  rw [← baumann_fixed_plane_of_omega_movement d hH hZ]
  exact inf_le_right.trans (centralizer_le (ChapterB.elementaryAbelianMaxJ_le_baumann _))

open Representation Representation.BinaryOffender
open BinaryPermutation.FivePairFixedSpaces

/-- The actual Sylow image, Thompson image and original plane admit a
single symmetric-five marking as soon as H moves the Sylow omega-center. -/
theorem thompson_plane_marking_of_omega_movement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let K := L ⊔ (T : Subgroup G)
    let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
    ∃ g : Perm, (S : Subgroup K).map d.localActor =
      (normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom ∧
      d.flag.preimage V₂ = (fixedSubgroup (first * second)).map (actionHom g) ∧
      (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom := by
  let K := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  have hfull := localActor_surjective_of_omega_movement d hH hZ
  let P := S.mapSurjective hfull
  have hcard : Nat.card (d.flag.preimage V₂) = 4 :=
    (d.flag.preimage_card V₂ d.flag.two_le_V).trans d.flag.two_card
  have hinv : ∀ p ∈ (P : Subgroup Perm), ∀ x ∈ d.flag.preimage V₂,
      actionHom p x ∈ d.flag.preimage V₂ := by
    rintro p ⟨t, ht, rfl⟩ x hx
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.normalizerAction ⟨t,_⟩) x.toAdd)) ∈ V₂
    rw [← d.flag.normalizer_equivariant]
    exact (mem_normalizer_iff.mp (d.flag.two_invariant ht) _).mp hx
  have hn : (P : Subgroup Perm) ≤ normalizer
      ((elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor : Set Perm) := by
    apply (map_mono (f := d.localActor) ?_).trans
      ((elementaryAbelianMaxJ (S : Subgroup K)).le_normalizer_map d.localActor)
    intro t ht
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (elementaryAbelianMaxJ (S : Subgroup K)).map (MulAut.conj t).toMonoidHom = _
    rw [← elementaryAbelianMaxJ_map_equiv]
    congr 1
    exact mem_normalizer_iff_map_conj_eq.mp ((S : Subgroup K).le_normalizer ht)
  have hJmap : (elementaryAbelianMaxJ (S : Subgroup K)).map K.subtype =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    rw [← elementaryAbelianMaxJ_map_injective K.subtype K.subtype_injective]
    congr 1
    exact map_subgroupOf_eq_of_le le_sup_right
  have hplane := thompson_fixes_plane_of_omega_movement d hH hZ
  have hfix : ∀ a ∈ (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor,
      ∀ x ∈ d.flag.preimage V₂, actionHom a x = x := by
    rintro a ⟨t, ht, rfl⟩ x hx
    apply d.flag.module.injective
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.normalizerAction ⟨t,_⟩) x.toAdd)) = _
    rw [← d.flag.normalizer_equivariant]
    apply mul_inv_eq_iff_eq_mul.mpr
    apply mem_centralizer_iff.mp (hplane hx) t
    rw [← hJmap]
    exact mem_map_of_mem K.subtype ht
  have hmoves := thompson_moves_of_omega_movement d hH hZ
  exact BinaryPermutation.FiveSylowPlane.exists_plane_and_normal_odd_marking
    P (d.flag.preimage V₂) ((elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor)
    hcard hinv hn hfix (d.local_thompson_image_not_le_alternating hmoves)

/-- Complete simultaneous source marking of T, J(T), Baum(T), and V₂.
In particular the Thompson and Baumann images are the same four-group. -/
theorem thompson_baumann_plane_marking_of_omega_movement
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    let K := L ⊔ (T : Subgroup G)
    let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
    ∃ g : Perm, (S : Subgroup K).map d.localActor =
      (normalizer (pairClosure : Set Perm)).map (MulAut.conj g).toMonoidHom ∧
      d.flag.preimage V₂ = (fixedSubgroup (first * second)).map (actionHom g) ∧
      (elementaryAbelianMaxJ (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom ∧
      (ChapterB.baumann (S : Subgroup K)).map d.localActor =
        pairClosure.map (MulAut.conj g).toMonoidHom := by
  let K := L ⊔ (T : Subgroup G)
  let S := T.subtype (show (T : Subgroup G) ≤ K from le_sup_right)
  obtain ⟨g,hP,hW,hJ⟩ := thompson_plane_marking_of_omega_movement d hH hZ
  have hBm : (ChapterB.baumann (S : Subgroup K)).map K.subtype =
      ChapterB.baumann (T : Subgroup G) := by
    change ((S : Subgroup K) ⊓ centralizer
      (omegaOneCenterAmbient (elementaryAbelianMaxJ (S : Subgroup K)) : Set K)).map K.subtype = _
    have hSm : (S : Subgroup K).map K.subtype = (T : Subgroup G) :=
      map_subgroupOf_eq_of_le le_sup_right
    rw [baumann_map_injective K.subtype K.subtype_injective,hSm]
    rfl
  refine ⟨g,hP,hW,hJ,le_antisymm ?_ ?_⟩
  · rintro a ⟨t,ht,rfl⟩
    apply (BinaryPermutation.FiveSylowPlane.fixes_marked_plane_iff g _).mp
    rw [← hW]
    intro x hx
    have htG : (t : G) ∈ ChapterB.baumann (T : Subgroup G) := by
      rw [← hBm]
      exact mem_map_of_mem K.subtype ht
    have hfixV : V₂ ≤ centralizer (ChapterB.baumann (T : Subgroup G) : Set G) := by
      rw [← baumann_fixed_plane_of_omega_movement d hH hZ]
      exact inf_le_right
    apply d.flag.module.injective
    change d.flag.module.map (Multiplicative.ofAdd
      (BinaryPermutation.coreRepresentation (Fin 5) (d.flag.normalizerAction ⟨t,_⟩) x.toAdd)) = _
    rw [← d.flag.normalizer_equivariant]
    exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_iff.mp (hfixV hx) t htG)
  · rw [← hJ]
    exact map_mono (ChapterB.elementaryAbelianMaxJ_le_baumann _)

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
