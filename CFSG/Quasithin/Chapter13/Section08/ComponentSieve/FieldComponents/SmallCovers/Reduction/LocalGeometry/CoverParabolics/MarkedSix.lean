module

public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.MarkedSetup
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.SixParabolics
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.SixDiagramSpan
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics.SourceComparison
public import Theory.GroupTheory.PResidual.SylowSupplement

/-!
# Marked maximal parabolics in the reduced six-cover branch

For the actual conjugation action on K/O₂,Z(K), the two-residual of its
kernel lies in the literal Y = O²(O₂,Z(K)). Indeed, its image in H/K is
trivial, its remaining image lies in O₂,Z(K), and two-perfectness places
that image in Y. Restricting the prescribed Sylow subgroup to the kernel
therefore puts the whole kernel in YT ≤ L₁T.

The theta identity and Y < L₁ give an order-three generator outside Y.
Such an element cannot act trivially: otherwise its odd order places it
in the residual of O₂,Z(K). Thus the seed has three-divisible action image.
Under the explicit natural-action hypothesis, the action range is the
inner A₆ or natural S₆. Their checked parabolic geometry gives ordinary
maximality, the marked join, and a conjugator marking both the Sylow and
the duad or syntheme parabolic. The coordinate maps commute with the
actual action and restrict to the supplied quotient map on K.

Source: Aschbacher–Smith, 13.8.21(2), printed p.956 (PDF p.973), after
reduction to the six-cover and exclusion of Y = L₁. The caller supplies
the trivial-diagram hypothesis for this H; no Mathieu replacement or
module for a different overgroup is used here.
-/

@[expose] public section

open Subgroup Theory.GroupAction.PCoreCentralModelAction
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
variable {G : Type*} [Group G] [Finite G]
variable {H K L₁ T G₁ M : Subgroup G}
variable (s : MarkedSetup H K L₁ T G₁ M)

/-- Conjugation on the supplied central quotient, in its actual A₆ coordinates. -/
noncomputable def MarkedSetup.sixAction
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) :
    H →* MulAut (alternatingGroup (Fin 6)) :=
  centralModelAction H K (@le_normalizer_of_normal_subgroupOf _ _ _ _
    s.component_normal s.component_le) e

/-- The action kernel has no two-residual outside the literal cover residual. -/
theorem MarkedSetup.sixAction_residual_le
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) :
    (pResidual 2 (s.sixAction e).ker).map (s.sixAction e).ker.subtype ≤
      (coverResidualIn K).subgroupOf H := by
  let := s.component_normal
  let a := s.sixAction e
  let N := a.ker
  let R := pResidual 2 N
  let f : R →* H := N.subtype.comp R.subtype
  let J := K.subgroupOf H
  let q := QuotientGroup.mk' J
  have ht := Chapter1.isSylowIn_iff.mp s.sylow
  have hj : J ⊔ T.subgroupOf H = ⊤ := by
    rw [← subgroupOf_sup s.component_le ht.2.1, ← s.generated, subgroupOf_self]
  have hp : IsPGroup 2 (H ⧸ J) :=
    isPGroup_quotient_of_sup_eq_top J (T.subgroupOf H) ht.1.comap_subtype hj
  have hr : IsPPerfect 2 R := isPPerfect_pResidual 2
  have hf := hr.hom_eq_one_of_isPGroup hp (q.comp f)
  have hfk (r : R) : f r ∈ J := by
    apply (QuotientGroup.eq_one_iff (f r)).mp
    exact congrArg (fun u : R →* (H ⧸ J) => u r) hf
  let g : R →* K := (H.subtype.comp f).codRestrict K hfk
  have hgc (r : R) : g r ∈ centralPreimage (pCore 2 K) := by
    have ha : a (inclusion s.component_le (g r)) = 1 := r.val.property
    change centralModelAction H K _ e (inclusion s.component_le (g r)) = 1 at ha
    rw [centralModelAction_inner] at ha
    apply (QuotientGroup.eq_one_iff (g r)).mp
    change QuotientGroup.mk' (centralPreimage (pCore 2 K)) (g r) = 1
    apply e.injective
    rw [map_one]
    apply AlternatingSix.ShadowLocal.inner_injective
    simpa only [map_one] using ha
  let c : R →* centralPreimage (pCore 2 K) := g.codRestrict _ hgc
  have hm := map_pResidual_le 2 c
  rw [(pResidual_eq_top_iff 2 R).mpr hr] at hm
  rintro x ⟨r, hr, rfl⟩
  let z : R := ⟨r, hr⟩
  exact ⟨g z, ⟨c z, hm ⟨z, trivial, rfl⟩, rfl⟩, rfl⟩

/-- The actual Sylow arrangement and Y ≤ L₁ absorb the full action kernel. -/
theorem MarkedSetup.sixAction_kernel_le_join
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) :
    (s.sixAction e).ker ≤ (L₁.subgroupOf H) ⊔ T.subgroupOf H := by
  obtain ⟨S, hS⟩ := s.sylow
  have hs : (S : Subgroup H) = T.subgroupOf H := by
    rw [← hS]
    exact (comap_map_eq_self (by simp [H.subtype.ker_eq_bot H.subtype_injective])).symm
  let N := (s.sixAction e).ker
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_normal N
  have hp := congrArg (fun V : Subgroup N => V.map N.subtype)
    (pResidual_sup_sylow_eq_top P)
  rw [Subgroup.map_sup, ← MonoidHom.range_eq_map, range_subtype, hP,
    subgroupOf_map_subtype] at hp
  change N ≤ _
  rw [← hp]
  exact sup_le ((s.sixAction_residual_le e).trans
    ((comap_mono s.proper_residual.le).trans le_sup_left))
    (inf_le_left.trans (hs ▸ le_sup_right))

omit [Finite G] in
/-- The theta generators and Y < L₁ force a surviving order-three seed image. -/
theorem MarkedSetup.sixAction_seed_three
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) :
    3 ∣ Nat.card ((L₁.subgroupOf H).map (s.sixAction e)) := by
  have hnot : ¬ {x : G | x ∈ H ⊓ M ∧ orderOf x = 3} ⊆ (coverResidualIn K : Set G) := by
    intro h
    apply s.proper_residual.not_ge
    rw [s.theta]
    exact (closure_le _).mpr h
  obtain ⟨x, hx, hxy⟩ := Set.not_subset.mp hnot
  have hxL : x ∈ L₁ := s.theta.symm ▸ subset_closure hx
  let z : H := ⟨x, hx.1.1⟩
  let a := s.sixAction e
  have hne : a z ≠ 1 := by
    intro ha
    let k : K := ⟨x, s.seed_le_component hxL⟩
    have hak : centralModelAction H K _ e (inclusion s.component_le k) = 1 := ha
    rw [centralModelAction_inner] at hak
    have hk : k ∈ centralPreimage (pCore 2 K) := by
      apply (QuotientGroup.eq_one_iff k).mp
      change QuotientGroup.mk' (centralPreimage (pCore 2 K)) k = 1
      apply e.injective
      rw [map_one]
      apply AlternatingSix.ShadowLocal.inner_injective
      simpa only [map_one] using hak
    let c : centralPreimage (pCore 2 K) := ⟨k, hk⟩
    have hc : orderOf c = 3 := by
      rw [← (centralPreimage (pCore 2 K)).orderOf_coe c, ← K.orderOf_coe k]
      exact hx.2
    have hr : c ∈ pResidual 2 (centralPreimage (pCore 2 K)) :=
      mem_pResidual_of_orderOf_coprime (hc ▸ (by decide : Nat.Coprime 2 3))
    exact hxy ⟨k, ⟨c, hr, rfl⟩, rfl⟩
  have hz : orderOf z = 3 := (H.orderOf_coe z).symm.trans hx.2
  have ho : orderOf (a z) = 3 := orderOf_eq_prime
    (by rw [← map_pow, ← hz, pow_orderOf_eq_one, map_one]) hne
  let y : (L₁.subgroupOf H).map a := ⟨a z, ⟨z, hxL, rfl⟩⟩
  have hy : orderOf y = 3 := (((L₁.subgroupOf H).map a).orderOf_coe y).symm.trans ho
  exact hy ▸ orderOf_dvd_natCard y

private theorem transport_geometry {X : Type*} [Group X] [Finite X]
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6))
    (f : H →* X) (hf : Function.Surjective f)
    (i : X →* MulAut (alternatingGroup (Fin 6))) (hi : Function.Injective i)
    (ha : i.comp f = s.sixAction e)
    (Geom : Subgroup X → Subgroup X → Prop)
    (native : ∀ (P : Sylow 2 X) (J A : Subgroup X),
      (P : Subgroup X) ≤ J → A ≤ J → J ≠ ⊤ → 3 ∣ Nat.card A →
      IsCoatom J ∧ J = A ⊔ P ∧ Geom P J) :
    IsCoatom ((H ⊓ M).subgroupOf H) ∧ H ⊓ M = L₁ ⊔ T ∧
      ∃ P : Sylow 2 X, (P : Subgroup X) = (T.subgroupOf H).map f ∧
        Geom P (((H ⊓ M).subgroupOf H).map f) := by
  let J := (H ⊓ M).subgroupOf H
  let A := L₁.subgroupOf H
  have ht := Chapter1.isSylowIn_iff.mp s.sylow
  have hTJ : T.subgroupOf H ≤ J := fun _ hx => ⟨ht.2.1 hx, s.sylow_le_M hx⟩
  have hAJ : A ≤ J := comap_mono s.seed_le_overlap
  have hk : f.ker ≤ A ⊔ T.subgroupOf H := by
    apply le_trans (show f.ker ≤ (s.sixAction e).ker from ?_) (s.sixAction_kernel_le_join e)
    intro x hx
    rw [← ha]
    change i (f x) = 1
    rw [show f x = 1 from hx, map_one]
  have hJker : f.ker ≤ J := hk.trans (sup_le hAJ hTJ)
  have hJ : J ≠ ⊤ := fun h => s.overlap_proper.not_ge (subgroupOf_eq_top.mp h)
  have hproper : J.map f ≠ ⊤ := by
    intro he
    have he' := congrArg (comap f) he
    rw [comap_map_eq_self hJker, comap_top] at he'
    exact hJ he'
  have hthree : 3 ∣ Nat.card (A.map f) := by
    have h := s.sixAction_seed_three e
    rw [← ha, ← map_map, card_map_of_injective hi] at h
    exact h
  obtain ⟨S, hS⟩ := s.sylow
  have hs : (S : Subgroup H) = T.subgroupOf H := by
    rw [← hS]
    exact (comap_map_eq_self (by simp [H.subtype.ker_eq_bot H.subtype_injective])).symm
  let P := S.mapSurjective hf
  have hP : (P : Subgroup X) = (T.subgroupOf H).map f := by
    change (S : Subgroup H).map f = _
    rw [hs]
  obtain ⟨hm, he, hg⟩ := native P (J.map f) (A.map f)
    (hP ▸ map_mono hTJ) (map_mono hAJ) hproper hthree
  have hJe : J = A ⊔ T.subgroupOf H := by
    rw [hP, ← Subgroup.map_sup] at he
    have hh := congrArg (comap f) he
    rwa [comap_map_eq_self hJker, comap_map_eq_self hk] at hh
  refine ⟨?_, ?_, P, hP, hg⟩
  · have hm' := isCoatom_comap_of_surjective hf hm
    rwa [comap_map_eq_self hJker] at hm'
  · have hh := congrArg (map H.subtype) hJe
    simpa only [J, A, Subgroup.map_sup, map_subgroupOf_eq_of_le inf_le_left,
      map_subgroupOf_eq_of_le (s.seed_le_component.trans s.component_le),
      map_subgroupOf_eq_of_le ht.2.1] using hh

omit [Finite G] in
private theorem exists_coordinates {X D : Type*} [Group X] [Group D]
    (a : H →* D) (i : X →* D) (hi : Function.Injective i) (hr : a.range = i.range) :
    ∃ f : H →* X, Function.Surjective f ∧ i.comp f = a := by
  let b : X ≃* a.range := (MonoidHom.ofInjective hi).trans (MulEquiv.subgroupCongr hr.symm)
  let f := b.symm.toMonoidHom.comp a.rangeRestrict
  refine ⟨f, b.symm.surjective.comp a.rangeRestrict_surjective, ?_⟩
  ext x
  exact congrArg Subtype.val (b.apply_symm_apply (a.rangeRestrict x))

open Theory.SpecificGroups.SymmetricSix

/-- Actual quotient-compatible coordinates and the incident Sylow marking. -/
def MarkedSetup.SixParabolicCoordinates
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6)) : Prop :=
  (∃ f : H →* A6, Function.Surjective f ∧
    MulAut.conj.comp f = s.sixAction e ∧
    (∀ k : K, f (inclusion s.component_le k) = e (QuotientGroup.mk' _ k)) ∧
    ∃ (P : Sylow 2 A6) (g : A6),
      (P : Subgroup A6) = (T.subgroupOf H).map f ∧
      (MulAut.conj g).mapSubgroup a6Borel = (P : Subgroup A6) ∧
      (((H ⊓ M).subgroupOf H).map f = (MulAut.conj g).mapSubgroup a6DuadStabilizer ∨
       ((H ⊓ M).subgroupOf H).map f = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer)) ∨
  (∃ f : H →* S6, Function.Surjective f ∧
    AlternatingSix.ShadowLocal.permutationAction.comp f = s.sixAction e ∧
    (∀ k : K, f (inclusion s.component_le k) = (e (QuotientGroup.mk' _ k) : S6)) ∧
    ∃ (P : Sylow 2 S6) (g : S6),
      (P : Subgroup S6) = (T.subgroupOf H).map f ∧
      (MulAut.conj g).mapSubgroup borel = (P : Subgroup S6) ∧
      (((H ⊓ M).subgroupOf H).map f = (MulAut.conj g).mapSubgroup duadStabilizer ∨
       ((H ⊓ M).subgroupOf H).map f = (MulAut.conj g).mapSubgroup synthemeStabilizer))

/-- Reduced-cover marked parabolic geometry, conditional only on the displayed
source setup, actual central quotient, and trivial diagram action. -/
theorem MarkedSetup.six_marked_parabolic
    (e : (K ⧸ centralPreimage (pCore 2 K)) ≃* alternatingGroup (Fin 6))
    (hdiagram : (s.sixAction e).range ≤ AlternatingSix.ShadowLocal.natural) :
    IsCoatom ((H ⊓ M).subgroupOf H) ∧ H ⊓ M = L₁ ⊔ T ∧
      Source.starImage H (H ⊓ M) = Source.starImage H (L₁ ⊔ T) ∧ s.SixParabolicCoordinates e := by
  have hi : AlternatingSix.ShadowLocal.inner ≤ (s.sixAction e).range :=
    centralModelAction_inner_le_range H K _ s.component_le e
  rcases six_eq_inner_or_natural (s.sixAction e).range hi hdiagram with hr | hr
  · obtain ⟨f, hf, ha⟩ := exists_coordinates (s.sixAction e) MulAut.conj
      AlternatingSix.ShadowLocal.inner_injective hr
    obtain ⟨hm, he, P, hP, g, hg, hj⟩ := transport_geometry s e f hf MulAut.conj
      AlternatingSix.ShadowLocal.inner_injective ha
      (fun S J => ∃ g : A6,
        (MulAut.conj g).mapSubgroup a6Borel = S ∧
        (J = (MulAut.conj g).mapSubgroup a6DuadStabilizer ∨
         J = (MulAut.conj g).mapSubgroup a6SynthemeStabilizer)) CoverParabolics.six_marked_parabolic
    refine ⟨hm, he, congrArg (Source.starImage H) he, Or.inl ⟨f, hf, ha, ?_, P, g, hP, hg, hj⟩⟩
    intro k
    apply AlternatingSix.ShadowLocal.inner_injective
    have hx := DFunLike.congr_fun ha (inclusion s.component_le k)
    exact hx.trans (centralModelAction_inner H K _ s.component_le e k)
  · obtain ⟨f, hf, ha⟩ := exists_coordinates (s.sixAction e)
      AlternatingSix.ShadowLocal.permutationAction
      AlternatingSix.ShadowLocal.permutationAction_injective hr
    obtain ⟨hm, he, P, hP, g, hg, hj⟩ := transport_geometry s e f hf
      AlternatingSix.ShadowLocal.permutationAction
      AlternatingSix.ShadowLocal.permutationAction_injective ha
      (fun S J => ∃ g : S6,
        (MulAut.conj g).mapSubgroup borel = S ∧
        (J = (MulAut.conj g).mapSubgroup duadStabilizer ∨
         J = (MulAut.conj g).mapSubgroup synthemeStabilizer)) symmetricSix_marked_parabolic
    refine ⟨hm, he, congrArg (Source.starImage H) he, Or.inr ⟨f, hf, ha, ?_, P, g, hP, hg, hj⟩⟩
    intro k
    apply AlternatingSix.ShadowLocal.permutationAction_injective
    rw [AlternatingSix.ShadowLocal.permutationAction_coe]
    have hx := DFunLike.congr_fun ha (inclusion s.component_le k)
    exact hx.trans (centralModelAction_inner H K _ s.component_le e k)

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.FieldComponents.SmallCovers.Reduction.LocalGeometry.CoverParabolics
