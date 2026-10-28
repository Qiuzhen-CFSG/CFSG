module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryParabolicSection
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.RadicalImages
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.SymplecticParabolic
public import Theory.GroupTheory.PResidual.FiniteImage
public import Theory.GroupTheory.PResidual.OddConjugateSpan
public import Theory.GroupTheory.QuotientIntersection
public import Theory.SpecificGroups.SL3.RadicalNormalizer
public import CFSG.Quasithin.ChapterC.Section02.SourceGeometry.StarSylow

/-!
# Transporting the cubic obstruction to the original star intersection

The comparison C/O₂(C) → C* has an odd central kernel. Two-perfectness of
M_C* therefore lifts to the image of the original intersection in C/O₂(C).
A reduced action kills O₂(C) when C is normal; if its full kernel lies in M,
that image maps onto C⁎ ∩ M⁎. This compares the two actual quotient maps
without identifying their kernels or assuming the action kernel is a two-group.

The cubic movement obstruction excludes two-perfectness of this reduced
intersection, hence also of M_C*. The actual nonbinary Sp₄ model supplies a
marked maximal parabolic. For SL₃, the original non-Sylow radical excludes
the Sylow alternative in the radical-normalizer theorem; maximality promotes
the normalizer to M_C*. Thus both nonbinary star models, as well as the
literal C.2.7 parabolic predicates, are excluded.

NonFFSourceDoubledBinaryStarIntersection supplies every premise on the same
chosen component and orbit. Ambient paired-plane containment and the binary
endgame remain separate obligations.
Source: Aschbacher--Smith, proof after 7.7.10, printed pp.708--709, and
C.2.7, printed pp.145--147, refs/quasithin.pdf.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarIntersection
open Chapter1.RadicalExclusions.ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]

private theorem twoPerfect_of_odd_kernel {X Z : Type*} [Group X] [Finite X] [Group Z]
    (f : X →* Z) (hf : Function.Surjective f)
    (hk : Nat.Coprime 2 (Nat.card f.ker)) (hp : IsPPerfect 2 Z) : IsPPerfect 2 X := by
  have hker : f.ker ≤ pResidual 2 X := by
    intro x hx
    exact mem_pResidual_of_orderOf_coprime (hk.of_dvd_right (f.ker.orderOf_dvd_natCard hx))
  apply (pResidual_eq_top_iff 2 X).mp
  have he := congrArg (comap f) (map_pResidual_of_surjective 2 f hf)
  rwa [(pResidual_eq_top_iff 2 Z).mpr hp, comap_top, comap_map_eq,
    sup_eq_left.mpr hker] at he

private theorem twoPerfect_of_odd_kernel_image {X Z : Type*} [Group X] [Finite X] [Group Z]
    (f : X →* Z) (B : Subgroup X) (hk : Nat.Coprime 2 (Nat.card f.ker))
    (hp : IsPPerfect 2 (B.map f)) : IsPPerfect 2 B := by
  let s := f.subgroupMap B
  have hi : Function.Injective (fun x : s.ker => (⟨x.val.val,congrArg Subtype.val x.property⟩ : f.ker)) := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : f.ker => (x : X)) he
  exact twoPerfect_of_odd_kernel s (f.subgroupMap_surjective B)
    (hk.of_dvd_right (Subgroup.card_dvd_of_injective
      { toFun := fun x => ⟨x.val.val,congrArg Subtype.val x.property⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl } hi)) hp

omit [Finite G] in
/-- The original intersection is mapped to the literal star intersection. -/
theorem intersection_star_map (K R M : Subgroup G) :
    (M.subgroupOf K).map (toStarImage K R) =
      (starM K R M).subgroupOf (starImage K R K) := by
  apply map_injective (starImage K R K).subtype_injective
  rw [map_subgroupOf_eq_of_le (starM_le K R M)]
  ext x
  constructor
  · rintro ⟨y,⟨k,hk,rfl⟩,rfl⟩
    exact ⟨inclusion (show K ≤ K ⊔ R from le_sup_left) k,⟨hk,k.property⟩,rfl⟩
  · rintro ⟨k,hk,rfl⟩
    exact ⟨toStarImage K R ⟨k,hk.2⟩,⟨⟨k,hk.2⟩,hk.1,rfl⟩,rfl⟩

/-- Oddness of the central comparison kernel lifts two-perfectness without
identifying either quotient with the other. -/
theorem core_intersection_twoPerfect {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hp : IsPPerfect 2 ((starM K R M).subgroupOf (starImage K R K))) :
    IsPPerfect 2 ((M.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))) := by
  let f := coreToStar h.normalizes
  have hk : f.ker ≤ center (K ⧸ pCore 2 K) :=
    coreToStar_ker_le_center_of_bound h.normalizes
      (ChapterC.C27Source.kernel_offender_from_source h).1.upper
  have ho : Nat.Coprime 2 (Nat.card f.ker) := Nat.prime_two.coprime_iff_not_dvd.mpr
    (PerfectCentralCovering.not_dvd_card_central_of_pCore_eq_bot
      (pCore_quotient_pCore_eq_bot 2) f.ker hk)
  apply twoPerfect_of_odd_kernel_image f _ ho
  rw [map_map,show f.comp (QuotientGroup.mk' (pCore 2 K)) = toStarImage K R from rfl,
    intersection_star_map]
  exact hp

omit [Finite G] in
/-- A reduced quotient kills the two-core of a normal component. -/
private theorem normal_component_core_killed {Z : Type*} [Group Z]
    (K : Subgroup G) [K.Normal] (q : G →* Z) (hq : Function.Surjective q)
    (hz : pCore 2 Z = ⊥) : pCore 2 K ≤ (q.comp K.subtype).ker := by
  have hn : ((pCore 2 K).map K.subtype).Normal := inferInstance
  have hl : ((pCore 2 K).map K.subtype).map q ≤ pCore 2 Z :=
    le_sSup ⟨hn.map q hq,(pCore_isPGroup.map K.subtype).map q⟩
  rw [hz,map_map] at hl
  exact (Subgroup.map_eq_bot_iff _).mp (le_bot_iff.mp hl)


/-- A star intersection which is two-perfect has two-perfect image under
any action of the component that kills its two-core. -/
theorem intersection_image_twoPerfect {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    {Z : Type*} [Group Z] (q : K →* Z) (hk : pCore 2 K ≤ q.ker)
    (hp : IsPPerfect 2 ((starM K R M).subgroupOf (starImage K R K))) :
    IsPPerfect 2 ((M.subgroupOf K).map q) := by
  let f := QuotientGroup.lift (pCore 2 K) q hk
  have hh := (core_intersection_twoPerfect h hp).of_surjective
    (f.subgroupMap ((M.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))))
    (f.subgroupMap_surjective _)
  have he : ((M.subgroupOf K).map (QuotientGroup.mk' (pCore 2 K))).map f =
      (M.subgroupOf K).map q := by
    rw [map_map]
    rfl
  exact he ▸ hh

/-- Compare the original intersection in the star quotient and a reduced
action. Both full centralizer kernels remain in their own quotient maps. -/
theorem reduced_intersection_twoPerfect {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal]
    {Z : Type*} [Group Z] (q : H →* Z) (hq : Function.Surjective q)
    (hz : pCore 2 Z = ⊥) (hkM : q.ker ≤ M.subgroupOf H)
    (hp : IsPPerfect 2 ((starM K R M).subgroupOf (starImage K R K))) :
    IsPPerfect 2 ((K.subgroupOf H).map q ⊓ (M.subgroupOf H).map q : Subgroup Z) := by
  let e : K ≃* K.subgroupOf H := (subgroupOfEquivOfLe h.component.1).symm
  let f : K →* Z := q.comp (inclusion h.component.1)
  have hk : pCore 2 K ≤ f.ker := by
    intro k hk
    have he : e k ∈ pCore 2 (K.subgroupOf H) := by
      rw [←pCore_map_iso 2 e]
      exact mem_map_of_mem e.toMonoidHom hk
    exact normal_component_core_killed (K.subgroupOf H) q hq hz he
  have hi := intersection_image_twoPerfect h f hk hp
  have hm : (M.subgroupOf K).map f =
      (K.subgroupOf H).map q ⊓ (M.subgroupOf H).map q := by
    rw [←map_inf_of_ker_le q _ _ hkM]
    ext z
    constructor
    · rintro ⟨k,hk,rfl⟩
      exact ⟨inclusion h.component.1 k,⟨k.property,hk⟩,rfl⟩
    · rintro ⟨k,hk,rfl⟩
      exact ⟨⟨k.val,hk.1⟩,hk.2,rfl⟩
  exact hm ▸ hi

/-- The cubic movement obstruction in the reduced action excludes the
literal C.2.7 parabolic predicates in its star quotient. -/
theorem star_parabolic_exclusions {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal]
    {Z : Type*} [Group Z] (q : H →* Z) (hq : Function.Surjective q)
    (hz : pCore 2 Z = ⊥) (hkM : q.ker ≤ M.subgroupOf H)
    (hnot : ¬ IsPPerfect 2 ((K.subgroupOf H).map q ⊓ (M.subgroupOf H).map q : Subgroup Z)) :
    let P := (starM K R M).subgroupOf (starImage K R K)
    ¬ IsPPerfect 2 P ∧ ¬ IsSp4FourMaximalParabolic P ∧
      (∀ (F : Type) [Field F] [Finite F] (n : ℕ), Nat.card F = 2 ^ n → 1 < n →
        ¬ IsLinearMaximalParabolic P 3 F) := by
  dsimp only
  have hp := fun hh => hnot (reduced_intersection_twoPerfect h q hq hz hkM hh)
  exact ⟨hp,DoubledBinaryParabolicSection.no_sp4Four_maximalParabolic _ hp,
    fun F _ _ n hF hn => DoubledBinaryParabolicSection.no_linearThree_maximalParabolic _ hp hF hn⟩

/-- The original Sp₄ star model supplies its actual marked parabolic, so
all nonbinary symplectic star components are excluded. -/
theorem no_nonbinary_symplectic_star {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K)
    (hp : ¬ IsPPerfect 2 ((starM K R M).subgroupOf (starImage K R K)))
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree) :
    ¬ Nonempty (starImage K R K ≃* Theory.SpecificGroups.SymplecticFour.Sp F.Carrier) := by
  intro ⟨e⟩
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  obtain ⟨g,hg⟩ := ChapterC.C27Source.star_symplectic_marked_parabolic_from_source h e hfour
  let a := e.trans (MulAut.conj g)
  have ha : a.toMonoidHom = (MulAut.conj g).toMonoidHom.comp e.toMonoidHom := rfl
  rw [map_map,←ha] at hg
  rcases hg with hg | hg
  · let b := (a.subgroupMap _).trans (MulEquiv.subgroupCongr hg)
    exact hp ((DoubledBinaryParabolicSection.symplectic_point_twoPerfect F.card_eq hn).of_surjective
      b.symm.toMonoidHom b.symm.surjective)
  · let b := (a.subgroupMap _).trans (MulEquiv.subgroupCongr hg)
    exact hp ((DoubledBinaryParabolicSection.symplectic_plane_twoPerfect F.card_eq hn).of_surjective
      b.symm.toMonoidHom b.symm.surjective)


/-- The original non-Sylow radical forces a nonbinary linear-three star
intersection to be a full parabolic, which the reduced cubic action excludes. -/
theorem no_nonbinary_linear_star {H K R M : Subgroup G}
    (h : Input KnownSimple.IsKnownSimple H R M K) [(K.subgroupOf H).Normal]
    (hsyl : ¬ Chapter1.IsSylowIn 2 R (K ⊔ R))
    (hp : ¬ IsPPerfect 2 ((starM K R M).subgroupOf (starImage K R K)))
    (F : ChapterB.QuasisimpleSource.BinaryField) (hn : 1 < F.degree) :
    ¬ Nonempty (starImage K R K ≃* Matrix.SpecialLinearGroup (Fin 3) F.Carrier) := by
  intro ⟨e⟩
  have hfour : 4 ≤ Nat.card F.Carrier := by
    rw [F.card_eq]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ F.degree)
  have hc : Nat.card (Matrix.SpecialLinearGroup (Fin 3) F.Carrier) =
      Nat.card F.Carrier ^ 3 * (Nat.card F.Carrier ^ 3 - 1) * (Nat.card F.Carrier ^ 2 - 1) := by
    rw [card_eq_card_quotient_mul_card_subgroup (center (Matrix.SpecialLinearGroup (Fin 3) F.Carrier)),
      Atlas.ExceptionalSupport.card_sl_center]
    exact Matrix.PSL3.LinearThree.card_projective_mul_scalar F.Carrier
  have hlarge : 40320 < Nat.card (starImage K R K) := by
    rw [Nat.card_congr e.toEquiv,hc]
    have hh := Nat.mul_le_mul
      (Nat.mul_le_mul (Nat.pow_le_pow_left hfour 3)
        (Nat.sub_le_sub_right (Nat.pow_le_pow_left hfour 3) 1))
      (Nat.sub_le_sub_right (Nat.pow_le_pow_left hfour 2) 1)
    exact lt_of_lt_of_le (by norm_num : 40320 < 4 ^ 3 * (4 ^ 3 - 1) * (4 ^ 2 - 1)) hh
  obtain ⟨hr,hnorm⟩ := ChapterC.C27Source.star_intersection_placement_from_source_of_large_order h hlarge
  let C := starImage K R K
  let U := (starImage K R R).subgroupOf C
  let P := (starM K R M).subgroupOf C
  have hu := hr.map_equiv e
  rcases Matrix.PSL3.LinearThree.RadicalNormalizer.radical_normalizer_parabolic_or_sylow
    (U.map e.toMonoidHom) hu hn F.card_eq with ⟨b,hb⟩ | ⟨S,hS⟩
  · let a := Matrix.HigherLinear.SubspaceTransport.slConj b
    let B := (P.map e.toMonoidHom).map a.toMonoidHom
    have hB : B ≠ ⊤ := by
      intro ht
      have hproper : P ≠ ⊤ := fun hP =>
        (ChapterC.C27Source.star_thompson_intersection_from_source h).2.not_ge (subgroupOf_eq_top.mp hP)
      apply hproper
      have h₁ := congrArg (comap a.toMonoidHom) ht
      have h₂ : P.map e.toMonoidHom = ⊤ := by
        simpa only [B,comap_map_eq_self_of_injective (f := a.toMonoidHom) a.injective,comap_top] using h₁
      have h₃ := congrArg (comap e.toMonoidHom) h₂
      simpa only [comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective,comap_top] using h₃
    have hNB : (normalizer (U.map e.toMonoidHom : Set _)).map a.toMonoidHom ≤ B := by
      rw [←map_equiv_normalizer_eq]
      exact map_mono (map_mono hnorm)
    let d : P ≃* B := (e.subgroupMap P).trans (a.subgroupMap (P.map e.toMonoidHom))
    rcases hb with hb | hb
    · have he : B = Matrix.PSL3.LinearThree.pointParabolicSL F.Carrier :=
        ((Matrix.PSL3.LinearThree.pointParabolicSL_isCoatom F.Carrier).le_iff_eq hB).mp (hb ▸ hNB)
      let c := d.trans (MulEquiv.subgroupCongr he)
      exact hp ((DoubledBinaryParabolicSection.linear_point_twoPerfect F.card_eq hn).of_surjective
        c.symm.toMonoidHom c.symm.surjective)
    · have he : B = Matrix.PSL3.LinearThree.lineParabolicSL F.Carrier :=
        ((Matrix.PSL3.LinearThree.lineParabolicSL_isCoatom F.Carrier).le_iff_eq hB).mp (hb ▸ hNB)
      let c := d.trans (MulEquiv.subgroupCongr he)
      exact hp ((DoubledBinaryParabolicSection.linear_line_twoPerfect F.card_eq hn).of_surjective
        c.symm.toMonoidHom c.symm.surjective)
  · let S' := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
    have hs' : (S' : Subgroup C) = U := by
      change (S : Subgroup _).map e.symm.toMonoidHom = U
      rw [hS]
      ext x
      constructor
      · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
        simpa using hz
      · intro hx
        exact ⟨e x,⟨x,hx,rfl⟩,e.symm_apply_apply x⟩
    have hSR : (S' : Subgroup C).map C.subtype ≤ starImage K R R := by
      rw [hs',subgroupOf_map_subtype]
      exact inf_le_left
    obtain ⟨T,hT⟩ := ChapterC.C27Source.radical_sylow_of_star_component_sylow h S' hSR
    apply hsyl
    refine ⟨T,?_⟩
    rw [hT,map_subgroupOf_eq_of_le (show R ≤ K ⊔ R from le_sup_right)]

end CFSG.Quasithin.Chapter7.NormalizedSource.DoubledBinaryStarIntersection
