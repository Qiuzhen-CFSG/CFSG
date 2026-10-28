module
public import CFSG.Quasithin.Chapter3.Section01.SourceThompsonResidual
public import CFSG.Quasithin.ChapterB.Section06To07.Structure
public import Theory.GroupTheory.SylowPreimageNormalizer
public import Theory.GroupTheory.SylowNormalRestriction
public import CFSG.Quasithin.ChapterB.Section06To07.FFClassification.Quotient
public import Theory.Representation.BinaryOffender.IrreducibleResidual

/-!
# Lifting the chief-image geometry for Thompson centralization

A subgroup of the chief image inside the fixed Sylow subgroup is lifted by
intersecting its full preimage with that same Sylow subgroup. Its kernel
intersection is Sylow in the kernel, so the relative Frattini argument lifts
its entire normalizer, including when the kernel contains odd-order elements.
A minimal actor-normalized lift of the image commutator is its own commutator
with the original actor. Minimal parabolicity lifts generation with the Sylow.

These actual subgroups supply the normalizer, index, commutator, and generation
inputs to Thompson replacement. The qrc application derives the balanced
ranks and the sharp FF-offender image from the same original minimal actor.
Its remaining premise is concrete subgroup geometry on the finite chief image.
The older symmetric-three subgroup selection API remains available separately.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), 3.1.9 and
15.1.12(3–4), printed pp.577–578 and1090.
-/

public section
open Subgroup Representation Representation.BinaryOffender NoncentralChiefRefinement Stellmacher
open scoped IsMulCommutative ENNReal
namespace CFSG.Quasithin.Chapter3
open ChapterD ChapterD.UniqueFactor Theory.GroupTheory
variable {G D : Type*} [Group G] [Finite G] [Group D]

/-- Lift image subgroup geometry through the actual minimal-parabolic quotient.
The Sylow intersection controls normalizers even when the kernel has odd order. -/
theorem exists_thompson_geometry_of_image
    (T : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver T ⊤)
    (q : G →* D) (hq : Function.Surjective q)
    (hcore : pCore 2 D = ⊥)
    (hker : q.ker ≤ ChapterB.minimalParabolicCore T hP)
    (A : Subgroup G) (hAT : A ≤ T)
    (Rbar Lbar : Subgroup D)
    (hRT : Rbar ≤ (T : Subgroup G).map q)
    (hAR : A.map q ≤ normalizer (Rbar : Set D))
    (hLR : Lbar ≤ normalizer (Rbar : Set D))
    (hAL : A.map q ≤ normalizer (Lbar : Set D))
    (hidx : Rbar.relIndex (A.map q) = 2)
    (hcomm : Lbar = ⁅Lbar, A.map q⁆)
    (hgen : Lbar ⊔ (T : Subgroup G).map q = ⊤) :
    ∃ R L : Subgroup G,
      pCore 2 G ≤ R ∧ R ≤ T ∧ R.relIndex A = 2 ∧
      L ≤ normalizer (R : Set G) ∧ L = ⁅L,A⁆ ∧ L ⊔ T = ⊤ := by
  classical
  have hmap (K : Subgroup G) (J : Subgroup D) (hJ : J ≤ K.map q) :
      (K ⊓ J.comap q).map q = J := by
    apply le_antisymm
    · rintro x ⟨y,hy,rfl⟩
      exact hy.2
    · intro x hx
      obtain ⟨y,hy,rfl⟩ := hJ hx
      exact ⟨y,⟨hy,hx⟩,rfl⟩
  let R := (T : Subgroup G) ⊓ Rbar.comap q
  have hRm : R.map q = Rbar := by
    exact hmap _ _ hRT
  have hQk : pCore 2 G ≤ q.ker := by
    have hn : ((pCore 2 G).map q).Normal := Subgroup.Normal.map inferInstance q hq
    have hh : (pCore 2 G).map q ≤ pCore 2 D := le_sSup ⟨hn, pCore_isPGroup.map q⟩
    rw [hcore] at hh
    exact (map_le_iff_le_comap.mp hh)
  have hQR : pCore 2 G ≤ R :=
    le_inf (pCore_isPGroup.le_sylow_of_normal T)
      (hQk.trans (by intro x hx; change q x ∈ Rbar; rw [MonoidHom.mem_ker.mp hx]; exact Rbar.one_mem))
  have hRk : R ⊓ q.ker = (T : Subgroup G) ⊓ q.ker := by
    apply le_antisymm (inf_le_inf_right _ inf_le_left)
    intro x hx
    refine ⟨⟨hx.1,?_⟩,hx.2⟩
    change q x ∈ Rbar
    rw [MonoidHom.mem_ker.mp hx.2]
    exact Rbar.one_mem
  obtain ⟨P,hPker⟩ := T.exists_sylow_map_eq_inf_of_normal q.ker
  have hNm : (normalizer (R : Set G)).map q = normalizer (Rbar : Set D) := by
    rw [←hRm]
    exact Subgroup.normalizer_map_eq_of_kernel_intersection R
      (T.isPGroup'.to_le inf_le_left) q hq P (hPker.trans hRk.symm)
  have hAN : A ≤ normalizer (R : Set G) :=
    (le_inf (hAT.trans (T : Subgroup G).le_normalizer)
      ((map_le_iff_le_comap.mp hAR).trans (Subgroup.le_normalizer_comap q))).trans
      inf_normalizer_le_normalizer_inf
  let B := normalizer (R : Set G) ⊓ Lbar.comap q
  have hBm : B.map q = Lbar := by
    exact hmap _ _ (hLR.trans_eq hNm.symm)
  have hAB : A ≤ normalizer (B : Set G) :=
    (le_inf (hAN.trans (normalizer (R : Set G)).le_normalizer)
      ((map_le_iff_le_comap.mp hAL).trans (Subgroup.le_normalizer_comap q))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨L,hL,hmin⟩ := exists_minimal_of_wellFoundedLT
    (fun L : Subgroup G => L ≤ normalizer (R : Set G) ∧ L.map q = Lbar ∧
      A ≤ normalizer (L : Set G)) ⟨B,inf_le_left,hBm,hAB⟩
  have hCL : ⁅L,A⁆ ≤ L := le_normalizer_iff_commutator_le_left.mp hL.2.2
  have hLC : L = ⁅L,A⁆ := by
    apply le_antisymm _ hCL
    apply hmin _ hCL
    exact ⟨hCL.trans hL.1,by rw [map_commutator,hL.2.1,←hcomm],
      normalizer_commutator_ge_right L A⟩
  have hLT : L ⊔ (T : Subgroup G) = ⊤ := by
    have hm : (L ⊔ (T : Subgroup G)).map q = ⊤ := by rw [Subgroup.map_sup,hL.2.1,hgen]
    have hs : (L ⊔ (T : Subgroup G)) ⊔ q.ker = ⊤ := by
      rw [← comap_map_eq,hm,comap_top]
    by_contra hne
    have hM := ChapterB.minimalParabolicMax_spec T hP
    have hLM := hP.1.le_maximal ⟨hM.2,hM.1.covBy_top⟩
      le_sup_right (lt_top_iff_ne_top.mpr hne)
    have hkM : q.ker ≤ ChapterB.minimalParabolicMax T hP := by
      rcases Subgroup.normal_le_core_or_sup_eq_top_of_uniqueMaximal
        hP.1 ⟨hM.2,hM.1⟩ (N := q.ker) with hc | hc
      · exact hc.trans (normalCore_le _)
      · exact (ChapterB.minimalParabolic_residual_not_le_core_of_factorization
          T hP q.ker hc hker).elim
    exact hM.1.ne_top (top_unique (hs ▸ sup_le hLM hkM))
  refine ⟨R,L,hQR,inf_le_left,?_,hL.1,hLC,hLT⟩
  have hi : A ⊓ R = A ⊓ Rbar.comap q := by
    dsimp only [R]
    rw [←inf_assoc,inf_eq_left.mpr hAT]
  rw [←inf_relIndex_left A R,hi,inf_relIndex_left,relIndex_comap,hidx]

/-- The image geometry on one irreducible chief action supplies the exact
normalizer and generation data used by Thompson replacement. -/
theorem thompson_centralizes_residual_of_chief_image_geometry
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
    (ρ : Representation (ZMod 2) G W) [IsIrreducible ρ]
    (S : Sylow 2 G) (hP : ChapterB.IsMinimalParabolicOver S ⊤)
    (U A : Subgroup G) [U.Normal] [IsElementaryAbelian 2 U]
    (hA : A ∈ elementaryAbelianMaxSubgroups (S : Subgroup G))
    (hmin : ∀ B ∈ elementaryAbelianMaxSubgroups (S : Subgroup G),
      ¬ B ≤ pCore 2 G → (pCore 2 G).relIndex A ≤ (pCore 2 G).relIndex B)
    (hU : U ≤ pCore 2 G) (hkernel : A ⊓ centralizer (U : Set G) ≤ pCore 2 G)
    (h1 : 2 * Nat.log 2 ((pCore 2 G).relIndex A) = fixedCodim (normalRepresentation U) A)
    (h2 : fixedCodim (normalRepresentation U) A =
      2 * Nat.log 2 ((centralizer (U : Set G)).relIndex (A ⊓ pCore 2 G)))
    (hc : U ⊓ centralizer (A : Set G) = U ⊓ centralizer (A ⊓ pCore 2 G : Set G))
    (Rbar Lbar : Subgroup (actionImage ρ))
    (hRT : Rbar ≤ (S : Subgroup G).map (actionHom ρ))
    (hAR : A.map (actionHom ρ) ≤ normalizer (Rbar : Set (actionImage ρ)))
    (hLR : Lbar ≤ normalizer (Rbar : Set (actionImage ρ)))
    (hAL : A.map (actionHom ρ) ≤ normalizer (Lbar : Set (actionImage ρ)))
    (hidx : Rbar.relIndex (A.map (actionHom ρ)) = 2)
    (hcomm : Lbar = ⁅Lbar, A.map (actionHom ρ)⁆)
    (hgen : Lbar ⊔ (S : Subgroup G).map (actionHom ρ) = ⊤) :
    omegaOneCenterAmbient (ChapterB.thompsonJ (S : Subgroup G) 1) ≤
      centralizer (pResidual 2 G : Set G) := by
  let q := actionHom ρ
  have hq : Function.Surjective q := ρ.asGroupHom.rangeRestrict_surjective
  have hcore := irreducible_image_twoCore_eq_bot ρ
  have hne : q.ker ≠ ⊤ := by
    intro he
    have ham : A.map q = ⊥ := by
      apply bot_unique
      exact (map_mono (show A ≤ q.ker by rw [he]; exact le_top)).trans_eq
        (map_ker_self q)
    rw [ham, relIndex_bot_right] at hidx
    norm_num at hidx
  have hker := (ChapterB.minimalParabolic_reduced_image S hP q hq hcore hne).1
  obtain ⟨R,L,hQR,hRS,hi,hLN,hLC,hLT⟩ := exists_thompson_geometry_of_image
    S hP q hq hcore hker A hA.1 Rbar Lbar hRT hAR hLR hAL hidx hcomm hgen
  apply ChapterB.omega_thompson_one_centralizes_residual_of_minimal_actor
    (S : Subgroup G) (pCore 2 G) R U A L S.isPGroup' hA hmin hU
    hQR hRS hkernel (MulAut.conjNormal : G →* MulAut U)
    (MulAut.conjNormal_ker_eq_centralizer U)
  · rw [← normalRepresentation_fixedCodim_eq_rank_difference U A]
    exact h1.symm
  · rw [← normalRepresentation_fixedCodim_eq_rank_difference U A]
    exact h2
  · exact hc
  · exact hi
  · exact hLN
  · exact hLC
  · exact hLT

/-- Source 15.1.12(4) from finite chief-image geometry for the original minimal
actor. The FF offender and sharp rank, the two balanced equalities, the kernel
bound, and the intrinsic minimal parabolic are all derived from the qrc source. -/
theorem QrcHypotheses.sqtk_thompson_omega_centralizes_residual_of_chief_geometry
    {T : Sylow 2 G} {M M₀ H V : Subgroup G}
    (h : QrcHypotheses T M M₀ H V) (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hM : IsMaximalTwoLocal M)
    (hu : ∀ N : Subgroup G, IsMaximalTwoLocal N → M₀ ≤ N → N = M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (V : Set G))
    (hne : V ≠ ⊥) (hV : V ≤ twoCoreIn H)
    (hdual : ¬ DualFF (h.toQRCConfiguration (h.no_common_normal hu)))
    (hq : letI := h.module_elementary
      quadraticRatio (imageRepresentation M₀ V h.module_normalized) = 2)
    (hgeometry :
      let d := h.toQRCConfiguration (h.no_common_normal hu)
      let U := (conjugateSpan H V).subgroupOf H
      let S := T.subtype h.right_mem.1.1.2
      letI := d.module_elementary
      letI := source_elementary_span_of_notFF d hV (source_notFF_of_ratio_two d hq)
      letI : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
        ((span_le_right_core d hV).trans (twoCore_le H))
      ∀ A ∈ elementaryAbelianMaxSubgroups (S : Subgroup H), ¬ A ≤ pCore 2 H →
        IsQuadratic (normalRepresentation U) A →
        (∀ B ∈ elementaryAbelianMaxSubgroups (S : Subgroup H),
          ¬ B ≤ pCore 2 H → (pCore 2 H).relIndex A ≤ (pCore 2 H).relIndex B) →
        2 * Nat.log 2 ((pCore 2 H).relIndex A) = fixedCodim (normalRepresentation U) A →
        fixedCodim (normalRepresentation U) A =
          2 * Nat.log 2 ((centralizer (U : Set H)).relIndex (A ⊓ pCore 2 H)) →
        U ⊓ centralizer (A : Set H) = U ⊓ centralizer (A ⊓ pCore 2 H : Set H) →
        ∀ (s : SeriesOn U) (i : Fin s.series.length), ¬ s.Central i →
          let ρ := s.factorRepresentation i
          let q := actionHom ρ
          IsOffender (Representation.BinaryOffender.imageRepresentation ρ) (A.map q) →
          rank (A.map q) = fixedCodim
            (Representation.BinaryOffender.imageRepresentation ρ) (A.map q) →
          ∃ Rbar Lbar : Subgroup (actionImage ρ),
            Rbar ≤ (S : Subgroup H).map q ∧
            A.map q ≤ normalizer (Rbar : Set (actionImage ρ)) ∧
            Lbar ≤ normalizer (Rbar : Set (actionImage ρ)) ∧
            A.map q ≤ normalizer (Lbar : Set (actionImage ρ)) ∧
            Rbar.relIndex (A.map q) = 2 ∧
            Lbar = ⁅Lbar,A.map q⁆ ∧ Lbar ⊔ (S : Subgroup H).map q = ⊤) :
    omegaOneCenterAmbient (ChapterB.thompsonJ (T : Subgroup G) 1) ≤
      centralizer ((pResidual 2 H).map H.subtype : Set G) := by
  let d := h.toQRCConfiguration (h.no_common_normal hu)
  let := d.module_elementary
  have hnf := source_notFF_of_ratio_two d hq
  let := source_elementary_span_of_notFF d hV hnf
  let U := (conjugateSpan H V).subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf
    ((span_le_right_core d hV).trans (twoCore_le H))
  let S := T.subtype h.right_mem.1.1.2
  have hS : (S : Subgroup H).map H.subtype = T := map_subgroupOf_eq_of_le h.right_mem.1.1.2
  obtain ⟨A,hA,hAR,hquad,hmin,hall⟩ :=
    h.sqtk_minimal_actor_equalities hG hM hu hJ hne hV hdual hq
  obtain ⟨s⟩ := NoncentralChiefRefinement.SeriesOn.exists_series U
  have hs := hall s
  obtain ⟨i,j,hij,hi,hj⟩ := s.one_lt_noncentralCount_iff.mp (by omega)
  have hp := source_intrinsic_minimalParabolic_of_notFF d hne hnf S hS
  let : IsElementaryAbelian 2 A := hA.2.1
  have hak := MultipleFactors.source_chief_sylow_kernel U S hp s i hi A hA.1
  have hn : ¬ A ≤ (s.factorRepresentation i).ker := by
    intro hn
    apply hAR
    have he : A ⊓ (s.factorRepresentation i).ker = A := inf_eq_left.mpr hn
    rw [he] at hak
    exact hak.le.trans inf_le_right
  have hidx : (s.factorRepresentation i).ker.relIndex A = (pCore 2 H).relIndex A := by
    rw [← inf_relIndex_left,hak,inf_relIndex_left]
  have he : rank (actionSubgroup (s.factorRepresentation i) A) =
      fixedCodim (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
        (actionSubgroup (s.factorRepresentation i) A) := by
    rw [rank_actionSubgroup_eq_log_relIndex,fixedCodim_actionSubgroup,hidx]
    exact hs.2.2.2.2.1 i hi
  have hoff : IsOffender
      (Representation.BinaryOffender.imageRepresentation (s.factorRepresentation i))
      (actionSubgroup (s.factorRepresentation i) A) :=
    ⟨elementary_actionSubgroup _ hn,he.ge⟩
  obtain ⟨Rbar,Lbar,hRT,hARbar,hLR,hAL,hindex,hcomm,hgen⟩ :=
    hgeometry A hA hAR hquad hmin hs.2.1 hs.2.2.1 hs.2.2.2.1 s i hi hoff he
  have hUN : U ≤ pCore 2 H := by
    intro u hu
    obtain ⟨x,hx,he⟩ := span_le_right_core d hV hu
    exact H.subtype_injective he ▸ hx
  have hkernel : A ⊓ centralizer (U : Set H) ≤ pCore 2 H :=
    (inf_le_inf_right _ hA.1).trans
      (source_span_centralizer_sylow_le_core d hne hV hnf S hS)
  let := s.factorRepresentation_irreducible i
  have hc := thompson_centralizes_residual_of_chief_image_geometry
    (s.factorRepresentation i) S hp U A hA hmin hUN hkernel
    hs.2.1 hs.2.2.1 hs.2.2.2.1 Rbar Lbar hRT hARbar hLR hAL hindex hcomm hgen
  have hm := Subgroup.map_mono (f := H.subtype) hc
  rw [← omegaOneCenterAmbient_map_injective H.subtype H.subtype_injective,
    ← ChapterB.thompsonJ_map_injective H.subtype H.subtype_injective, hS] at hm
  exact hm.trans (by
    simpa only [Subgroup.coe_map] using
      Subgroup.map_centralizer_le_centralizer_image (pResidual 2 H : Set H) H.subtype)

end CFSG.Quasithin.Chapter3
