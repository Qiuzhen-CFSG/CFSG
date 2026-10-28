module
public import CFSG.Quasithin.ChapterG.Section11.CorrectedReduction
public import CFSG.Quasithin.ChapterG.Section10.RankTwoSolvableSource


/-!
# Type-a₂ exclusion of nondegenerate exchanged constituents

The original rank-two involution preserves each component constituent and
moves every nonzero constituent. On a nondegenerate constituent its type-a₂
displacement form is alternating, hence has even rank. That constituent contributes at least two to displacement; its
nonzero complementary constituent contributes at least one more. This
contradicts total displacement rank at most two. This removes every nondegenerate exchanged natural branch.

Together with the normal-cubic source theorem, moved-plane nontransitivity
also removes the solvable degree-six branch. The resulting specialized
reduction feeds the literal strict quotient in `StrictWholeComponent`.
It retains the whole-component branch and the exceptional whole S₈ action;
it does not assert exhaustive G.11.2 recognition.
Source: Aschbacher--Smith G.11.6 and 6.2.16(6), 6.2.18--19,
printed pp.365--366,689--691.
-/

open Subgroup Module Representation Representation.BinaryOffender Theory.GroupTheory
open scoped IsMulCommutative
public noncomputable section
namespace CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition

private theorem even_constituent_displacement
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (B : LinearMap.BilinForm (ZMod 2) V) (hB : B.IsAlt)
    (I : Submodule (ZMod 2) V) (hnd : (B.restrict I).Nondegenerate)
    (δ : V →ₗ[ZMod 2] V) (hδ : I.map δ ≤ I) (ha : ∀ u, B u (δ u) = 0) :
    Even (finrank (ZMod 2) (I.map δ)) := by
  let N : I →ₗ[ZMod 2] I := (δ.comp I.subtype).codRestrict I (fun u =>
    hδ (Submodule.mem_map_of_mem u.property))
  let C := (B.restrict I).compLeft N
  have hC : C.IsAlt := fun u => hB.eq_iff.mp (ha u)
  have hk : C.ker = N.ker := by
    ext u
    constructor
    · intro hu
      exact hnd.1 (N u) (fun w => LinearMap.congr_fun hu w)
    · intro hu
      ext w
      change B (N u) w = 0
      rw [hu]
      simp
  have hr : N.range.map I.subtype = I.map δ := by
    ext u
    constructor
    · rintro ⟨w,⟨t,rfl⟩,rfl⟩
      exact Submodule.mem_map_of_mem t.property
    · rintro ⟨w,hw,rfl⟩
      exact ⟨N ⟨w,hw⟩,⟨⟨w,hw⟩,rfl⟩,rfl⟩
  have he := AlternatingForm.even_finrank_sub_finrank_ker C hC
  have hd := N.finrank_range_add_finrank_ker
  rw [hk,← hd,Nat.add_sub_cancel_right] at he
  rw [← hr,Submodule.finrank_map_subtype_eq]
  exact he

variable {G V : Type*} [Group G] [Finite G] [AddCommGroup V]
  [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {ρ : Representation (ZMod 2) G V} {B : LinearMap.BilinForm (ZMod 2) V}
  {v : V} {W : Submodule (ZMod 2) V} {X : Subgroup G}
  [IsElementaryAbelian 2 X] {X₀ : Subgroup X}

/-- Type-a₂ excludes every nondegenerate exchanged constituent, with the
actual marked low-rank involution retained throughout. -/
theorem not_exchanged_nondegenerate_of_type_a2
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hS : NormalSylow ρ v X) (hn : ¬ Group.IsSolvable G)
    (a : G) (ha : a ∈ X)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a) ≤ 2)
    (hv : v ∈ RankTwo.movedSpace ρ a) (htype : ∀ u, B u (ρ a u) = 0)
    {L : Subgroup G} (hL : IsComponent G L) (hm : ⁅L,X⁆ ≠ ⊥)
    {I : Submodule (ZMod 2) V}
    (hI : Homogeneous.IsIrrPlusWith ρ (componentOrbit L ⊤) X I)
    (hgeo : Section10.ExchangedConstituentGeometry ρ B v W X I)
    (hnd : (B.restrict I).Nondegenerate) : False := by
  let H := componentOrbit L ⊤
  let := componentOrbit_top_normal L
  let R := invariantSubspace ρ H I hI.invariant
  obtain ⟨x,_,hc,_⟩ := exchanged_lowRank_pair h cover ⟨a,ha,hr,hv⟩ hS hn hL hm hI hgeo
  let Q := conjugateSubrepresentationOrderIso ρ H x R
  have hi := h.irreducible_of_not_solvable hn
  have hR : IsIrreducible R.toRepresentation := hI.isIrrPlus.irreducible_of_normal_restriction ρ hi H
  have hQ : IsIrreducible Q.toRepresentation :=
    (Subrepresentation.irreducible_iff_isAtom Q).mpr
      (((conjugateSubrepresentationOrderIso ρ H x).isAtom_iff R).mpr
        ((Subrepresentation.irreducible_iff_isAtom R).mp hR))
  have hQspace : Q.toSubmodule = I.map (ρ x) :=
    conjugateSubrepresentationOrderIso_toSubmodule ρ H x R
  have hstable (J : Subrepresentation (ρ.comp H.subtype)) (hj : IsIrreducible J.toRepresentation) :
      J.toSubmodule.map (ρ a) = J.toSubmodule := by
    have hd : 3 ≤ finrank (ZMod 2) J.toSubmodule := by
      let : Group.IsPerfect H := hL.orbit_isPerfect ⊤
      apply PerfectInvolutionExtension.constituent_dimension ρ hi H ?_ J hj
      rw [ρ.ker_eq_bot h.faithful]
      exact fun hh => hL.componentOrbit_top_ne_bot (le_bot_iff.mp hh)
    apply map_constituent_eq_self_of_displacement_lt ρ H a J hj
    exact lt_of_le_of_lt hr (by omega)
  let δ := ρ a - LinearMap.id
  have hle (J : Subrepresentation (ρ.comp H.subtype)) (hj : IsIrreducible J.toRepresentation) :
      J.toSubmodule.map δ ≤ J.toSubmodule := by
    rintro _ ⟨u,hu,rfl⟩
    exact J.toSubmodule.sub_mem ((hstable J hj) ▸ Submodule.mem_map_of_mem hu) hu
  have hpos (J : Subrepresentation (ρ.comp H.subtype)) (hj : IsIrreducible J.toRepresentation) :
      0 < finrank (ZMod 2) (J.toSubmodule.map δ) :=
    Nat.pos_of_ne_zero (fun hz => component_subrepresentation_moved h cover hS hn hL hm
      ⟨a,ha⟩ hr hv J ((Subrepresentation.irreducible_iff_isAtom J).mp hj).ne_bot
      (Submodule.finrank_eq_zero.mp hz))
  have hd : Disjoint (R.toSubmodule.map δ) (Q.toSubmodule.map δ) :=
    (show Disjoint R.toSubmodule Q.toSubmodule by rw [hQspace]; exact hc.disjoint).mono
      (hle R hR) (hle Q hQ)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (R.toSubmodule.map δ) (Q.toSubmodule.map δ)
  rw [hd.eq_bot,finrank_bot,add_zero,← Submodule.map_sup] at hsum
  have htop : R.toSubmodule ⊔ Q.toSubmodule = ⊤ := by rw [hQspace]; exact hc.sup_eq_top
  rw [htop,Submodule.map_top] at hsum
  have he := even_constituent_displacement B h.alternating I hnd δ (hle R hR)
    (fun u => by change B u (ρ a u-u)=0; rw [map_sub,htype,h.alternating,sub_self])
  obtain ⟨k,hk⟩ := he
  have hp := hpos R hR
  have hq := hpos Q hQ
  change finrank (ZMod 2) δ.range ≤ 2 at hr
  change finrank (ZMod 2) (R.toSubmodule.map δ) = k+k at hk
  omega

/-- The actual type-a₂ and moved-plane nontransitivity premises remove both
the solvable remainder and every exchanged natural remainder. -/
theorem corrected_conclusion_or_whole_of_type_a2
    (h : Section10.Hypothesis ρ B v W X X₀)
    (cover : Nonempty (Section09.SQTKCover KnownSimple.IsKnownSimple G))
    (hS : NormalSylow ρ v X)
    (a : G) (ha : a ∈ X) (ha2 : a ^ 2 = 1)
    (hr : finrank (ZMod 2) (RankTwo.movedSpace ρ a) = 2)
    (hv : v ∈ RankTwo.movedSpace ρ a) (htype : ∀ u, B u (ρ a u) = 0)
    (hnt : ¬ RankTwo.StabilizerTransitive ρ (RankTwo.movedSpace ρ a)) :
    FullLinearFour.ConclusionWithFullLinearFour ρ B v W X X₀ ∨
      (IsIrreducible ρ ∧ 6 ≤ finrank (ZMod 2) V ∧ ¬ Group.IsSolvable G ∧
        ∃ L : Subgroup G, IsComponent G L ∧ ⁅L,X⁆ ≠ ⊥ ∧
          Section10.ComponentOrthogonalData ρ B L ∧
          Section09.ComponentHypothesis KnownSimple.IsKnownSimple ρ X L (componentOrbit L ⊤)
            (finrank (ZMod 2) (Additive X))) := by
  rcases corrected_conclusion_or_remaining h cover ⟨a,ha,hr.le,hv⟩ hS with
    hc | ⟨hi,hd,hs | ⟨hn,L,hL,hm,horth,hwhole | hex⟩⟩
  · exact Or.inl hc
  · have hfour := h.solvable_degree_le_four_of_rank_two_nontransitive cover hs.1 a ha ha2 hr hnt
    omega
  · exact Or.inr ⟨hi,hd,hn,L,hL,hm,horth,hwhole⟩
  · obtain ⟨I,hI,_,hgeo,_,_,_,hnd,_⟩ := hex
    exact (not_exchanged_nondegenerate_of_type_a2 h cover hS hn a ha hr.le hv htype
      hL hm hI hgeo hnd).elim

end CFSG.Quasithin.ChapterG.Section11.ExchangedRecognition
