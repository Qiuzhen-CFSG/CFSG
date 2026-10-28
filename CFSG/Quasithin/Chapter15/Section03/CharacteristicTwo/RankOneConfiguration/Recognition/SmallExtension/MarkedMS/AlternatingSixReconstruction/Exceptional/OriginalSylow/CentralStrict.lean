module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.UncontrolledKernels
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.SmallSlices
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.OriginalSylow.DistinctShifts
import all CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.CubicOmegaGeneration

/-!
# Distinct Borel movers at a strict Baumann slice

A subgroup of the two-ball radius whose quotient over the seed has order
dividing eight lies in the Baumann slice when the actual component residual
normalizes it. Indeed, its quotient automorphism group has order coprime
to five, whereas a nontrivial image of the perfect component contains the
A6 central quotient. This uses only residual normalization.

In the centrally generated branch, an uncontrolled small critical endpoint
constructs such a small residual-invariant fixed span. A strict forward
slice excludes this span. Endpoint control then makes the whole neighboring
seed span invariant under the critical actor and opposite mover, which
generate the residual when the movers are distinct. The neighboring seed
would lie in the Baumann slice, again contradicting strictness.

The existing paired selectors now give an actual compatible backward path
with every overlap retained. Combining with the noncentral-generation
branch gives the distinct-mover small shift without a central-generation
premise. Equal movers and terminal distance exclusions remain separate
obligations. OriginalSylowExceptional applies this family to c.L,d.S.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (5.7), printed p.919; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement Pointwise
open Theory.SpecificGroups.SymmetricSix Theory.SpecificGroups.SymmetricSix.BinaryFlags CoreCrossing
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticSetup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Exceptional.OriginalSylow
open Exhaustion Exhaustion.LargeDistance Exhaustion.LargeDistance.CubicFull
local notation "borel" => Theory.SpecificGroups.SymmetricSix.borel

universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
  (hk : layerKernel L R = extensionKernel h)
local notation "M" => (L ⊔ R : Subgroup G)
local notation "Rg" => edge L R
local notation "W₀" => (⁅centralOmega L R,L.subgroupOf M⁆ : Subgroup M)
local notation "π" => CubicAction.projection h e hz hk
local instance : IsElementaryAbelian 2 W₀ := IsElementaryAbelian.of_le (commutator_le_left _ _)
open Representation.NormalElementaryQuotient

include h e in
private theorem component_hom_eq_one_of_five_coprime
    {H : Type*} [Group H] [Finite H] (f : L →* H)
    (hf : Nat.Coprime 5 (Nat.card H)) : f = 1 := by
  let := h.component_perfect
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsQuasisimple (L ⧸ pCore 2 L) := h.core_quasisimple_of_centralCore
    (e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp)))
  let q := QuotientGroup.mk' (pCore 2 L)
  let N := f.ker
  let : (N.map q).Normal := Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  apply MonoidHom.ker_eq_top_iff.mp
  rcases IsQuasisimple.normal_le_center_or_eq_top (N.map q) with hn | hn
  · have hN : N ≤ centralPreimage (pCore 2 L) := map_le_iff_le_comap.mp hn
    have hdiv := index_dvd_of_le hN
    have he := e.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (by simp))
    have hc : (centralPreimage (pCore 2 L)).index = 360 := by
      rw [index_eq_card,Nat.card_congr he.toEquiv]
      exact Theory.SpecificGroups.SymmetricSix.a6_order
    rw [hc] at hdiv
    have hncard : 5 ∣ Nat.card H := (show 5 ∣ 360 by decide).trans
      (hdiv.trans (by
        change f.ker.index ∣ Nat.card H
        rw [index_ker]
        exact f.range.card_subgroup_dvd_card))
    exact (Nat.prime_five.coprime_iff_not_dvd.mp hf hncard).elim
  · have hsup : N ⊔ pCore 2 L = ⊤ := by
      have he := congrArg (Subgroup.comap q) hn
      simpa only [q,comap_map_eq,QuotientGroup.ker_mk',comap_top] using he
    exact top_le_iff.mp (perfect_le_of_le_sup_two ⊤ N (pCore 2 L) pCore_isPGroup hsup.ge)

include h e hz hk in
/-- Residual invariance suffices for a radius section of order dividing eight
to lie in the Baumann slice. The component's genuine A₆ central quotient
kills its action on this section; whole-stabilizer normality is unnecessary. -/
theorem residual_small_radius_le_slice
    (D : Subgroup (FreeAmalgam Rg))
    (hDV : D ≤ V Rg (alpha Rg))
    (hDN : Ltilde Rg (alpha Rg) ≤ normalizer (D : Set (FreeAmalgam Rg)))
    (hsmall : (Z Rg (alpha Rg)).relIndex D ∣ 8) :
    D ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) := by
  have hb := distance_gt_two h e hz hk
  let D₀ := D.comap (embedM Rg)
  let Z₀ := (Z Rg (alpha Rg)).comap (embedM Rg)
  let K := L.subgroupOf M
  have hDm : D₀.map (embedM Rg) = D := map_comap_eq_self
    ((hDV.trans ((sourceGeometry h).V_local _ rfl hb)).trans_eq (stabilizer_m_base Rg))
  have hZm : Z₀.map (embedM Rg) = Z Rg (alpha Rg) := map_comap_eq_self
    ((Z_le_stabilizer Rg _).trans_eq (stabilizer_m_base Rg))
  have hKm : K.map (embedM Rg) = Ltilde Rg (alpha Rg) := by
    rw [Ltilde_alpha,h.relative_residual]
  have hg (m : M) : embedM Rg m ∈ stabilizer Rg (alpha Rg) := by
    change embedM Rg m ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨m,rfl⟩
  let : Z₀.Normal := ⟨by
    intro z hz m
    change embedM Rg (m*z*m⁻¹) ∈ Z Rg (alpha Rg)
    rw [map_mul,map_mul,map_inv]
    exact (mem_normalizer_iff.mp ((Z_normalized Rg _) (hg m)) (embedM Rg z)).mp hz⟩
  have hKN : K ≤ normalizer (D₀ : Set M) := by
    intro k hkK
    apply mem_normalizer_iff.mpr
    intro d
    change embedM Rg d ∈ D ↔ embedM Rg (k*d*k⁻¹) ∈ D
    rw [map_mul,map_mul,map_inv]
    exact mem_normalizer_iff.mp (hDN (hKm ▸ mem_map_of_mem _ hkK)) _
  let q := QuotientGroup.mk' Z₀
  let V := D₀.map q
  have hKV : K.map q ≤ normalizer (V : Set (M ⧸ Z₀)) :=
    (map_mono hKN).trans (le_normalizer_map q)
  let f : K →* MulAut V := V.normalizerMonoidHom.comp
    ((q.comp K.subtype).codRestrict (normalizer (V : Set (M ⧸ Z₀)))
      (fun k => hKV (mem_map_of_mem q k.property)))
  have hc : Nat.card V ∣ 8 := by
    rw [←relIndex_ker D₀ q]
    rw [show q.ker = Z₀ from QuotientGroup.ker_mk' Z₀]
    rw [←relIndex_map_map_of_injective _ _ (embedM_injective Rg),hDm,hZm]
    exact hsmall
  let d := subgroupOfEquivOfLe (show L ≤ L ⊔ R from le_sup_left)
  have hf := component_hom_eq_one_of_five_coprime h e (f.comp d.symm.toMonoidHom)
    (five_coprime_card_mulAut_of_card_dvd_eight hc)
  have hf' : f = 1 := by
    apply MonoidHom.ext
    intro k
    obtain ⟨l,rfl⟩ := d.symm.surjective k
    exact DFunLike.congr_fun hf l
  have hcent : K.map q ≤ centralizer (V : Set (M ⧸ Z₀)) := by
    rintro _ ⟨k,hkK,rfl⟩ v hv
    have he := congrArg (fun a : MulAut V => (a ⟨v,hv⟩ : M ⧸ Z₀))
      (DFunLike.congr_fun hf' (⟨k,hkK⟩ : K))
    change q k * v * (q k)⁻¹ = v at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hcomm : ⁅D₀,K⁆ ≤ Z₀ := by
    rw [←QuotientGroup.ker_mk' Z₀,←Subgroup.map_eq_bot_iff,map_commutator]
    exact commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hcent)
  have hm := map_mono (f := embedM Rg) hcomm
  rw [map_commutator,hDm,hKm,hZm,commutator_comm] at hm
  intro v hv
  exact (mem_B_iff Rg (alpha Rg) _ ((sourceGeometry h).V_local _ rfl hb) v).mpr
    ⟨hDV hv,fun l hl => hm (commutator_mem_commutator hl hv)⟩
include h e hz hk in
/-- In the central-generation branch with distinct movers, a strict forward
slice forces endpoint commutator control on every trapped small critical
path. This is the original full-omega comparison, with no predecessor-slice
bound. -/
theorem borel_central_distinct_strict_endpoint_control
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    (hne : edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin c t)
    (hbad : Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)))
    (hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    ⁅Z Rg c,X Rg z⁆ ≤ Z Rg (alpha Rg) ⊔ ⁅X Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ := by
  by_contra hescape
  obtain ⟨hindex,hYV,hYN,_⟩ := borel_central_uncontrolled_fixed_span h e hz hk u hR
    p hp hat hct hgen hsplit hne hbad hescape
  let K := X Rg z ⊓ Q Rg (alpha Rg)
  let D := Z Rg c ⊓ centralizer (K : Set (FreeAmalgam Rg))
  let Y := D ⊔ Z Rg (alpha Rg)
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hZaX : Z Rg (alpha Rg) ≤ X Rg (alpha Rg) :=
    (sourceGeometry h).omega_bound _ rfl (by
      rw [(sourceGeometry h).distance_constant _ rfl]
      exact sourceDistance_pos h)
  have hZaT : Z Rg (alpha Rg) ≤ Q Rg t :=
    (hZaX.trans (omegaCenter_le _)).trans (Q_le_adjacent_h Rg ht hat)
  have hTNc : Q Rg t ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg c)
  let := finite_Z Rg (alpha Rg)
  have hbig : (Z Rg (alpha Rg)).relIndex (Z Rg c ⊔ Z Rg (alpha Rg)) ∣ 8 := by
    rw [relIndex_sup_of_normalizes (Z Rg c) (Z Rg (alpha Rg)) (hZaT.trans hTNc)]
    have hd := relIndex_dvd_of_le_left (Z Rg c) (adjacent_Z_le Rg rfl hat)
    rw [borel_full_seed_edge_index h e hz hk u hR hc hct] at hd
    exact hd
  have hsmall : (Z Rg (alpha Rg)).relIndex Y ∣ 8 := by
    have hm := relIndex_mul_relIndex (Z Rg (alpha Rg)) Y
      (Z Rg c ⊔ Z Rg (alpha Rg)) le_sup_right (sup_le_sup_right inf_le_left _)
    exact (Dvd.intro _ hm).trans hbig
  have hDB : D ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (residual_small_radius_le_slice h e hz hk Y hYV hYN hsmall)
  let := finite_Z Rg c
  let : Finite (U Rg c) := Finite.of_injective _
    (Subgroup.inclusion_injective (DistanceEight.U_le_Z Rg c))
  have hbound := (relIndex_le_of_le_left hDB (index_ne_zero_of_finite :
    D.relIndex (U Rg c) ≠ 0)).trans hindex
  omega

include h e hz hk in
/-- At a distinct mover, a strict slice cannot remain trapped on the selected
critical path. The opposite mover and the critical endpoint generate the
residual, which forces the full neighboring seed into the Baumann slice. -/
theorem borel_central_distinct_strict_escape
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z c t : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hat : Adjacent Rg (alpha Rg) t) (hct : Adjacent Rg c t)
    (hgen : Q Rg t ⊔ Z Rg z = stabilizer Rg (alpha Rg))
    (hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    (hne : edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin c t)
    (hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c)) :
    ¬ Z Rg c ≤ Q Rg (p.walk.getVert (p.walk.length-2)) := by
  intro hbad
  have hb := distance_gt_two h e hz hk
  have ht : color Rg t = true := by
    have hh := adjacent_color_ne Rg hat
    change false ≠ color Rg t at hh
    cases he : color Rg t <;> simp_all
  have hc : color Rg c = false := by
    have hh := adjacent_color_ne Rg hct
    rw [ht] at hh
    cases he : color Rg c <;> simp_all
  have hTNa : Q Rg t ≤ normalizer (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg (alpha Rg) from
      fun _ hx => hx.2 _ (adjacent_symm Rg hat)).trans (Z_normalized Rg _)
  have hTNc : Q Rg t ≤ normalizer (Z Rg c : Set (FreeAmalgam Rg)) :=
    (show Q Rg t ≤ stabilizer Rg c from
      fun _ hx => hx.2 _ (adjacent_symm Rg hct)).trans (Z_normalized Rg _)
  have hXa : Z Rg (alpha Rg) ≤ X Rg (alpha Rg) :=
    (sourceGeometry h).omega_bound _ rfl (by
      rw [(sourceGeometry h).distance_constant _ rfl]
      exact sourceDistance_pos h)
  have hXz : X Rg z = Z Rg z := omega_eq_seed_of_central_generation h z p.end_color
    (omega_generation_transport (show color Rg (alpha Rg) = false from rfl) p.end_color hsplit)
  have hcontrol := borel_central_distinct_strict_endpoint_control h e hz hk u hR
    p hp hat hct hgen hsplit hne hbad hstrict
  rw [hXz] at hcontrol
  let Y := Z Rg c ⊔ Z Rg (alpha Rg)
  have hKc : ⁅Z Rg z ⊓ Q Rg (alpha Rg),Z Rg c⁆ ≤ Z Rg c :=
    le_normalizer_iff_commutator_le_right.mp
      ((inf_le_right.trans (Q_le_adjacent_h Rg ht hat)).trans hTNc)
  have hZN : Z Rg z ≤ normalizer (Y : Set (FreeAmalgam Rg)) := by
    have hZlocal := critical_Z_le_stabilizer Rg (sourceGeometry h) (alpha Rg) rfl
      (sourceDistance_pos h) p.critical
    have hZV : Z Rg c ≤ V Rg (alpha Rg) := (Z_le_localZSpan Rg _ _).trans
      (localZSpan_le_V Rg
        (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct))
    have hZcG := hZV.trans ((sourceGeometry h).V_local _ rfl hb)
    have hXaN : Z Rg z ≤ normalizer (Z Rg (alpha Rg) : Set (FreeAmalgam Rg)) :=
      hZlocal.trans (Z_normalized Rg _)
    have hcomm : ⁅Z Rg c,Z Rg z⁆ ≤ Y :=
      hcontrol.trans (sup_le le_sup_right (hKc.trans le_sup_left))
    apply le_normalizer_iff.mpr
    intro x hx v hv
    have hm : Y.map (MulAut.conj x).toMonoidHom ≤ Y := by
      rw [Subgroup.map_sup]
      refine sup_le ?_ ((mem_normalizer_iff_map_conj_eq.mp (hXaN hx)).le.trans le_sup_right)
      rintro _ ⟨y,hy,rfl⟩
      have hh := Y.mul_mem
        (hcomm ((commutator_comm (Z Rg c) (Z Rg z)) ▸ commutator_mem_commutator hx hy))
        (mem_sup_left hy)
      simpa [MulAut.conj_apply,commutatorElement_def,mul_assoc] using hh
    exact hm (mem_map_of_mem (MulAut.conj x).toMonoidHom hv)
  have hcore : ¬ Q Rg (alpha Rg) ≤ edgeOffenderJoin c t := by
    intro hcore
    exact borel_opposite_containing_core_nonsplit h e hz hk u hR rfl hc
      hat hct hne hcore hsplit
  have hJN : edgeOffenderJoin c t ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    ((remaining_edge_thompson h e hz hk u (Or.inr hR) hc hct).2.2.1.trans
      (le_inf hTNc hTNa)).trans (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hYN : Ltilde Rg (alpha Rg) ≤ normalizer (Y : Set (FreeAmalgam Rg)) :=
    (borel_opposite_generation_of_core_not_le h e hz hk u hR rfl hc
      hat hct (Z Rg z) hgen hcore).2.trans (sup_le hJN hZN)
  have hYV : Y ≤ V Rg (alpha Rg) :=
    sup_le ((Z_le_localZSpan Rg _ _).trans (localZSpan_le_V Rg
      (CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.neighbor_distance_le_two hat hct)))
      (Z_le_VBall Rg _ 2)
  let := finite_Z Rg (alpha Rg)
  have hsmall : (Z Rg (alpha Rg)).relIndex Y ∣ 8 := by
    change (Z Rg (alpha Rg)).relIndex (Z Rg c ⊔ Z Rg (alpha Rg)) ∣ 8
    rw [relIndex_sup_of_normalizes (Z Rg c) (Z Rg (alpha Rg))
      (((hXa.trans (omegaCenter_le _)).trans (Q_le_adjacent_h Rg ht hat)).trans hTNc)]
    have hd := relIndex_dvd_of_le_left (Z Rg c) (adjacent_Z_le Rg rfl hat)
    rw [borel_full_seed_edge_index h e hz hk u hR hc hct] at hd
    exact hd
  have hZB : Z Rg c ≤ B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    le_sup_left.trans (residual_small_radius_le_slice h e hz hk Y hYV hYN hsmall)
  have hi := relIndex_eq_one.mpr ((DistanceEight.U_le_Z Rg c).trans hZB)
  omega

include h e hz hk in
/-- In the centrally generated case, distinct Borel movers supply compatible
backward paths at a strict slice, without any starting-core containment
assumption. The source selectors and all path overlaps are retained. -/
theorem borel_central_distinct_small_shift
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hne : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ≠
      edgeOffenderJoin delta (p.walk.getVert 1))
    (hsplit : X Rg (alpha Rg) = U Rg (alpha Rg) ⊔
      (X Rg (alpha Rg) ⊓ centralizer (stabilizer Rg (alpha Rg) : Set (FreeAmalgam Rg))))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let c := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
          ((∃ b : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
           (∃ b : CriticalPath Rg (sourceGeometry h) c (q.walk.getVert (q.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  obtain ⟨t,hat,r,hr,hgen,hpair,_,_,hgenedge,_,_,_,hnorm,hinside,_,g,hg,hgt,_⟩ :=
    borel_small_critical_seed_selectors_with_opposite h e hz hk u hR p hp
  let x := (embedM Rg r)⁻¹
  let c := act Rg g delta
  have hxG : x ∈ stabilizer Rg (alpha Rg) := by
    change x ∈ stabilizer Rg (mVertex Rg 1)
    rw [stabilizer_m_base]
    exact ⟨r⁻¹,by rw [map_inv]⟩
  have hxa : act Rg x (alpha Rg) = alpha Rg := hxG
  have hpact : ∃ q : CriticalPath Rg (sourceGeometry h)
      (act Rg x (alpha Rg)) (act Rg x z),
      ∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i) :=
    ⟨p.act x,fun i => by simp only [CriticalPath.act,actWalk_getVert]⟩
  rw [hxa] at hpact
  obtain ⟨q,hqverts⟩ := hpact
  have hqs : (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 := by
    rw [←hxa,Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj x⁻¹).injective]
    exact hp
  have hct : Adjacent Rg c t := by
    rw [←hgt]
    exact (adjacent_act_iff Rg g _ _).mpr hd
  have hc : color Rg c = false := by
    have h₁ := adjacent_color_ne Rg hat
    have h₂ := adjacent_color_ne Rg hct
    change false ≠ color Rg t at h₁
    cases he : color Rg c <;> cases he' : color Rg t <;> simp_all
  have hb := distance_gt_two h e hz hk
  have hB : (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).map
      (MulAut.conj g⁻¹).toMonoidHom = B Rg (alpha Rg) ((sourceGeometry h).Z_normal _) :=
    mem_normalizer_iff_map_conj_eq.mp (Escape.Propagation.Rigidity.B_normalized
      hb (alpha Rg) rfl ((stabilizer Rg (alpha Rg)).inv_mem hg))
  have hstrict : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) := by
    change 2 < (B Rg (alpha Rg) _).relIndex (U Rg (act Rg g delta))
    rw [U_act,←hB,relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective]
    exact hs
  have hfirst : Adjacent Rg (alpha Rg) (p.walk.getVert 1) := by
    apply (cosetGraph_adj Rg _ _).mp
    simpa only [SimpleGraph.Walk.getVert_zero] using
      p.walk.adj_getVert_succ (i := 0) (p.length_eq_b ▸ sourceDistance_pos h)
  have hdcol : color Rg delta = false := by
    simpa only [c,action_preserves_color] using hc
  have hga : act Rg g (alpha Rg) = alpha Rg := hg
  have hJa := remaining_edge_join_act h e hz hk u (Or.inr hR) rfl hfirst g
  have hJd := remaining_edge_join_act h e hz hk u (Or.inr hR) hdcol hd g
  simp only [hga,hgt] at hJa hJd
  have hnec : edgeOffenderJoin (alpha Rg) t ≠ edgeOffenderJoin c t := by
    intro he
    apply hne
    apply map_injective (f := (MulAut.conj g⁻¹).toMonoidHom) (MulAut.conj g⁻¹).injective
    exact hJa.symm.trans (he.trans hJd)
  have extend (w : Vertex Rg) (s : CriticalPath Rg (sourceGeometry h) (alpha Rg) w)
      (hn : ¬ Z Rg c ≤ Q Rg (s.walk.getVert (s.walk.length-2))) :
      ∃ b : CriticalPath Rg (sourceGeometry h) c (s.walk.getVert (s.walk.length-2)),
        b.walk.getVert 1 = t ∧ ∀ i ≤ s.walk.length-2, b.walk.getVert (i+2) = s.walk.getVert i := by
    let v : (cosetGraph Rg).Walk c (alpha Rg) :=
      .cons ((cosetGraph_adj Rg _ _).mpr hct)
        (.cons ((cosetGraph_adj Rg _ _).mpr (adjacent_symm Rg hat)) .nil)
    have hv : v.length = 2 := rfl
    let b := s.prepend_two (Nat.le_of_lt hb) hc v hv hn
    refine ⟨b,?_,fun i hi => s.prepend_two_overlap _ _ _ _ _ hi⟩
    simp only [b,CriticalPath.prepend_two_walk,SimpleGraph.Walk.getVert_append,
      hv,show 1<2 from by decide,ite_true,v,SimpleGraph.Walk.getVert_cons_succ,
      SimpleGraph.Walk.getVert_zero]
  exact ⟨t,hat,r,hr,q,hqverts,hqs,hgen,hpair,hnorm,hinside,g,hg,hgt,
    hstrict,Or.inl (extend _ p (borel_central_distinct_strict_escape h e hz hk u hR
      p hp hat hct hgenedge hsplit hnec hstrict))⟩

include h e hz hk in
/-- Distinct Borel movers supply compatible backward critical paths at a
strict slice, including central generation and both moving covers. -/
theorem borel_distinct_small_shift
    (u : S) (hR : (Rg).map π = borel.map (MulAut.conj u).toMonoidHom)
    {z delta : Vertex Rg}
    (p : CriticalPath Rg (sourceGeometry h) (alpha Rg) z)
    (hp : (Q Rg z).relIndex (Z Rg (alpha Rg)) < 4)
    (hd : Adjacent Rg delta (p.walk.getVert 1))
    (hne : edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ≠
      edgeOffenderJoin delta (p.walk.getVert 1))
    (hs : 2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg delta)) :
    ∃ t, Adjacent Rg (alpha Rg) t ∧ ∃ r ∈ L.subgroupOf M,
      let x := (embedM Rg r)⁻¹
      ∃ q : CriticalPath Rg (sourceGeometry h) (alpha Rg) (act Rg x z),
        (∀ i, q.walk.getVert i = act Rg x (p.walk.getVert i)) ∧
        (Q Rg (act Rg x z)).relIndex (Z Rg (alpha Rg)) < 4 ∧
        (edgeOffenderJoin (alpha Rg) t ⊔ Z Rg z) ⊔ Z Rg (act Rg x z) = stabilizer Rg (alpha Rg) ∧
        edgeOffenderJoin (alpha Rg) t ⊔ edgeOffenderJoin (alpha Rg) (act Rg x t) = stabilizer Rg (alpha Rg) ∧
        x ∈ normalizer (edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) : Set (FreeAmalgam Rg)) ∧
        Z Rg z ⊔ Z Rg (act Rg x z) ≤ edgeOffenderJoin (alpha Rg) (p.walk.getVert 1) ∧
        ∃ g ∈ stabilizer Rg (alpha Rg), act Rg g (p.walk.getVert 1) = t ∧
          let c := act Rg g delta
          2 < (B Rg (alpha Rg) ((sourceGeometry h).Z_normal _)).relIndex (U Rg c) ∧
          ((∃ b : CriticalPath Rg (sourceGeometry h) c (p.walk.getVert (p.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ p.walk.length-2, b.walk.getVert (i+2) = p.walk.getVert i) ∨
           (∃ b : CriticalPath Rg (sourceGeometry h) c (q.walk.getVert (q.walk.length-2)),
              b.walk.getVert 1 = t ∧
              ∀ i ≤ q.walk.length-2, b.walk.getVert (i+2) = q.walk.getVert i)) := by
  rcases borel_small_shift_or_central_generation h e hz hk u hR p hp hd hs with
    hcentral | hpaths
  · exact borel_central_distinct_small_shift h e hz hk u hR p hp hd hne (hcentral _ rfl).1 hs
  · exact hpaths

end AlternatingSixReconstruction.Exceptional.OriginalSylow
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
