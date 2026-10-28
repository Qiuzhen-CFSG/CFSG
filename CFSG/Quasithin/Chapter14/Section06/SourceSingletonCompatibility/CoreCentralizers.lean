module
public import CFSG.Quasithin.Chapter14.Section06.SourceFactorMovement
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.OrthogonalSource.MovedQuotient

/-!
# Core centralizers of the original solvable moved span

The odd residual lies in the generalized-Fitting preimage. Original 14.6.1(5)
therefore makes it centralize the omega-center of the two-core. A vector in
[U,J] centralizing that core has residual-fixed image in the residual moved
space of U/Z. Coprime fixed/moved separation makes its image zero, giving
C_[U,J](O₂(J)) = Z. Original 14.6.2 supplies the reverse inclusion.

Consequently the two-core exchanges the two lifts of every nonzero moved
quotient vector. Every quotient point stabilizer lifts onto the centralizer
of the same actual point. The application to the original elementary-nine
critical endpoint is in `NinePointControl`.

Source: Aschbacher--Smith 14.6.1(5), 14.6.2 and 14.6.12,
printed pp.1020--1021 and 1031 of refs/quasithin.pdf.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender Stellmacher
open scoped IsMulCommutative commutatorElement
namespace CFSG.Quasithin.Chapter14.Section06
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open OddNormalizer OddCriticalPair.OrthogonalSource
variable {G : Type*} [Group G] [Finite G]
variable (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
include hG hempty hM hu hmany hcard e hab

/-- In the original minimal solvable outside group, the two-core centralizer
in the entire moved span is exactly the original Sylow central line. -/
theorem source_solvable_moved_core_centralizer
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T)) :
    ⁅conjugateSpanBy (localModule T M) J,J⁆ ⊓ centralizer (J.pCoreIn 2 : Set G) =
      centralInvolutions T := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  let P := pResidual 2 (J ⧸ pCore 2 J)
  obtain ⟨p,hp,hE,_,hne,_⟩ := source_solvable_minimal_elementary_residual
    hG T hempty hM hu hmany hcard e hab J hJ hs
  let : Fact p.Prime := ⟨by rcases hp with rfl | rfl <;> decide⟩
  let : IsElementaryAbelian p P := hE
  have hodd : Odd (Nat.card P) := by
    obtain ⟨n,hn⟩ := (IsElementaryAbelian.isPGroup p P).exists_card_eq
    rw [hn]
    exact (show Odd p by rcases hp with rfl | rfl <;> decide).pow
  have hPf : P ≤ generalizedFitting (J ⧸ pCore 2 J) :=
    (show P ≤ fittingSubgroup (J ⧸ pCore 2 J) from
      le_sSup ⟨inferInstance,inferInstance⟩).trans le_sup_left
  have hRf : residual J ≤ ChapterA.Section04.twoGeneralizedFittingPreimage J := by
    apply map_mono
    apply map_le_iff_le_comap.mp
    rw [map_pResidual_quotient]
    exact hPf
  have hRC := hRf.trans (source_generalizedFittingPreimage_centralizes_omegaCore
    hG T hempty hJ.1 h.H_centralizes)
  have hZ : D.V₁ ≤ ⁅D.UH,J⁆ := by
    have hz := source_point_le_lifted_odd_factor
      hG T hempty hM hu hmany hcard e hab J hJ hs P le_rfl hne
    exact hz.trans (commutator_mono le_rfl (map_subtype_le _))
  apply le_antisymm ?_ (le_inf hZ (le_centralizer_iff.mp
    ((pCoreIn_le 2 J).trans h.H_centralizes)))
  intro u hmem
  have huU : u ∈ D.UH := moved_le a hmem.1
  have huOmega : u ∈ omegaOneCenterAmbient D.QH :=
    (mem_omegaOneCenterAmbient_iff _ _).mpr
      ⟨h.UH_le_QH huU,elemPow_eq_one_of_isElementaryAbelian u huU,hmem.2⟩
  have hW := source_rankTwo_whole_moved_eq_residual
    hG T hempty hM hu hmany hcard e hab J hJ.1 a
  apply supportPreimage_fixedFree a hodd (movedSpace a) hW.le u
  · apply (mem_supportPreimage a _ ⟨u,huU⟩).mpr
    exact (movedMap a ⟨u,hmem.1⟩).toAdd.property
  · intro k hk
    rw [commutatorElement_eq_one_iff_mul_comm.mpr (hRC hk u huOmega)]
    exact one_mem _

omit hG T hempty hM hu hmany hcard e hab in
private theorem core_conjugate_of_same_fiber
    {D : ChapterF.Section09.Setup G} (h : D.Hypothesis)
    [IsElementaryAbelian 2 D.UH]
    (u v : D.UH) (hmove : ¬ D.QH ≤ centralizer ({(u : G)} : Set G))
    (he : QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u =
      QuotientGroup.mk' (D.V₁.subgroupOf D.UH) v) :
    ∃ q ∈ D.QH, (MulAut.conj q) (u : G) = (v : G) := by
  obtain ⟨q,hq,hqu⟩ := SetLike.not_le_iff_exists.mp hmove
  have hz : ⁅(u : G),q⁆ ∈ D.V₁ :=
    h.commutator_UH_QH_le_point (commutator_mem_commutator u.property hq)
  have hzn : ⁅(u : G),q⁆ ≠ 1 := by
    intro hh
    exact hqu (mem_centralizer_singleton_iff.mpr
      (commutatorElement_eq_one_iff_mul_comm.mp hh).symm)
  have hw : (u : G) * (v : G)⁻¹ ∈ D.V₁ := by
    change u * v⁻¹ ∈ D.V₁.subgroupOf D.UH
    apply (QuotientGroup.eq_one_iff (u * v⁻¹)).mp
    change QuotientGroup.mk' (D.V₁.subgroupOf D.UH) (u * v⁻¹) = 1
    rw [map_mul,map_inv,he,mul_inv_cancel]
  by_cases hw1 : (u : G) * (v : G)⁻¹ = 1
  · exact ⟨1,one_mem _,by simpa using mul_inv_eq_one.mp hw1⟩
  · obtain ⟨z,hz1,heq⟩ := (Nat.card_eq_two_iff' (1 : D.V₁)).mp h.point_card
    have hh : (u : G) * (v : G)⁻¹ = ⁅(u : G),q⁆ := by
      exact congrArg Subtype.val ((heq ⟨_,hw⟩ (fun hh => hw1 (congrArg Subtype.val hh))).trans
        (heq ⟨_,hz⟩ (fun hh => hzn (congrArg Subtype.val hh))).symm)
    refine ⟨q,hq,?_⟩
    have hc : (u : G) * ((MulAut.conj q) (u : G))⁻¹ = ⁅(u : G),q⁆ := by
      simp only [MulAut.conj_apply,commutatorElement_def,mul_inv_rev,inv_inv]
      group
    exact (inv_injective (mul_left_cancel (hh.trans hc.symm))).symm

/-- Every quotient stabilizer of a noncentral moved point lifts to its actual
centralizer, with the original quotient map and the same point retained. -/
theorem source_solvable_moved_point_centralizer_lifts
    (J : Subgroup G) (hJ : J ∈ Chapter3.HStar (T : Subgroup G) M)
    (hs : Group.IsSolvable J)
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)]
    (a : LocalQuotientAction J (conjugateSpanBy (localModule T M) J) (centralInvolutions T))
    (u : conjugateSpanBy (localModule T M) J)
    (huW : (u : G) ∈ ⁅conjugateSpanBy (localModule T M) J,J⁆)
    (huZ : (u : G) ∉ centralInvolutions T)
    (t : J ⧸ pCore 2 J)
    (ht : a.representation t (Additive.ofMul
      (QuotientGroup.mk' ((centralInvolutions T).subgroupOf _) u)) =
      Additive.ofMul (QuotientGroup.mk' ((centralInvolutions T).subgroupOf _) u)) :
    ∃ k : J, QuotientGroup.mk' (pCore 2 J) k = t ∧
      (k : G) ∈ centralizer ({(u : G)} : Set G) := by
  let D : ChapterF.Section09.Setup G :=
    ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,J⟩
  let : IsElementaryAbelian 2 D.UH :=
    ‹IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) J)›
  let h : D.Hypothesis := source_rankTwo_f9_hypothesis hG T hempty hM hu hmany hcard e hab J hJ.1
  have hmove : ¬ D.QH ≤ centralizer ({(u : G)} : Set G) := by
    intro hc
    apply huZ
    rw [←source_solvable_moved_core_centralizer hG T hempty hM hu hmany hcard e hab J hJ hs a]
    exact ⟨huW,fun q hq => mem_centralizer_singleton_iff.mp (hc hq)⟩
  obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 J) t
  let v : D.UH := ⟨(MulAut.conj (x : G)) (u : G),(a.normalizes x.property u).mp u.property⟩
  have he : QuotientGroup.mk' (D.V₁.subgroupOf D.UH) u =
      QuotientGroup.mk' (D.V₁.subgroupOf D.UH) v := by
    exact congrArg Additive.toMul (ht.symm.trans (a.conjugation x u))
  obtain ⟨q,hq,hqu⟩ := core_conjugate_of_same_fiber h u v hmove he
  let qJ : J := ⟨q,pCoreIn_le 2 J hq⟩
  have hqker : QuotientGroup.mk' (pCore 2 J) qJ = 1 := by
    apply (QuotientGroup.eq_one_iff _).mpr
    obtain ⟨y,hy,he⟩ := hq
    exact (show y = qJ from Subtype.ext he) ▸ hy
  refine ⟨qJ⁻¹*x,by rw [map_mul,map_inv,hqker,inv_one,one_mul],?_⟩
  apply mem_centralizer_singleton_iff.mpr
  have hh : q * (u : G) * q⁻¹ = (x : G) * (u : G) * (x : G)⁻¹ := hqu
  change (q⁻¹*(x : G))*(u : G) = (u : G)*(q⁻¹*(x : G))
  calc
    (q⁻¹*(x : G))*(u : G) = q⁻¹*((x : G)*(u : G)*(x : G)⁻¹)*(x : G) := by group
    _ = q⁻¹*(q*(u : G)*q⁻¹)*(x : G) := by rw [hh]
    _ = (u : G)*(q⁻¹*(x : G)) := by group

end CFSG.Quasithin.Chapter14.Section06
