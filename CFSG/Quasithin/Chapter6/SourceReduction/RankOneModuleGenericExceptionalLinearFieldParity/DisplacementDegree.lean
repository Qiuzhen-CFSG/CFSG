module
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.Estimates
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupNatural
public import Theory.Representation.BinaryOffender.CommutatorRank
public import Theory.Representation.BinaryOffender.InvolutionFixed
public import Theory.Representation.FixedFreeCentralAction
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.OddSetupCartanFree
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleGenericExceptionalLinearFieldParity.CriticalPairProper

/-!
# Reducing the parity argument to degree three

The natural-seed calculation makes the central Cartan of order 2ⁿ−1 act
without fixed vectors on U/Z₁. Its free orbits force every nonzero
invariant subspace to have dimension at least n. In particular this holds
for the displacement of every actor outside the local two-core.

The critical pair now gives n ≤ 4 without the H.4.7 multiplicity argument.
If the opposite kernel centralizes the endpoint span, either the existing
centralized case applies or its index bounds a nonzero displacement by
four. Otherwise a moved TI point embeds in the quotient of two-rank four.
For odd n > 1, only n = 3 remains. This reduces the representation input
needed by the actual Chapter12 parity assembly to the order-seven Cartan.
Global TI/F.8 construction and the degree-three displacement calculation
remain with qt-d-1222-linear-field-parity.

Source: Aschbacher–Smith 5.1.17, printed pp.640–642 (refs/quasithin.pdf).
-/

open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Representation Representation.BinaryOffender
public noncomputable section
namespace CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L H A B : Subgroup G} {n : ℕ}

/-- The seed's actual Cartan acts without fixed vectors in any coordinates
for the literal quotient. Abstract coordinates avoid dependent quotient casts. -/
theorem Seed.cartan_fixedFree (s : Seed T L H A n)
    (c : CartanPair T L H A B)
    {X : Type*} [AddCommGroup X] [Module (ZMod 2) X] [FiniteDimensional (ZMod 2) X]
    (ρ : Representation (ZMod 2)
      ((H ⊔ A : Subgroup G) ⧸ pCore 2 (H ⊔ A : Subgroup G)) X)
    (d : BinaryConjugationSection (H ⊔ A) (setup T L s.V H A).U
      (setup T L s.V H A).V₁
      (ρ.comp (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G)))))
    (a : A) (ha : a ≠ 1) (v : X)
    (hv : ρ (QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
      ⟨a,mem_sup_right a.property⟩) v = v) : v = 0 := by
  have hnat := s.natural
  have hgeom := s.f8
  rw [← s.module_eq] at hnat hgeom d
  exact fundamental_cartan_fixedFree s.fundamental c hnat hgeom s.cartan_central ρ d a ha v hv

set_option backward.isDefEq.respectTransparency false in
/-- Every actor outside the literal two-core moves at least n binary dimensions. -/
theorem Seed.degree_le_displacement (s : Seed T L H A n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : CartanPair T L H A B)
    {y : G} (hy : y ∈ H ⊔ A) (hyQ : y ∉ (H ⊔ A : Subgroup G).pCoreIn 2) :
    n ≤ displacement (setup T L s.V H A) y := by
  let E := setup T L s.V H A
  let := point_normal_in_span s.f8
  let := ChapterF.Section08.Setup.lemma_F_8_5_two s.f8
  let : IsElementaryAbelian 2 (E.U ⧸ E.V₁.subgroupOf E.U) :=
    IsElementaryAbelian.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  obtain ⟨ρ,d,hρ,_⟩ := exists_faithful_action s.f8
  let q := QuotientGroup.mk' (pCore 2 (H ⊔ A : Subgroup G))
  let f : A →* E.HStar := q.comp (inclusion (show A ≤ H ⊔ A from le_sup_right))
  have hf (a : A) (ha : a ≠ 1) (v) (hv : ρ (f a) v = v) : v = 0 :=
    s.cartan_fixedFree c ρ d a ha v hv
  have hcard : Nat.card A + 1 = 2^n := by
    rw [(c.left_cyclic_and_card hTL hpsl).2,Nat.sub_add_cancel Nat.one_le_two_pow]
  have hcomm (a : A) : Commute (f a) (q ⟨y,hy⟩) := by
    apply Commute.symm
    exact mem_center_iff.mp (s.cartan_central (mem_map_of_mem q a.property)) _
  have hne : ρ (q ⟨y,hy⟩) ≠ 1 := by
    intro he
    have hq : q ⟨y,hy⟩ = 1 := hρ (he.trans (map_one ρ).symm)
    exact hyQ (mem_map_of_mem (H ⊔ A : Subgroup G).subtype
      ((QuotientGroup.eq_one_iff _).mp hq))
  have hb := FixedFreeCentralAction.degree_le_displacement ρ f hf n hcard _ hcomm hne
  rw [displacement_eq_fixedCodim s.f8 ρ d y hy]
  have he : (zpowers y).subgroupOf (H ⊔ A) =
      zpowers (⟨y,hy⟩ : ↥(H ⊔ A : Subgroup G)) := by
    apply map_injective (H ⊔ A : Subgroup G).subtype_injective
    rw [map_subgroupOf_eq_of_le (zpowers_le.mpr hy),MonoidHom.map_zpowers]
    rfl
  change n ≤ fixedCodim ρ (((zpowers y).subgroupOf (H ⊔ A)).map q)
  rw [he,MonoidHom.map_zpowers,fixedCodim_zpowers_eq_displacement_rank]
  exact hb


/-- The displacement source is established for every degree at least nine. -/
theorem Seed.largeDisplacement_of_nine_le (s : Seed T L H A n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : CartanPair T L H A B) (hn : 9 ≤ n) :
    LargeDisplacement (setup T L s.V H A) := by
  intro y hy _ hne
  exact hn.trans (s.degree_le_displacement hTL hpsl c hy hne)
private theorem exponent_le_four_of_kernel_movement
    (s : Seed T L H A n) (C : s.f8.CriticalPath)
    (hmove : ⁅C.DH,C.Ug⁆ ≠ ⊥) : n ≤ 4 := by
  let E := setup T L s.V H A
  let := ChapterF.Section08.Setup.lemma_F_8_5_two s.f8
  have hDH : IsPGroup 2 C.DH :=
    (IsElementaryAbelian.isPGroup 2 E.U).to_le (commutatorPreimage_le _ _ _)
  have hspan : C.Ug = ⨆ (b : E.H) (l : L),
      E.V₁.map (MulAut.conj ((C.g : G)*b*l)).toMonoidHom := by
    change (conjugateSpanBy s.V E.H).map _ = _
    conv_lhs => arg 2; arg 1; rw [← s.point_span]
    rw [conjugateSpanBy_eq_iSup_conj, Subgroup.map_iSup]
    congr 1
    funext b
    rw [conjugateSpanBy_eq_iSup_conj, Subgroup.map_iSup, Subgroup.map_iSup]
    congr 1
    funext l
    change ((E.V₁.conjBy l).conjBy b).conjBy C.g = _
    rw [← conjBy_mul, ← conjBy_mul]
    rfl
  have hm : ∃ (b : E.H) (l : L), ¬ C.DH ≤ centralizer
      (E.V₁.map (MulAut.conj ((C.g : G)*b*l)).toMonoidHom : Set G) := by
    by_contra! hh
    apply hmove
    apply commutator_eq_bot_iff_le_centralizer.mpr
    apply le_centralizer_iff.mpr
    rw [hspan]
    exact iSup_le fun b => iSup_le fun l => le_centralizer_iff.mp (hh b l)
  obtain ⟨b,l,hm⟩ := hm
  let a : G := (C.g : G)*b*l
  let W := E.V₁.map (MulAut.conj a).toMonoidHom
  have hWU : W ≤ C.Ug := by rw [hspan]; exact le_iSup_of_le b (le_iSup_of_le l le_rfl)
  have hd : W ⊓ E.QH = ⊥ := by
    apply _root_.eq_bot_iff.mpr
    intro x hx
    apply mem_bot.mpr
    by_contra hx1
    have hxc : x ∈ centralizer (C.DH : Set G) := kernel_intersection_centralizes C W hWU hx
    apply hm
    exact s.twoGroup_centralizes_point_of_fixed C.DH hDH a x hx.1 hx1
      (by intro d hd; exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp hxc d hd))
  let : IsElementaryAbelian 2 E.V₁ := IsElementaryAbelian.of_injective
    (inclusion (point_le_span s.f8)) (inclusion_injective _)
  let : IsElementaryAbelian 2 W := IsElementaryAbelian.map _
  have hi := quotient_image_index_le W (hWU.trans C.Ug_le_H)
  rw [← inf_relIndex_right, inf_comm, hd, relIndex_bot_left,
    card_map_of_injective (MulAut.conj a).injective, s.point_card] at hi
  have hp : 2^n ≤ 2^4 := hi.trans (Nat.pow_le_pow_right (by decide) s.quotient_rank)
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp hp

/-- The Cartan's fixed-point-free action bounds the field degree without
assuming the nine-dimensional displacement estimate. -/
theorem Seed.exponent_le_four (s : Seed T L H A n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : CartanPair T L H A B) : n ≤ 4 := by
  let E := setup T L s.V H A
  obtain ⟨C⟩ := s.f8.exists_criticalPath
  by_cases hmove : ⁅C.DH,C.Ug⁆ = ⊥
  · by_cases hle : C.Ug ≤ E.QH
    · apply s.centralized_exponent_le_four C
      rw [Dg_eq_core_intersection C,inf_eq_right.mpr hle]
    · obtain ⟨y,hy,hyQ⟩ := SetLike.not_le_iff_exists.mp hle
      have hfix : C.DH ≤ commutatorPreimage E.U (zpowers y) E.V₁ :=
        le_commutatorPreimage (commutatorPreimage_le _ _ _)
          ((commutator_mono le_rfl (zpowers_le.mpr hy)).trans (hmove.le.trans bot_le))
      have hi := (relIndex_le_of_le_left hfix
        (show C.DH.relIndex E.U ≠ 0 from index_ne_zero_of_finite)).trans
        (s.critical_indices_le_sixteen C).2
      have hsmall : displacement E y ≤ 4 := by
        have hh := Nat.log_mono_right (b := 2) hi
        exact hh.trans (by decide)
      exact (s.degree_le_displacement hTL hpsl c (C.Ug_le_H hy) hyQ).trans hsmall
  · exact exponent_le_four_of_kernel_movement s C hmove

/-- Only degree three remains in the odd-degree source configuration. -/
theorem Seed.exponent_eq_three_of_odd (s : Seed T L H A n)
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G))
    (hpsl : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 2 (2 ^ n))
    (c : CartanPair T L H A B) (hn : 1 < n) (hodd : Odd n) : n = 3 := by
  have hb := s.exponent_le_four hTL hpsl c
  obtain ⟨k,hk⟩ := hodd
  omega

end CFSG.Quasithin.Chapter6.Source.RankOneGeneric.LinearParity
