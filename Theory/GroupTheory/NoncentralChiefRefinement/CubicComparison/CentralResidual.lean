module
public import Theory.GroupTheory.PCoreImage
public import Theory.Representation.BinaryCoprimeDegree.PerfectCentral
public import Theory.Representation.Quotient
public import Theory.Representation.NormalInvariants
public import Theory.GroupAction.NoncentralTwoChiefLength.BinaryRepresentation
public import Theory.GroupTheory.NoncentralChiefRefinement.NormalPerfectMovement
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.Bounds
public import Theory.GroupTheory.NoncentralChiefRefinement.CubicComparison.FixedIndex
public import Theory.Representation.BinaryConjugationSection.CubicLength

/-!
# Central cubic residuals force three binary chief layers

In a finite perfect group with self-centralizing two-core, a normal two-perfect
subgroup N with cubic two-core quotient and central image modulo the ambient
two-core moves a chief interval of that core. Descend the actual section action
through its kernel. Its nontrivial central cubic and the Schur-field determinant
bound force binary degree at least six, with no cubic fixed points. Coprime
commutator comparison transfers all this movement to O₂(N).

The Chapter13 covered augmentation consumer applies this to the literal
L₀ = O²(O₂,Z(L)). No faithful chief-action witness is assumed.
Source: Aschbacher--Smith, 13.4.10(2), printed p.908; the central-scalar
Schur-field argument underlying the binary degree bound.
-/

public noncomputable section
open Subgroup Representation
open scoped commutatorElement IsMulCommutative
namespace NoncentralChiefRefinement.CubicComparison
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [Finite W]

private theorem central_cubic_fixedIndex
    [Group.IsPerfect H] (ρ : Representation (ZMod 2) H W) [ρ.IsIrreducible]
    (A : Subgroup H) (hA : Nat.card A = 3) (hc : A ≤ center H)
    (hm : ¬ A ≤ ρ.ker) : 64 ≤ BinaryFixedPoints.fixedIndex (ρ.comp A.subtype) := by
  let q := QuotientGroup.mk' ρ.ker
  let σ := quotientOfLEKer ρ ρ.ker le_rfl
  let : σ.IsIrreducible := (quotientOfLEKer_irreducible_iff ρ _ le_rfl).mpr inferInstance
  have hf : Function.Injective σ := by
    apply (MonoidHom.ker_eq_bot_iff σ).mp
    apply bot_unique
    intro x hx
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective ρ.ker x
    exact (QuotientGroup.eq_one_iff g).mpr hx
  have hAc : A.map q ≤ center (H ⧸ ρ.ker) := by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective ρ.ker x
    exact (map_mul q g a).symm.trans ((congrArg q (mem_center_iff.mp (hc ha) g)).trans (map_mul q a g))
  have hcard : Nat.card (A.map q) = 3 := by
    have hd : Nat.card (A.map q) ∣ 3 := hA ▸ card_map_dvd A q
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he
    · have hz := eq_bot_of_card_eq (A.map q) he
      exact (hm (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp hz)).elim
    · exact he
  have hd := BinaryCoprimeDegree.perfect_central_prime_degree σ hf Nat.prime_three
    (by decide : 3 ≠ 2) (hcard ▸ card_dvd_of_le hAc)
  have hd6 : 6 ≤ Module.finrank (ZMod 2) W := by simpa only [show orderOf (2 : ZMod 3) = 2 from (orderOf_eq_iff (by decide : 0 < 2)).mpr (by decide)] using hd
  let : A.Normal := ⟨fun x hx g => by
    simpa only [mem_center_iff.mp (hc hx) g, mul_inv_cancel_right] using hx⟩
  have hfix : invariants (ρ.comp A.subtype) = ⊥ := by
    by_contra hn
    exact hm (le_ker_of_normal_invariants_ne_bot ρ A hn)
  have hindex := BinaryFixedPoints.fixedIndex_mul_card (ρ.comp A.subtype)
  rw [hfix, Nat.card_unique, mul_one, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Nat.card_zmod] at hindex
  rw [hindex]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hd6


variable {G : Type*} [Group G] [Finite G] [Group.IsPerfect G]

/-- A normal two-perfect central-cover residual moves at least three binary
layers on its own two-core inside a perfect group with self-centralizing two-core. -/
theorem central_residual_cubic_length_ge_three
    (N : Subgroup G) [N.Normal] (hpN : IsPPerfect 2 N)
    (hc : N.map (QuotientGroup.mk' (pCore 2 G)) ≤ center (G ⧸ pCore 2 G))
    (hq : Nat.card (N ⧸ pCore 2 N) = 3)
    (hself : centralizer (pCore 2 G : Set G) ≤ pCore 2 G)
    (A : Subgroup G) (hA : Nat.card A = 3) (hAN : A ≤ N) :
    3 ≤ conjugationCubicLength A (N.pCoreIn 2) := by
  let Q := pCore 2 G
  have hAp : IsPGroup 3 A := IsPGroup.of_card (n := 1) (by simpa using hA)
  have hnot : ¬ A ≤ Q := by
    intro hh
    have hco := IsPGroup.coprime_card_of_ne 2 3 (by decide) A A
      (pCore_isPGroup.to_le hh) hAp
    rw [hA] at hco
    exact (by decide : ¬ Nat.Coprime 3 3) hco
  have hm : ¬ ⁅Q,N⁆ ≤ (⊥ : Subgroup G) := by
    intro hh
    have hcN := le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp (bot_unique hh))
    exact hnot (hAN.trans (hcN.trans hself))
  let Qn : NormalNode G := ⟨Q,inferInstanceAs Q.Normal⟩
  let Nn : NormalNode G := ⟨N,inferInstanceAs N.Normal⟩
  obtain ⟨B,U,_,hBU,hUQ,hmove⟩ := exists_moved_chief_of_normal_twoPerfect
    (⊥ : NormalNode G) Qn Nn bot_le pCore_isPGroup hpN hm
  let := chief_elementary B U hBU (pCore_isPGroup.to_le hUQ)
  let ρ : Representation (ZMod 2) G (Additive (Section B U)) := binarySectionRepresentation B U
  let : ρ.IsIrreducible := binarySection_irreducible B U hBU
  have hQker : Q ≤ ρ.ker := normal_p_subgroup_le_ker ρ Q pCore_isPGroup
  have hNker : ¬ N ≤ ρ.ker := by
    intro hh
    apply hmove
    rw [commutator_comm,commutator_le]
    intro n hn u hu
    have he := LinearMap.congr_fun (hh hn)
      (Additive.ofMul (QuotientGroup.mk' (B.val.subgroupOf U.val) ⟨u,hu⟩))
    change sectionAction B U n (QuotientGroup.mk' _ ⟨u,hu⟩) =
      QuotientGroup.mk' _ ⟨u,hu⟩ at he
    have he' := QuotientGroup.eq_iff_div_mem.mp he
    change n * u * n⁻¹ / u ∈ B.val at he'
    simpa only [commutatorElement_def,div_eq_mul_inv] using he'
  have hNcore : N.pCoreIn 2 ≤ Q :=
    le_sSup ⟨inferInstanceAs ((pCore 2 N).map N.subtype).Normal, isPGroup_pCoreIn 2 N⟩
  let π := QuotientGroup.mk' (pCore 2 N)
  have hAi : Nat.card (A.subgroupOf N) = 3 :=
    (Nat.card_congr (subgroupOfEquivOfLe hAN).toEquiv).trans hA
  have hAiπ : (A.subgroupOf N).map π = ⊤ := by
    apply eq_of_le_of_card_ge le_top
    rw [card_top,hq,GLS3.Chapter5.cubic_image_card_of_two_kernel π
      (by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup) _ hAi]
  have hsup : A ⊔ N.pCoreIn 2 = N := by
    have hh := congrArg (map N.subtype) (congrArg (comap π) hAiπ)
    simpa only [pCoreIn,π,comap_map_eq,comap_top,Subgroup.map_sup,QuotientGroup.ker_mk',
      map_subgroupOf_eq_of_le hAN,←MonoidHom.range_eq_map,range_subtype] using hh
  have hAmove : ¬ A ≤ ρ.ker := by
    intro hh
    exact hNker (hsup ▸ sup_le hh (hNcore.trans hQker))
  let q := QuotientGroup.mk' ρ.ker
  let σ := quotientOfLEKer ρ ρ.ker le_rfl
  let : σ.IsIrreducible := (quotientOfLEKer_irreducible_iff ρ _ le_rfl).mpr inferInstance
  have hAc : A.map q ≤ center (G ⧸ ρ.ker) := by
    rintro _ ⟨a,ha,rfl⟩
    apply mem_center_iff.mpr
    intro x
    obtain ⟨g,rfl⟩ := QuotientGroup.mk'_surjective ρ.ker x
    have hm := mem_center_iff.mp (hc (mem_map_of_mem _ (hAN ha)))
      (QuotientGroup.mk' (pCore 2 G) g)
    have he : g * a / (a * g) ∈ Q := (QuotientGroup.eq_iff_div_mem.mp (by
      change QuotientGroup.mk' Q (g * a) = QuotientGroup.mk' Q (a * g)
      rw [map_mul,map_mul]
      exact hm))
    exact (map_mul q g a).symm.trans ((QuotientGroup.eq_iff_div_mem.mpr (hQker he)).trans
      (map_mul q a g))
  have hAcard : Nat.card (A.map q) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (hA ▸ card_map_dvd A q) with hh | hh
    · exact (hAmove (by simpa only [q,QuotientGroup.ker_mk'] using (map_eq_bot_iff A).mp (eq_bot_of_card_eq _ hh))).elim
    · exact hh
  have hAm : ¬ A.map q ≤ σ.ker := by
    intro hh
    exact hAmove (fun a ha => hh (mem_map_of_mem q ha))
  have hb := central_cubic_fixedIndex σ (A.map q) hAcard hAc hAm
  have hidx : BinaryFixedPoints.fixedIndex (ρ.comp A.subtype) =
      BinaryFixedPoints.fixedIndex (σ.comp (A.map q).subtype) := by
    let := BinaryFixedPoints.action (ρ.comp A.subtype)
    exact BinaryFixedPoints.fixedIndex_eq_of_equivariant _
      (q.subgroupMap A) (q.subgroupMap_surjective A) (MulEquiv.refl _) (fun _ _ => rfl)
  rw [←hidx] at hb
  have hsec : sectionCubicLength A B.val U.val =
      Nat.log 4 (BinaryFixedPoints.fixedIndex (ρ.comp A.subtype)) := by
    let := quotientConjugationAction A U.val B.val le_normalizer_of_normal le_normalizer_of_normal
    rw [sectionCubicLength_eq_quotient_of_twoGroup A U.val B.val hAp
      (pCore_isPGroup.to_le hUQ) hBU.le le_normalizer_of_normal le_normalizer_of_normal]
    exact BinaryFixedPoints.cubicLength_eq_of_equivariant (ρ.comp A.subtype)
      (MonoidHom.id A) Function.surjective_id (MulEquiv.refl _) (fun _ _ => rfl)
  have hl : 3 ≤ sectionCubicLength A B.val U.val := by
    rw [hsec]
    exact (show Nat.log 4 64 = 3 by decide) ▸ Nat.log_mono_right hb
  have hu := conjugationCubicLength_mono A hUQ
  change conjugationCubicLength A U.val ≤ conjugationCubicLength A (pCore 2 G) at hu
  have hlQ : 3 ≤ conjugationCubicLength A Q := by
    unfold sectionCubicLength at hl
    change conjugationCubicLength A U.val ≤ conjugationCubicLength A Q at hu
    omega
  let : (N.pCoreIn 2).Normal := inferInstanceAs ((pCore 2 N).map N.subtype).Normal
  have hcomm : ⁅Q,A⁆ ≤ N.pCoreIn 2 :=
    (commutator_mono le_rfl hAN).trans
      ((commutator_le_core_commutator_of_isSubnormal N Q
        (inferInstance : N.Normal).isSubnormal hpN pCore_isPGroup le_normalizer_of_normal).trans
          (map_mono (commutator_le_left (pCore 2 N) ⊤)))
  have he := length_eq_of_commutator_le A Q (N.pCoreIn 2) hAp pCore_isPGroup hNcore
    le_normalizer_of_normal le_normalizer_of_normal hcomm
  exact he ▸ hlQ

end NoncentralChiefRefinement.CubicComparison
