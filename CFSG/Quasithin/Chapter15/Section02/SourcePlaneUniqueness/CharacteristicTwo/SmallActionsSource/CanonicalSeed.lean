module
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.SmallActionsSource.PairApplications
public import Theory.GroupTheory.SpecificGroups.SymmetricThreeProductResidual
public import CFSG.Quasithin.Chapter15.Section02.SourcePlaneUniqueness.CharacteristicTwo.ComponentModels.LinearThree.BinaryResidualAction

/-!
# Conjugate canonical seeds in the Omega action

For the literal Y₁ = O^{3′}(M ∩ I), the original action of M on V has
kernel C_M(V) contained in NI. Pull back the elementary abelian residual
of S₃ × S₃. The intersection of NI with that preimage is normal there,
and taking O^{3′} does not change when restricting to this intersection.
Consequently Y₁ and each of its M-conjugates are normal in one common
subgroup. This proves their mutual commutator containment directly.

The corrected local normalizer argument now proves the canonical-seed
instance of 15.2.22 without a seed-family commutator premise. The binary
component application also consumes the existing parabolic action,
residual comparison and S₃ quotient proofs. Its complementary-factor
commutator and K = Kc remain explicit in this module.

This is a specialized route for the canonical seed, not the arbitrary-seed
Frattini argument in the printed lemma. The actual Omega action is an
earlier 15.2.13 input from qt-e-152-plane-geometry and
qt-e-152-small-parabolic; final source discharge remains with
qt-e-152-plane-uniqueness.

Source: Aschbacher--Smith, combined manuscript (1 March 2004),
15.2.22 and the binary branch of 15.2.23, printed pp.1114--1116;
refs/quasithin.pdf.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
open ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem residual_normal_in_abelian_preimage
    (U : Subgroup G) (f : G →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hk : f.ker ≤ U) :
    let A := (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))).comap f
    (primeToResidual 3 U).map U.subtype ≤ A ∧
      A ≤ normalizer (((primeToResidual 3 U).map U.subtype : Subgroup G) : Set G) := by
  let R := pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
  let A := R.comap f
  let : IsMulCommutative R := IsPGroup.isMulCommutative_of_card_eq_prime_sq
    (p := 3) (show Nat.card R = 3 ^ 2 from SymmetricThreeProductResidual.residual_card)
  let g : A →* R := (f.comp A.subtype).codRestrict R (fun x => x.property)
  have hker : g.ker ≤ (A ⊓ U).subgroupOf A := by
    intro x hx
    refine ⟨x.property, hk ?_⟩
    exact congrArg Subtype.val hx
  have hnormal : ((A ⊓ U).subgroupOf A).Normal := by
    rw [← comap_map_eq_self hker]
    infer_instance
  have hn : A ≤ normalizer ((A ⊓ U : Subgroup G) : Set G) :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mp hnormal
  have hres : primeToResidual 3 G ≤ A := by
    apply primeToResidual_le
    rw [show A = R.comap f from rfl, index_comap]
    have hi : R.index = 4 := by
      dsimp only [R]
      rw [SymmetricThreeProductResidual.residual_eq, index_prod]
      simp
    exact (show Nat.Coprime 3 R.index from hi ▸ (by decide)).coprime_dvd_right
      (R.relIndex_dvd_index_of_normal f.range)
  have he := embedded_primeToResidual_inf_eq_of_normal 3 A U hres
  refine ⟨(map_primeToResidual_le_of_hom 3 U.subtype).trans hres, ?_⟩
  rw [← he]
  exact hn.trans (normalizer_le_normalizer_characteristic_image (A ⊓ U)
    (primeToResidual 3 (A ⊓ U : Subgroup G)))

private theorem canonical_commutator
    (U : Subgroup G) (f : G →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))
    (hk : f.ker ≤ U) (t : G) :
    let Y := (primeToResidual 3 U).map U.subtype
    ⁅Y, Y.map (MulAut.conj t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj t).toMonoidHom := by
  let A := (pResidual 2 (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3))).comap f
  let Y := (primeToResidual 3 U).map U.subtype
  obtain ⟨hYA, hAY⟩ := residual_normal_in_abelian_preimage U f hk
  have htA : t ∈ normalizer (A : Set G) := by rw [normalizer_eq_top]; trivial
  have hYtA : Y.map (MulAut.conj t).toMonoidHom ≤ A :=
    (map_mono hYA).trans_eq (mem_normalizer_iff_map_conj_eq.mp htA)
  exact le_inf
    (le_normalizer_iff_commutator_le_left.mp (hYtA.trans hAY))
    (le_normalizer_iff_commutator_le_right.mp
      (hYA.trans (normalizes_conjugate_of_normalizes htA hAY)))

variable {T : Sylow 2 G} {M Mc V H ZS I : Subgroup G}
variable {hsource : ChosenSmallSource T M Mc V}
variable (d : PlaneUniquenessPreceding hsource H ZS)
include d

/-- For the canonical seed used in the binary component, the actual Omega
image supplies the conjugate-family relation without a Frattini witness. -/
theorem canonical_seed_conjugate_commutator (hI : PlaneEscapes Mc ZS I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (t : G) (ht : t ∈ (T : Subgroup G)) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ⁅Y,Y.map (MulAut.conj t).toMonoidHom⁆ ≤
      Y ⊓ Y.map (MulAut.conj t).toMonoidHom := by
  let f := e.toMonoidHom.comp (actionHom M V hsource.prepared.normalized).rangeRestrict
  let U := (M ⊓ I).subgroupOf M
  have hk : f.ker ≤ U := by
    intro x hx
    have hz : (actionHom M V hsource.prepared.normalized).rangeRestrict x = 1 :=
      e.injective (hx.trans e.map_one.symm)
    have hxk : x ∈ (actionHom M V hsource.prepared.normalized).ker :=
      congrArg Subtype.val hz
    rw [actionHom_ker] at hxk
    exact ⟨x.property, d.module_centralizer_le hI hxk⟩
  let a : M := ⟨t,hsource.maximal.1.2 ht⟩
  have hp := map_mono (f := M.subtype) (canonical_commutator U f hk a)
  have he : U.map M.subtype = M ⊓ I := map_subgroupOf_eq_of_le inf_le_left
  have hm : ((primeToResidual 3 U).map U.subtype).map M.subtype =
      (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype := by
    rw [map_embedded_primeToResidual_of_hom,he]
  have hc : M.subtype.comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj t).toMonoidHom.comp M.subtype := by ext x; rfl
  have hcm : (((primeToResidual 3 U).map U.subtype).map
      (MulAut.conj a).toMonoidHom).map M.subtype =
      (((primeToResidual 3 U).map U.subtype).map M.subtype).map
        (MulAut.conj t).toMonoidHom := by
    rw [map_map, hc, ← map_map]
  rw [map_commutator, map_inf _ _ _ M.subtype_injective, hcm, hm] at hp
  exact hp


/-- The specialized source 15.2.22 conclusion for Y₁ = O^{3′}(NI).
The earlier Omega action and the genuine seed quotient are explicit;
both conjugate-family commutators and the normalizer contradiction are proved. -/
theorem canonical_seed_commutator_exclusion
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (hquot : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
      Nonempty (((Y ⊔ smallActionS T ZS : Subgroup G) ⧸
        pCore 2 (Y ⊔ smallActionS T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    {t : G}
    (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t) :
    let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
    ¬ ⁅Y,p.K₂⁆ ≤ Y ⊓ p.K₂ := by
  obtain ⟨hle,hperfect,hnormal⟩ :=
    PlaneUniquenessPreceding.LinearThree.intersection_cubic_residual_basics d hI
  exact commutator_exclusion_of_residualPair d hI hfit p
    ⟨hle,hperfect,hnormal,hquot⟩ hC
    (canonical_seed_conjugate_commutator d hI e t p.t_mem)

/-- Construct the source pair from reducibility before applying the canonical-seed
normalizer argument. No pair or same-family commutator is assumed. -/
theorem canonical_seed_exclusion_of_reducible
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
        (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hC : IsSmallActionThreePrime (M ⊓ centralizer (V : Set G)))
    (hquot : let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
      Nonempty (((Y ⊔ smallActionS T ZS : Subgroup G) ⧸
        pCore 2 (Y ⊔ smallActionS T ZS : Subgroup G)) ≃* Equiv.Perm (Fin 3)))
    (hnot : ¬ IsSmallActionIrreducible (smallActionS T ZS) (smallActionK H))
    (t : G) (ht : t ∈ (T : Subgroup G)) (htS : t ∉ smallActionS T ZS) :
    ∃ p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t,
      let Y := (primeToResidual 3 (M ⊓ I : Subgroup G)).map (M ⊓ I).subtype
      ¬ ⁅Y,p.K₂⁆ ≤ Y ⊓ p.K₂ := by
  obtain ⟨p⟩ := exists_residualPair d hI hnot t ht htS
  exact ⟨p,canonical_seed_commutator_exclusion d hI hfit e hC hquot p⟩

/-- Apply the corrected canonical-seed exclusion to the actual binary component.
The existing parabolic action proves the seed quotient, residual comparison and
forbidden commutator. Only the complementary factor and K = Kc are still needed. -/
theorem binary_component_false_of_omega_action
    (hI : PlaneEscapes Mc ZS I) (hfit : generalizedFitting I = pCore 2 I)
    (e : (actionHom M V hsource.prepared.normalized).range ≃*
      (Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    {X : Subgroup G} {F : Type} [Field F] [Finite F]
    (b : PlaneUniquenessPreceding.LinearThree.Branch M I X 1 F)
    (hout : ¬ X ≤ Mc)
    (f : (M ⊓ I : Subgroup G) →* Equiv.Perm (Fin 3))
    (hker : f.ker = (centralizer (V : Set G)).subgroupOf (M ⊓ I))
    {t : G}
    (p : ResidualPair (T : Subgroup G) (smallActionS T ZS) (smallActionK H) t)
    (hc : ⁅X,p.K₂⁆ ≤ X.pCoreIn 2)
    (hK : smallActionK H = smallActionKc H Mc) : False := by
  have hC := source_15_2_21_2_from_preceding d hK
  exact canonical_seed_commutator_exclusion d hI hfit e hC
    (b.binary_source_residual_quotient d hI hout f hker hC) p
    (b.binary_commutator_of_action d hI hout f hker hC
      (p.second_normalized inf_le_left (d.escape_index hI).2) p.second.2.2.1 hc)

end CFSG.Quasithin.Chapter15.Section02.SmallActionsSource
