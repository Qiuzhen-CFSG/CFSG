module

public import Theory.GroupTheory.QuaternionDihedralInvolutionCosets
public import Theory.GroupTheory.PGroup.RankTwoExtraspecialThirtyTwo
public import Theory.GroupTheory.PCoreFrattiniAction
public import Theory.GroupTheory.PCoreKernelRange
public import Theory.GroupTheory.SolvableFivePointAction

/-!
# The outer action on a quaternion–dihedral two-core

Let a finite solvable group have self-centralizing extraspecial two-core
`H = Q₈ ∘ D₈`. Conjugation on the five nonidentity central involution cosets
has kernel exactly `H`. If four divides the core index, its actual image
has order twenty, odd core of order five, and cyclic Sylow two-subgroups
of order four. Thus all noncentral involutions of `H` are conjugate in the
ambient group.

The five-point kernel is the central-quotient kernel, hence the Frattini
kernel. The solvable five-point calculation identifies the image. A
five-cycle moves the central cosets and inner conjugation moves the two
involutions within a coset. In particular it is the full ambient action,
rather than the odd subgroup alone, that fuses the ten involutions.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

namespace Subgroup

private theorem quotientAut_kernel_congr {H : Type*} [Group H]
    (U V : Subgroup H) [U.Characteristic] [V.Characteristic] (h : U = V) :
    (quotientAut U).ker = (quotientAut V).ker := by
  subst V
  rfl

/-- The actual conjugation action on central involution cosets of the two-core. -/
@[expose] public noncomputable def pCoreCentralInvolutionAction
    (K : Type*) [Group K] : K →* Equiv.Perm (CentralInvolutionCosets (pCore 2 K)) :=
  centralInvolutionCosetAction.comp MulAut.conjNormal

variable {K : Type*} [Group K] [Finite K] [IsExtraspecial 2 (pCore 2 K)]

/-- The quaternion–dihedral core is exactly the kernel of its five-point action. -/
public theorem quaternion_dihedral_pCore_action_kernel
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (B C : Subgroup (pCore 2 K))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* DihedralGroup 4))
    (hcomm : C ≤ centralizer (B : Set (pCore 2 K))) (hjoin : B ⊔ C = ⊤) :
    (pCoreCentralInvolutionAction K).ker = pCore 2 K := by
  unfold pCoreCentralInvolutionAction
  rw [← MonoidHom.comap_ker,
    quaternion_dihedral_central_involution_coset_kernel B C hB hC hcomm hjoin,
    ← quotientAut_kernel_congr (frattini (pCore 2 K)) (center (pCore 2 K))
      IsExtraspecial.frattini_eq_center_two,
    MonoidHom.comap_ker]
  exact pCore_frattini_action_kernel 2 hcentral

/-- The outer quotient acts faithfully on the five intrinsic involution cosets. -/
public theorem quaternion_dihedral_pCore_faithful_outer_action
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcard : Nat.card (pCore 2 K) = 32)
    (B C : Subgroup (pCore 2 K))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* DihedralGroup 4))
    (hcomm : C ≤ centralizer (B : Set (pCore 2 K))) (hjoin : B ⊔ C = ⊤) :
    Nat.card (CentralInvolutionCosets (pCore 2 K)) = 5 ∧
      ∃ f : (K ⧸ pCore 2 K) →* Equiv.Perm (CentralInvolutionCosets (pCore 2 K)),
        Function.Injective f ∧
        f.comp (QuotientGroup.mk' (pCore 2 K)) = pCoreCentralInvolutionAction K := by
  have hk := quaternion_dihedral_pCore_action_kernel hcentral B C hB hC hcomm hjoin
  refine ⟨quaternion_dihedral_central_involution_cosets_card hcard B C hB hC hcomm hjoin,
    QuotientGroup.lift _ (pCoreCentralInvolutionAction K) hk.symm.le,
    (QuotientGroup.injective_lift_iff _ _ _).mpr hk.symm, ?_⟩
  rfl

/-- Four-divisibility forces the literal outer-action image to have order twenty,
with odd core of order five and cyclic-four Sylow two-subgroups. -/
public theorem quaternion_dihedral_pCore_action_range
    (hsolv : Group.IsSolvable K)
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcard : Nat.card (pCore 2 K) = 32)
    (B C : Subgroup (pCore 2 K))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* DihedralGroup 4))
    (hcomm : C ≤ centralizer (B : Set (pCore 2 K))) (hjoin : B ⊔ C = ⊤)
    (hfour : 4 ∣ (pCore 2 K).index) :
    Nat.card (pCoreCentralInvolutionAction K).range = 20 ∧
      Nat.card (pPrimeCore 2 (pCoreCentralInvolutionAction K).range) = 5 ∧
      ∀ P : Sylow 2 (pCoreCentralInvolutionAction K).range,
        Nat.card P = 4 ∧ IsCyclic P := by
  let a := pCoreCentralInvolutionAction K
  have hk : a.ker = pCore 2 K :=
    quaternion_dihedral_pCore_action_kernel hcentral B C hB hC hcomm hjoin
  have hfour' : 4 ∣ Nat.card a.range := by
    rwa [← index_ker, hk]
  exact solvable_faithful_five_point_action
    (Group.isSolvable_of_surjective a.rangeRestrict_surjective)
    (pCore_range_eq_bot_of_ker_eq_pCore 2 a hk)
    (quaternion_dihedral_central_involution_cosets_card hcard B C hB hC hcomm hjoin)
    a.range.subtype a.range.subtype_injective hfour'

/-- The odd core of the actual outer image is a faithful, transitive group
of order five on the central involution cosets. -/
public theorem quaternion_dihedral_pCore_odd_action
    (hsolv : Group.IsSolvable K)
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcard : Nat.card (pCore 2 K) = 32)
    (B C : Subgroup (pCore 2 K))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* DihedralGroup 4))
    (hcomm : C ≤ centralizer (B : Set (pCore 2 K))) (hjoin : B ⊔ C = ⊤)
    (hfour : 4 ∣ (pCore 2 K).index) :
    let A := (pCoreCentralInvolutionAction K).range
    let O := pPrimeCore 2 A
    let f := A.subtype.comp O.subtype
    Nat.card O = 5 ∧ Function.Injective f ∧
      ∀ x y : CentralInvolutionCosets (pCore 2 K), ∃ g : O, f g x = y := by
  classical
  dsimp only
  let A := (pCoreCentralInvolutionAction K).range
  let O := pPrimeCore 2 A
  let f := A.subtype.comp O.subtype
  have hO : Nat.card O = 5 :=
    (quaternion_dihedral_pCore_action_range hsolv hcentral hcard
      B C hB hC hcomm hjoin hfour).2.1
  have hf : Function.Injective f := A.subtype_injective.comp O.subtype_injective
  refine ⟨hO, hf, ?_⟩
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := O) 5 (by rw [hO])
  have hfg : orderOf (f g) = 5 := (orderOf_injective f hf g).trans hg
  let _ := Fintype.ofFinite (CentralInvolutionCosets (pCore 2 K))
  have hpoints : Fintype.card (CentralInvolutionCosets (pCore 2 K)) = 5 := by
    simpa only [← Nat.card_eq_fintype_card] using
      quaternion_dihedral_central_involution_cosets_card hcard B C hB hC hcomm hjoin
  have hcycle : (f g).IsCycle := Equiv.Perm.isCycle_of_prime_order'
    (by rw [hfg]; decide) (by rw [hfg, hpoints]; decide)
  have hs : (f g).support = Finset.univ := Finset.eq_univ_of_card _
    (by rw [← hcycle.orderOf, hfg, hpoints])
  intro x y
  obtain ⟨n, hn⟩ := hcycle.exists_pow_eq
    (Equiv.Perm.mem_support.mp (hs ▸ Finset.mem_univ x))
    (Equiv.Perm.mem_support.mp (hs ▸ Finset.mem_univ y))
  exact ⟨g ^ n, by change f (g ^ n) x = y; rwa [map_pow]⟩

/-- The noncentral involutions of a quaternion–dihedral two-core form one
ambient conjugacy orbit when four divides the core index. -/
public theorem quaternion_dihedral_pCore_noncentral_involutions_isConj
    (hsolv : Group.IsSolvable K)
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcard : Nat.card (pCore 2 K) = 32)
    (B C : Subgroup (pCore 2 K))
    (hB : Nonempty (B ≃* QuaternionGroup 2)) (hC : Nonempty (C ≃* DihedralGroup 4))
    (hcomm : C ≤ centralizer (B : Set (pCore 2 K))) (hjoin : B ⊔ C = ⊤)
    (hfour : 4 ∣ (pCore 2 K).index)
    (x y : pCore 2 K) (hx : orderOf x = 2) (hxZ : x ∉ center (pCore 2 K))
    (hy : orderOf y = 2) (hyZ : y ∉ center (pCore 2 K)) :
    IsConj (x : K) (y : K) := by
  have himage := (quaternion_dihedral_pCore_action_range hsolv hcentral hcard
    B C hB hC hcomm hjoin hfour).1
  apply isConj_noncentral_involutions_of_five_cosets (pCore 2 K)
    (quaternion_dihedral_central_involution_cosets_card hcard B C hB hC hcomm hjoin)
    ?_ x y hx hxZ hy hyZ
  change 5 ∣ Nat.card (pCoreCentralInvolutionAction K).range
  rw [himage]
  decide

/-- The intrinsic rank-two formulation for recognition callers: an
extraspecial core of order thirty-two has a single noncentral involution
orbit under the same self-centralization and index hypotheses. -/
public theorem extraspecial_pCore_noncentral_involutions_isConj_of_rank_two
    (hsolv : Group.IsSolvable K)
    (hcentral : centralizer (pCore 2 K : Set K) ≤ pCore 2 K)
    (hcard : Nat.card (pCore 2 K) = 32)
    (hrank : ∀ E : Subgroup (pCore 2 K), IsElementaryAbelian 2 E → Nat.card E < 8)
    (hfour : 4 ∣ (pCore 2 K).index)
    (x y : pCore 2 K) (hx : orderOf x = 2) (hxZ : x ∉ center (pCore 2 K))
    (hy : orderOf y = 2) (hyZ : y ∉ center (pCore 2 K)) :
    IsConj (x : K) (y : K) := by
  obtain ⟨B, C, hB, hC, hcomm, hjoin, _⟩ :=
    IsExtraspecial.dihedral_quaternion_factors_of_card_thirty_two hrank hcard
  exact quaternion_dihedral_pCore_noncentral_involutions_isConj hsolv hcentral hcard
    B C hB hC hcomm hjoin hfour x y hx hxZ hy hyZ

end Subgroup
