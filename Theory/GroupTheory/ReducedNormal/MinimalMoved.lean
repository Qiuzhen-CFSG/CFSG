module
public import Theory.GroupTheory.ReducedNormal.MovedWitness
public import Theory.GroupTheory.CoprimeCentralizerDirectProduct
public import Theory.GroupTheory.CoprimeCentralizerDecomposition.CubicQuotient
public import Theory.GroupTheory.Commutator.NormalGeneration

/-!
# Minimal reduced subgroups moved by a normal actor

Inside a normal elementary abelian group moved by a two-perfect normal actor,
choose a subgroup of least order among the normal subgroups still moved by the
actor. The reduced-normal subgroup theorem shows that this minimal subgroup is
reduced, and commutator idempotence makes it its own displacement subgroup.
The final two lemmas give full movement inside a coprime displacement space,
including an actor with cubic quotient and a centralizing two-core.

These are the minimal-module and cubic-action steps used in the original
Aschbacher--Smith proof of 13.7.4(1), printed p.937 (A.4.11).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem exists_minimal_isPReduced_le_of_moved
    (X U : Subgroup G) (hsub : X.IsSubnormal) (hX : IsPPerfect p X)
    (hchief : HasCentralPChiefFactorsAbove p (pCore p X))
    [U.Normal] [IsElementaryAbelian p U]
    (hkill : (pCore p X).map X.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U, X⁆ ≠ ⊥) :
    ∃ V : Subgroup G, V ≤ U ∧ IsPReduced p V ∧ ⁅V, X⁆ ≠ ⊥ ∧
      ∀ A : Subgroup G, A ≤ V → A.Normal → ⁅A, X⁆ ≠ ⊥ → A = V := by
  let s : Set (Subgroup G) := {V | V ≤ U ∧ V.Normal ∧ ⁅V, X⁆ ≠ ⊥}
  have hs : s.Nonempty := ⟨U, le_rfl, inferInstance, hmoved⟩
  obtain ⟨V, hV, hmin⟩ := Set.exists_min_image s (fun V => Nat.card V) (Set.toFinite s) hs
  obtain ⟨hVU, hVn, hVm⟩ := hV
  let := hVn
  let : IsElementaryAbelian p V := IsElementaryAbelian.of_le hVU
  have hminimal : ∀ A : Subgroup G, A ≤ V → A.Normal → ⁅A, X⁆ ≠ ⊥ → A = V := by
    intro A hAV hAn hAm
    exact eq_of_le_of_card_ge hAV (hmin A ⟨hAV.trans hVU, hAn, hAm⟩)
  obtain ⟨W, hWV, hWred, hWm⟩ := exists_isPReduced_le_of_moved X V hsub hX hchief
    (hkill.trans (centralizer_le hVU)) hVm
  have he : W = V := hminimal W hWV hWred.normal hWm
  exact ⟨V, hVU, he ▸ hWred, hVm, hminimal⟩

theorem exists_minimal_isPReduced_le_of_normal_moved
    (X U : Subgroup G) [X.Normal] (hX : IsPPerfect p X)
    (hchief : HasCentralPChiefFactorsAbove p (pCore p X))
    [U.Normal] [IsElementaryAbelian p U]
    (hkill : (pCore p X).map X.subtype ≤ centralizer (U : Set G))
    (hmoved : ⁅U, X⁆ ≠ ⊥) :
    ∃ V : Subgroup G, V ≤ U ∧ IsPReduced p V ∧ V ≠ ⊥ ∧ ⁅V, X⁆ = V ∧
      ∀ A : Subgroup G, A ≤ V → A.Normal → ⁅A, X⁆ ≠ ⊥ → A = V := by
  obtain ⟨V, hVU, hred, hVm, hmin⟩ := exists_minimal_isPReduced_le_of_moved X U
    (inferInstance : X.Normal).isSubnormal hX hchief hkill hmoved
  let := hred.normal
  let := hred.elementary
  have hne : V ≠ ⊥ := by intro he; exact hVm (by simp [he])
  have he : ⁅V, X⁆ = V := hmin _ (commutator_le_left V X) inferInstance (by
    rwa [commutator_isPPerfect_idempotent X V hX
      (IsElementaryAbelian.isPGroup p V) le_normalizer_of_normal])
  exact ⟨V, hVU, hred, hne, he, hmin⟩

theorem commutator_eq_self_of_le_coprime_displacement
    (W A V : Subgroup G) [IsMulCommutative W]
    (hAW : A ≤ normalizer (W : Set G))
    (hAV : A ≤ normalizer (V : Set G))
    (hc : Nat.Coprime (Nat.card A) (Nat.card W))
    (hV : V ≤ ⁅W,A⁆) : ⁅V,A⁆ = V := by
  have hVW : V ≤ W := hV.trans (le_normalizer_iff_commutator_le_left.mp hAW)
  let : IsMulCommutative V := IsMulCommutative.of_comm fun x y =>
    (inclusion_injective hVW) (by simp only [map_mul, mul_comm])
  have hcop : Nat.Coprime (Nat.card A) (Nat.card V) :=
    hc.of_dvd_right (card_dvd_of_le hVW)
  have hd := commutator_disjoint_centralizer_of_coprime W A hAW hc
  have hfix : V ⊓ centralizer (A : Set G) = ⊥ := by
    apply bot_unique
    intro x hx
    exact hd.le_bot ⟨hV hx.1,hVW hx.1,hx.2⟩
  have he := eq_commutator_sup_centralizer_of_solvable_coprime V A hAV
    (Group.isSolvable_of_comm fun x y => mul_comm x y) hcop
  simpa only [hfix,sup_bot_eq] using he.symm

theorem commutator_eq_self_of_le_cubic_displacement
    (W A V : Subgroup G) [W.Normal] [V.Normal] [IsMulCommutative W]
    (hW : IsPGroup 2 W)
    (hcore : A.pCoreIn 2 ≤ centralizer (W : Set G))
    (hcard : Nat.card (A ⧸ pCore 2 A) = 3)
    (hz : ∃ z ∈ A, orderOf z = 3)
    (hV : V ≤ ⁅W,A⁆) : ⁅V,A⁆ = V := by
  obtain ⟨z,hzA,hz3⟩ := hz
  have hzle : zpowers z ≤ A := zpowers_le.mpr hzA
  have hgen := pCoreIn_sup_zpowers_eq_of_quotient_card_three hcard hzA hz3
  have hsplit : ⁅W,A.pCoreIn 2 ⊔ zpowers z⁆ = ⁅W,A.pCoreIn 2⁆ ⊔ ⁅W,zpowers z⁆ := by
    simpa [iSup_bool_eq] using
      commutator_iSup_of_normal_left W (fun b : Bool => if b then A.pCoreIn 2 else zpowers z)
  have hc : ⁅W,A.pCoreIn 2⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hcore
  have he : ⁅W,A⁆ = ⁅W,zpowers z⁆ := by rw [←hgen,hsplit,hc,bot_sup_eq]
  have hpz : IsPGroup 3 (zpowers z) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers,hz3,pow_one])
  have hcop := IsPGroup.coprime_card_of_ne 3 2 (by decide) (zpowers z) W hpz hW
  have hm : ⁅V,zpowers z⁆ = V := commutator_eq_self_of_le_coprime_displacement W (zpowers z) V
    le_normalizer_of_normal le_normalizer_of_normal hcop (hV.trans_eq he)
  apply le_antisymm (commutator_le_left V A)
  exact hm.ge.trans (commutator_mono le_rfl hzle)

end Theory.GroupTheory
