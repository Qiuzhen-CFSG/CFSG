module

public import Stellmacher.Recognition.MaximalC2S4Centralizer
public import Theory.SpecificGroups.CyclicTwoSymmetricFourSylow

/-!

# The Sylow centralizer in the order-32 C₂ times S₄ branch

Suppose a finite group has a supplied Sylow two-subgroup of order 32 and a
maximal two-local subgroup isomorphic to `C₂ × S₄`. There is an involution
in the supplied Sylow whose full centralizer is `C₂ × S₄` and whose Sylow
centralizer is `C₂ × D₈`, of order sixteen and index two. This involution
has no square root anywhere in the ambient group.

Start with the full-centralizer witness from maximal two-locality. Choose
a local Sylow containing its central involution and extend it to an ambient
Sylow with exactly that local intersection. An actual Sylow conjugator
moves the whole configuration into the supplied Sylow. The centralizer is
identified by that intersection, not by classifying groups of order 32.
Any square root commutes with its square, so a putative ambient square root
would lie in the full centralizer. Its central involution is not a square
in `C₂ × S₄`, as seen from the first factor and the trivial center of S₄.

Source: the initial case-(c) analysis in Kurzweil–Stellmacher, The Theory of
Finite Groups, Chapter 12, printed p. 367. The chapter's later use of the
additional Z condition is not needed for these conclusions.
-/

open scoped Pointwise

namespace Stellmacher.Recognition

private def centralizerEquiv {A B : Type*} [Group A] [Group B]
    (e : A ≃* B) (a : A) :
    Subgroup.centralizer ({a} : Set A) ≃*
      Subgroup.centralizer ({e a} : Set B) where
  toFun x := ⟨e x, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    simpa only [map_mul] using
      congrArg e (Subgroup.mem_centralizer_singleton_iff.mp x.property)⟩
  invFun x := ⟨e.symm x, by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply e.injective
    simpa only [map_mul, MulEquiv.apply_symm_apply] using
      Subgroup.mem_centralizer_singleton_iff.mp x.property⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x)
  right_inv x := Subtype.ext (e.apply_symm_apply x)
  map_mul' x y := Subtype.ext (e.map_mul x y)

set_option maxRecDepth 100000 in
private theorem model_center_not_square :
    ∀ t : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4),
      t ∈ Subgroup.center _ → t ≠ 1 →
        ∀ x : Multiplicative (ZMod 2) × Equiv.Perm (Fin 4), x ^ 2 ≠ t := by
  decide

private theorem central_involution_not_square
    {G : Type*} [Group G] [Finite G] (P : Subgroup G)
    (e : P ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))
    (a : G) (ha : orderOf a = 2)
    (hC : Subgroup.centralizer ({a} : Set G) = P) :
    ∀ x : G, x ^ 2 ≠ a := by
  have haP : a ∈ P := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
  let aP : P := ⟨a, haP⟩
  have haCentral : aP ∈ Subgroup.center P := by
    rw [Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    apply Subgroup.mem_centralizer_singleton_iff.mp
    change (x : G) ∈ Subgroup.centralizer ({a} : Set G)
    simpa only [hC] using x.property
  have heaCentral : e aP ∈ Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := e.surjective y
    simpa only [map_mul] using congrArg e (Subgroup.mem_center_iff.mp haCentral x)
  have heaNe : e aP ≠ 1 := by
    intro h
    have he : aP = 1 := e.injective (by simpa using h)
    have haOne : a = 1 := congrArg Subtype.val he
    simp [haOne] at ha
  intro x hx
  have hxP : x ∈ P := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff, ← hx]
    simp only [pow_two, mul_assoc]
  apply model_center_not_square (e aP) heaCentral heaNe (e ⟨x, hxP⟩)
  have he : (⟨x, hxP⟩ : P) ^ 2 = aP := Subtype.ext hx
  simpa only [map_pow] using congrArg e he

/-- The exact involution-centralizer configuration supplied by the
order-32 maximal `C₂ × S₄` branch. -/
public theorem sylow32_c2s4_configuration
    {G : Type*} [Group G] [Finite G] (S0 : Sylow 2 G)
    (hOrder : Nat.card S0 = 2 ^ 5) (P : Subgroup G)
    (hP : IsMaximalTwoLocal P)
    (hModel : Nonempty (P ≃* Multiplicative (ZMod 2) × Equiv.Perm (Fin 4))) :
    ∃ t : S0, orderOf t = 2 ∧
      Nonempty (Subgroup.centralizer ({(t : G)} : Set G) ≃*
        Multiplicative (ZMod 2) × Equiv.Perm (Fin 4)) ∧
      Nonempty (Subgroup.centralizer ({t} : Set S0) ≃*
        Multiplicative (ZMod 2) × DihedralGroup 4) ∧
      Nat.card (Subgroup.centralizer ({t} : Set S0)) = 16 ∧
      (Subgroup.centralizer ({t} : Set S0)).index = 2 ∧
      ∀ x : G, x ^ 2 ≠ (t : G) := by
  classical
  obtain ⟨a, ha, hC⟩ := exists_involution_centralizer_of_maximal_c2s4 P hP hModel
  obtain ⟨e⟩ := hModel
  have haNoSquare := central_involution_not_square P e a ha hC
  have haP : a ∈ P := by
    rw [← hC, Subgroup.mem_centralizer_singleton_iff]
  let aP : P := ⟨a, haP⟩
  have haPorder : orderOf aP = 2 := (Subgroup.orderOf_coe aP).symm.trans ha
  have haPgroup : IsPGroup 2 (Subgroup.zpowers aP) :=
    IsPGroup.of_card (n := 1) (by
      simpa only [Nat.card_zpowers, pow_one] using haPorder)
  obtain ⟨T, hT⟩ := haPgroup.exists_le_sylow
  obtain ⟨S, hS⟩ := T.exists_comap_subtype_eq
  have haS : a ∈ (S : Subgroup G) := by
    have hmem : aP ∈ (T : Subgroup P) := hT (Subgroup.mem_zpowers aP)
    rw [← hS] at hmem
    exact hmem
  let s : S := ⟨a, haS⟩
  have hCS : Subgroup.centralizer ({s} : Set S) =
      ((S : Subgroup G) ⊓ P).subgroupOf (S : Subgroup G) := by
    ext x
    constructor
    · intro hx
      refine ⟨x.property, ?_⟩
      change (x : G) ∈ P
      rw [← hC, Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hx)
    · rintro ⟨_, hx⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      apply Subgroup.mem_centralizer_singleton_iff.mp
      rwa [hC]
  have hTI : (T : Subgroup P) = ((S : Subgroup G) ⊓ P).subgroupOf P := by
    rw [Subgroup.inf_subgroupOf_right]
    exact hS.symm
  let eCI : Subgroup.centralizer ({s} : Set S) ≃* ↥((S : Subgroup G) ⊓ P) :=
    (MulEquiv.subgroupCongr hCS).trans (Subgroup.subgroupOfEquivOfLe inf_le_left)
  let eTI : T ≃* ↥((S : Subgroup G) ⊓ P) :=
    (MulEquiv.subgroupCongr hTI).trans (Subgroup.subgroupOfEquivOfLe inf_le_right)
  obtain ⟨eT⟩ := CyclicTwoSymmetricFour.sylow_two_equiv ⟨e⟩ T
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S S0
  let eS : S ≃* S0 := (S.equivSMul g).trans
    (MulEquiv.subgroupCongr (congrArg Sylow.toSubgroup hg))
  let t : S0 := eS s
  have htG : (t : G) = MulAut.conj g a := rfl
  let eCentral : Subgroup.centralizer ({t} : Set S0) ≃*
      Multiplicative (ZMod 2) × DihedralGroup 4 :=
    (centralizerEquiv eS s).symm.trans ((eCI.trans eTI.symm).trans eT)
  have hcard : Nat.card (Subgroup.centralizer ({t} : Set S0)) = 16 := by
    rw [Nat.card_congr eCentral.toEquiv, Nat.card_prod]
    norm_num [Nat.card_eq_fintype_card, DihedralGroup.card]
  have hindex : (Subgroup.centralizer ({t} : Set S0)).index = 2 := by
    have h := (Subgroup.centralizer ({t} : Set S0)).card_mul_index
    rw [hcard, hOrder] at h
    norm_num at h
    omega
  refine ⟨t, (eS.orderOf_eq s).trans ?_, ?_, ⟨eCentral⟩, hcard, hindex, ?_⟩
  · exact (Subgroup.orderOf_coe s).symm.trans ha
  · rw [htG]
    exact ⟨(centralizerEquiv (MulAut.conj g) a).symm.trans
      ((MulEquiv.subgroupCongr hC).trans e)⟩
  · intro x hx
    apply haNoSquare ((MulAut.conj g).symm x)
    have he := congrArg (MulAut.conj g).symm hx
    simpa only [map_pow, htG, MulEquiv.symm_apply_apply] using he

end Stellmacher.Recognition
