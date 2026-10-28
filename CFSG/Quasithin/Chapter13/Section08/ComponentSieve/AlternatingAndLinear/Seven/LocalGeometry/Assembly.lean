module
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.FirstCase
public import CFSG.Quasithin.Chapter13.Section08.ComponentSieve.AlternatingAndLinear.Seven.LocalGeometry.Reduction
public import Theory.ElementaryAbelian.Quotient
public import Theory.ElementaryAbelian.VectorSpace
/-!
# The source local reduction for the A₇ exclusion

The module is the literal Ũ_H = ⟨V₃^H⟩/V₁, with its faithful H/O₂(H)
action specified on quotient representatives. The earlier inputs used here
are relative component normality (13.8.16), H = KT (13.8.21), the theta
identity (13.7.3(9)), universal solvable exclusion (13.8.13), the genuine
13.8.5 group/module alternatives, and 13.8.8 with the F.9.13 conjugated
critical actors. The triple-cover marking uses the actual L₁/O₂(L₁) ≃ E₉.
These are explicit earlier-source inputs, not assertions proved in this file.

Construct the faithful action from K/O₂(K) ≃ A₇, exclude each possible
first-case actor by FirstCase, then apply the proved solvable partition
calculation and theta argument. The output retains the component marking
on every representative, the three Sylow orbits, the full used case-(2)
clauses, the original β conjugacy and the actual Vα* ≤ O₂(L₁*T*) conjugate.
The separate Reduction module justifies application to original overgroups
through the source's KL₁T member of Hz. Neither case-(2) partition
contradiction, nor the final exclusion of A₇, is claimed here.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
13.8.24, printed pp.958–959, using 13.8.5, 8, 13, 16, 21 and F.9.13
(combined manuscript, 1 March 2004).
-/

public section
open Subgroup Equiv Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
variable {G : Type*} [Group G]
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]

/-- The precise case-(2) clauses used in 13.8.24, before passing the marked
conjugate to the star quotient. The indices use the actual D_H and U_H. -/
@[expose] def SecondCase (H L₁ T U_H Uγ Vγ A₁ V₁ : Subgroup G)
    (ρ : Representation (ZMod 2) (Source.Hstar H) E) : Prop :=
  Source.Dgamma Uγ U_H V₁ < Uγ ∧ Source.DH U_H Uγ A₁ < U_H ∧
  0 < rank (Source.starImage H Uγ) ∧
  Nat.log 2 ((Source.DH U_H Uγ A₁).relIndex U_H) ≤ rank (Source.starImage H Uγ) ∧
  IsElementaryTwo (Source.starImage H Uγ) ∧ IsQuadratic ρ (Source.starImage H Uγ) ∧
  fixedCodim ρ (Source.starImage H Uγ) ≤ 2 * rank (Source.starImage H Uγ) ∧
  ∃ h : H, Vγ.map (MulAut.conj (h : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2

/-- Conjugating the coordinates preserves the exact alternating component image. -/
theorem alternating_image_conjugate {J : Type*} [Group J]
    (φ : J →* S7) (D : Subgroup J) (hD : D.map φ = alternatingGroup (Fin 7))
    (σ : S7) : D.map ((MulAut.conj σ).toMonoidHom.comp φ) = alternatingGroup (Fin 7) := by
  rw [← map_map, hD]
  exact mem_normalizer_iff_map_conj_eq.mp (by
    rw [(alternatingGroup (Fin 7)).normalizer_eq_top]
    exact mem_top σ)

variable [Finite G]

private theorem base_solvable (L₁ T : Subgroup G)
    [Group.IsSolvable L₁] (hT : IsPGroup 2 T)
    (hn : T ≤ normalizer (L₁ : Set G)) : Group.IsSolvable (L₁ ⊔ T : Subgroup G) := by
  let : Group.IsNilpotent T := hT.isNilpotent
  let A := L₁.subgroupOf (L₁ ⊔ T)
  let B := T.subgroupOf (L₁ ⊔ T)
  let : A.Normal := normal_subgroupOf_of_le_normalizer (sup_le L₁.le_normalizer hn)
  let : Group.IsSolvable A := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show L₁ ≤ L₁ ⊔ T from le_sup_left)).toMonoidHom)
    (subgroupOfEquivOfLe (show L₁ ≤ L₁ ⊔ T from le_sup_left)).injective
  let : Group.IsSolvable B := Group.isSolvable_of_isSolvable_injective
    (f := (subgroupOfEquivOfLe (show T ≤ L₁ ⊔ T from le_sup_right)).toMonoidHom)
    (subgroupOfEquivOfLe (show T ≤ L₁ ⊔ T from le_sup_right)).injective
  apply Group.isSolvable_of_normal_sup_eq_top A B
  apply map_injective (L₁ ⊔ T).subtype_injective
  simp [A, B, Subgroup.map_sup, le_sup_left, le_sup_right, ← MonoidHom.range_eq_map]

/-- The local permutation reduction. The earlier source clauses used here are
explicit assertions on the actual groups and quotient-conjugation action. Case (1) is proved
impossible; neither of the two remaining partition contradictions is assumed.
The quotient conjugators of both marked V actors and of V_alpha are retained. -/
theorem local_geometry
    (H K L L₁ T G₁ M V₃ Uγ Vγ Uβ Vβ A₁ V₁ : Subgroup G)
    [IsElementaryAbelian 2 (Source.UH H V₃)]
    [(V₁.subgroupOf (Source.UH H V₃)).Normal]
    (_hV₁ : V₁ ≤ Source.UH H V₃)
    (hH : H ∈ Source.Hz L₁ T G₁ M) (hKH : K ≤ H)
    (hK : (K.subgroupOf H).IsCComponent) (hKn : (K.subgroupOf H).Normal)
    (S : Sylow 2 H) (hS : (S : Subgroup H) = T.subgroupOf H)
    (hT : IsPGroup 2 T) (h21 : K ⊔ T = H)
    (eK : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7))
    [Group.IsSolvable L₁] (hTN : T ≤ normalizer (L₁ : Set G))
    (htheta : L₁ = closure {x : G | x ∈ H ⊓ M ∧ orderOf x = 3})
    (h13 : ∀ J : Subgroup G, L₁ ⊔ T ≤ J → J ≤ G₁ → Group.IsSolvable J → J ≤ M)
    (hUH : H ≤ normalizer (Source.UH H V₃ : Set G))
    (ρ : Representation (ZMod 2) (Source.Hstar H) (Additive (Source.Utilde H V₃ V₁)))
    (_hρ : Function.Injective ρ)
    (_hact : ∀ h : H, ∀ u : Source.UH H V₃,
      ρ (QuotientGroup.mk' (pCore 2 H) h)
        (Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃)) u)) =
      Additive.ofMul (QuotientGroup.mk' (V₁.subgroupOf (Source.UH H V₃))
        ⟨(h : G) * (u : G) * (h : G)⁻¹,
          (mem_normalizer_iff.mp (hUH h.property) u).mp u.property⟩))
    (h5 : ∀ a : Source.Hstar H, a ≠ 1 → fixedCodim ρ (zpowers a) = 1 →
      TransvectionModels ρ L)
    (hcover : SolvableExclusion.IsTripleCoverSix (L ⧸ pCore 2 L) →
      Nonempty ((L₁ ⧸ pCore 2 L₁) ≃* Multiplicative (Fin 2 → ZMod 3)))
    (hUβVβ : Uβ ≤ Vβ) (hVβH : Vβ ≤ H) (hVγH : Vγ ≤ H)
    [IsElementaryAbelian 2 Uβ] [IsElementaryAbelian 2 Vγ]
    (b : G) (hUβ : Uβ = Uγ.map (MulAut.conj b).toMonoidHom)
    (hVβ : Vβ = Vγ.map (MulAut.conj b).toMonoidHom)
    (hF : ∀ V : Subgroup G, V = Vβ ∨ V = Vγ →
      ∃ y : H, V.map (MulAut.conj (y : G)).toMonoidHom ≤ (L₁ ⊔ T).pCoreIn 2)
    (h8 : (∃ a ∈ Source.starImage H Uβ, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) ∨
      (∃ a ∈ Source.starImage H Vγ, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) ∨
      SecondCase H L₁ T (Source.UH H V₃) Uγ Vγ A₁ V₁ ρ) :
    ∃ φ : Source.Hstar H →* S7, Function.Injective φ ∧
      (Source.starImage H K).map φ = alternatingGroup (Fin 7) ∧
      (∃ σ : S7, ∀ k : K,
        φ (QuotientGroup.mk' (pCore 2 H) ⟨k, hKH k.property⟩) =
          (MulAut.conj σ) (eK (QuotientGroup.mk' (pCore 2 K) k)).val) ∧
      (Source.starImage H (L₁ ⊔ T) = fourThreeStabilizer.comap φ ∨
        Source.starImage H (L₁ ⊔ T) = pairStabilizer.comap φ) ∧
      {y : Fin 7 | ∃ s ∈ Source.starImage H T, φ s 0 = y} = {0, 1, 2, 3} ∧
      {y : Fin 7 | ∃ s ∈ Source.starImage H T, φ s 4 = y} = {4, 5} ∧
      {y : Fin 7 | ∃ s ∈ Source.starImage H T, φ s 6 = y} = {6} ∧
      SecondCase H L₁ T (Source.UH H V₃) Uγ Vγ A₁ V₁ ρ ∧
      Uβ = Uγ.map (MulAut.conj b).toMonoidHom ∧
      Vβ = Vγ.map (MulAut.conj b).toMonoidHom ∧
      (∀ V : Subgroup G, V = Vβ ∨ V = Vγ → ∃ y : H,
        (Source.starImage H V).map
          (MulAut.conj (QuotientGroup.mk' (pCore 2 H) y)).toMonoidHom ≤
          (Source.starImage H (L₁ ⊔ T)).pCoreIn 2) ∧
      ∃ h : H,
        Source.starImage H (Vγ.map (MulAut.conj (h : G)).toMonoidHom) =
          (Source.starImage H Vγ).map
            (MulAut.conj (QuotientGroup.mk' (pCore 2 H) h)).toMonoidHom ∧
        Source.starImage H (Vγ.map (MulAut.conj (h : G)).toMonoidHom) ≤
          (Source.starImage H (L₁ ⊔ T)).pCoreIn 2 := by
  let : Group.IsSolvable (L₁ ⊔ T : Subgroup G) := base_solvable L₁ T hT hTN
  have hbase : L₁ ⊔ T ≤ H := hH.1.2
  obtain ⟨φ, hi, hAlt, hrep⟩ := source_action_exists H K T hKH
    (le_sup_right.trans hbase) hK hKn hT h21 eK
  have ha : alternatingGroup (Fin 7) ≤ φ.range := by
    rw [← hAlt]
    exact map_le_range φ (Source.starImage H K)
  have hnβ : ¬ (∃ a ∈ Source.starImage H Uβ, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) :=
    fun ht => exclude_first_case_actor H L L₁ T G₁ M Uβ Vβ hbase hH.2.1 htheta h13
      S hS ρ φ hi ha h5 hcover hVβH hUβVβ (hF Vβ (Or.inl rfl)) ht
  have hnγ : ¬ (∃ a ∈ Source.starImage H Vγ, a ≠ 1 ∧ fixedCodim ρ (zpowers a) = 1) :=
    fun ht => exclude_first_case_actor H L L₁ T G₁ M Vγ Vγ hbase hH.2.1 htheta h13
      S hS ρ φ hi ha h5 hcover hVγH le_rfl (hF Vγ (Or.inr rfl)) ht
  have hcase : SecondCase H L₁ T (Source.UH H V₃) Uγ Vγ A₁ V₁ ρ :=
    h8.elim (fun h => (hnβ h).elim) (fun h => h.elim (fun h => (hnγ h).elim) id)
  obtain ⟨σ, hp, h0, h4, h6⟩ := source_partition_dichotomy H L₁ T G₁ M hbase hH.2.1
    htheta h13 φ hi ha S hS
  refine ⟨(MulAut.conj σ).toMonoidHom.comp φ, (MulAut.conj σ).injective.comp hi,
    alternating_image_conjugate φ _ hAlt σ,
    ⟨σ, fun k => congrArg (MulAut.conj σ) (hrep k)⟩,
    hp, h0, h4, h6, hcase, hUβ, hVβ, ?_, ?_⟩
  · intro V hv
    obtain ⟨y, hy⟩ := hF V hv
    exact ⟨y, star_conjugate_le_twoCore H (L₁ ⊔ T) V hbase
      (hv.elim (fun h => h.symm ▸ hVβH) (fun h => h.symm ▸ hVγH)) y hy⟩
  · obtain ⟨h, hh⟩ := hcase.2.2.2.2.2.2.2
    refine ⟨h, starImage_conjugate H Vγ hVγH h, ?_⟩
    rw [starImage_conjugate H Vγ hVγH h]
    exact star_conjugate_le_twoCore H (L₁ ⊔ T) Vγ hbase hVγH h hh

end CFSG.Quasithin.Chapter13.Section08.ComponentSieve.Seven.LocalGeometry
