module

public import Theory.Representation.OrthogonalFourMinusRankOne.HermitianQuinticSylowQuotientNoConflict
public import CFSG.Quasithin.Chapter6.SourceReduction.RankOneModuleNaturalFixedQuotientTitsQuinticKernel

/-!
# The original quintic actor fixes the small Hermitian image

The same full module has image of order at most32 in KT/O₂(KT). A moving
quotient for its actual quintic subgroup and original inner Sylow would
have at least64 elements. Thus every original quintic torus displacement
lies in the full O₂(KT), without changing either acting group or kernel.

Source: Aschbacher--Smith6.1.4, printed pp.665--666.
-/

set_option backward.isDefEq.respectTransparency false
public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher Representation
attribute [local instance] SL2.BinarySmall.spaceBinaryModule
namespace CFSG.Quasithin.Chapter6.Source.RankOneRecognition
open RankOneGeneric
open OrthogonalFourMinus.FiniteModel OrthogonalFourMinus.RankOne Matrix.SpecialLinearGroup
open Representation.OrthogonalFourMinus.RankOne.QuinticAdapter
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V M₁ K D : Subgroup G} {n : ℕ}

/-- Every element of the actual order-five torus fixes the original full
Hermitian module modulo the whole two-core of KT. -/
theorem original_hermitian_tits_quintic_torus_centralizes_mod_core
    (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
    (hout : Chapter3.HasMaximalOutside T M)
    (hm : IsConjugationModel L (reducedSubgroup (L ⊔ (T : Subgroup G)))
      (SL2.BinarySmall.hermitian 2))
    (hM₁ : IsMaximalTwoLocal M₁) (hCM₁ : omegaCentralizer T ≤ M₁)
    (hK : K ∈ Chapter1.cComponentsIn M₁) (hnot : ¬ K ≤ M)
    (hqK : IsQuasisimple (K ⧸ pCore 2 K))
    (e : coreCentralQuotient K ≃* Tits.ParrottGroup)
    (hD : Nat.card D = 5) (hDB : D ≤ localBorel T L)
    (hDX : D ≤ quinticResidual T L) :
    ⁅D,reducedSubgroup (L ⊔ (T : Subgroup G))⁆ ≤ (K ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let B := reducedSubgroup (L ⊔ (T : Subgroup G))
  let J := K ⊔ (T : Subgroup G)
  obtain ⟨q,f,W,hq,hker,hf,hS,hmem,hcard,hinv⟩ :=
    original_hermitian_tits_kernel_coordinates h hout hm hM₁ hCM₁ hK hnot hqK e
  let A := D.subgroupOf L
  let Dq := A.map q
  let P := upperUnipotentSylow (Field 2) 2
  have hDL : D ≤ L := hDB.trans inf_le_left
  have hDJ : D ≤ J := hDX.trans
    ((original_hermitian_quintic_le_tits_component h hout hm hM₁ hCM₁ hK hnot hqK e).trans le_sup_left)
  have hAc : Nat.card A = 5 := (Nat.card_congr (subgroupOfEquivOfLe hDL).toEquiv).trans hD
  have hdis : Disjoint A q.ker := by
    rw [hker]
    obtain ⟨k,hk⟩ := (pCore_isPGroup (p := 2) (G := L)).exists_card_eq
    apply disjoint_of_coprime_natCard
    rw [hAc,hk]
    exact (by decide : Nat.Coprime 5 2).pow_right k
  have hqi : Function.Injective (q.subgroupMap A) := by
    apply (injective_iff_map_eq_one _).mpr
    intro a ha
    apply Subtype.ext
    exact disjoint_def.mp hdis a.property (congrArg Subtype.val ha)
  have hDqc : Nat.card Dq = 5 :=
    (Nat.card_congr (MulEquiv.ofBijective (q.subgroupMap A)
      ⟨hqi,q.subgroupMap_surjective A⟩).toEquiv).symm.trans hAc
  have hAN : A ≤ normalizer (((T : Subgroup G).subgroupOf L : Subgroup L) : Set L) := by
    have hdb' : D ≤ (normalizer (((T : Subgroup G).subgroupOf L : Subgroup L) : Set L)).map L.subtype := by
      rw [← localBorel_eq_map]
      exact hDB
    have hmap : A.map L.subtype ≤
        (normalizer (((T : Subgroup G).subgroupOf L : Subgroup L) : Set L)).map L.subtype := by
      rw [map_subgroupOf_eq_of_le hDL]
      exact hdb'
    exact (Subgroup.map_le_map_iff_of_injective L.subtype_injective).mp hmap
  have hDN : Dq ≤ normalizer (P : Set (Matrix.SpecialLinearGroup (Fin 2) (Field 2))) := by
    change Dq ≤ normalizer (upperUnipotent (Field 2) : Set _)
    rw [←hS]
    exact (map_mono hAN).trans (le_normalizer_map q)
  have hPW : ∀ p ∈ P, ∀ x ∈ W, SL2.BinarySmall.hermitian 2 p x ∈ W := by
    intro p hp x hx
    have hp' : p ∈ ((T : Subgroup G).subgroupOf L).map q := hS.symm ▸ hp
    obtain ⟨l,hl,rfl⟩ := hp'
    exact hinv l ((le_sup_right : (T : Subgroup G) ≤ J) hl) x hx
  have hDW : ∀ d ∈ Dq, ∀ x ∈ W, SL2.BinarySmall.hermitian 2 d x ∈ W := by
    rintro d ⟨l,hl,rfl⟩ x hx
    exact hinv l (hDJ hl) x hx
  have hfix := quintic_fixes_quotient_of_card_le_thirtyTwo P Dq hDN hDqc W hPW hDW hcard
  apply commutator_le.mpr
  intro d hd b hb
  let dl : L := ⟨d,hDL hd⟩
  let bv : B := ⟨b,hb⟩
  let db : B := B.normalizerMonoidHom ⟨d,hm.normalizes (hDL hd)⟩ bv
  have he := hfix (q dl) (mem_map_of_mem q (show dl ∈ A from hd)) (f bv).toAdd
  rw [←hf dl bv] at he
  have hv : (f (db*bv⁻¹)).toAdd ∈ W := by
    simpa only [map_mul,map_inv,toAdd_mul,toAdd_inv,sub_eq_add_neg] using he
  have hh := (hmem (db*bv⁻¹)).mp hv
  exact hh

end CFSG.Quasithin.Chapter6.Source.RankOneRecognition
