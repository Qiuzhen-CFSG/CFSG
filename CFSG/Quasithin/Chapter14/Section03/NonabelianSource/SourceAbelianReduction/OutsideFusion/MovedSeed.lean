module
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.Defs
public import CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction.OutsideFusion.FactorExchange
public import CFSG.Quasithin.ChapterG.Section09.FittingRecognition.Four.NormalSylowResidual
public import Theory.GroupTheory.UniqueInvolutionDihedralKernel
public import Theory.GroupTheory.WreathTwoSylowModel

/-!
# Core return from the moved-seed centralizer count

Exchange of the original elementary factors puts all involutions of C_R(t)
in V. Since t moves V and fixes its marked point, that point is the unique
involution of C_R(t). If this centralizer has order eight, its map to H^y/Q^y
kills the point: an injective image would be a full dihedral Sylow subgroup,
which has distinct involutions. The literal map is conjugation back into H
followed by the original terminal quotient, whose kernel is O₂(H).

The order-eight centralizer calculation remains explicit in the final theorem.
Source: Aschbacher--Smith 14.3.21(2), printed p.998.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
open Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section02 SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Recognition
variable {G : Type*} [Group G] [Finite G]

/-- An element of T moving the seed fixes exactly its marked point. -/
theorem seed_centralizer_eq_point_of_movement
    {T : Sylow 2 G} {V : Subgroup G} (F : InvariantFlag T V 2)
    (t : G) (htT : t ∈ (T : Subgroup G)) (htV : t ∉ centralizer (V : Set G)) :
    V ⊓ centralizer ({t} : Set G) = F.Vi 1 := by
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hv : Nat.card V = 4 := by simpa only [F.last,show (2 : ℕ)^2 = 4 from rfl] using F.card 2 le_rfl
  have htc : t ∈ centralizer (F.Vi 1 : Set G) :=
    normalizer_le_centralizer_of_card_two (F.Vi 1) hp (F.invariant 1 htT)
  have hle : F.Vi 1 ≤ V ⊓ centralizer ({t} : Set G) := by
    refine le_inf (F.le_seed 1) ?_
    intro x hx
    exact mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp htc x hx)
  have hproper : V ⊓ centralizer ({t} : Set G) ≠ V := by
    intro he
    apply htV
    intro x hx
    have hx' : x ∈ centralizer ({t} : Set G) := (he.symm ▸ hx).2
    exact mem_centralizer_singleton_iff.mp hx'
  have hd : Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G) ∣ 4 :=
    hv ▸ card_dvd_of_le (show V ⊓ centralizer ({t} : Set G) ≤ V from inf_le_left)
  have hsmall : Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G) < 4 := by
    have hle4 := Nat.le_of_dvd (by decide : 0 < 4) hd
    have hne4 : Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G) ≠ 4 := by
      intro hc
      exact hproper (eq_of_le_of_card_ge inf_le_left (by rw [hv,hc]))
    omega
  have hlarge : 2 ≤ Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G) := by
    rw [← hp]
    exact Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)
  have hc : Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G) = 2 := by
    interval_cases hh : Nat.card (V ⊓ centralizer ({t} : Set G) : Subgroup G) <;> omega
  exact (eq_of_le_of_card_ge hle (by rw [hp,hc])).symm

variable
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hnot : ¬ ClassificationModels.IsTheoremEModel G)
    (F : InvariantFlag T (rankTwoSeed T M) 2)
    [IsElementaryAbelian 2 (rankTwoSeed T M)]
    (hne : ¬ IsMulCommutative F.U)
    (g : G) (hgP : g ∈ F.P (sourceResidual M Mc)) (hgH : g ∉ F.H)
    (hs : Group.IsSolvable F.TerminalHdot)
include hG hempty hM hu hmany hcard e hnot hne hgP hgH hs

/-- In the moved-seed case the marked point is the unique involution of C_R(t). -/
theorem source_moved_centralizer_unique_involution
    (z : G) (hz : z ∈ F.Vi 1) (hzne : z ≠ 1)
    (t : G) (htT : t ∈ (T : Subgroup G))
    (htout : t ∉ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2)
    (htV : t ∉ centralizer (rankTwoSeed T M : Set G)) :
    z ∈ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({t} : Set G) ∧
    ∀ x ∈ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({t} : Set G),
      orderOf x = 2 → x = z := by
  obtain ⟨_,A,B,hAR,_,hVA,_,_,_,_,_,_,_,_,_,_,_,_,hfix⟩ :=
    source_outside_factor_exchange_of_solvable
      hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs t htT htout
  have he := seed_centralizer_eq_point_of_movement F t htT htV
  have hzc := he.ge hz
  refine ⟨⟨hAR (hVA (F.le_seed 1 hz)),hzc.2⟩,?_⟩
  intro x hx hx2
  have hxV := hfix x hx.1 (by rw [← hx2]; exact pow_orderOf_eq_one x)
    (mem_centralizer_singleton_iff.mp hx.2)
  have hxP : x ∈ F.Vi 1 := he.le ⟨hxV,hx.2⟩
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  obtain ⟨a,_,ha⟩ := (Nat.card_eq_two_iff' (1 : F.Vi 1)).mp hp
  have hxne : (⟨x,hxP⟩ : F.Vi 1) ≠ 1 := fun h =>
    (orderOf_eq_prime_iff.mp hx2).2 (congrArg Subtype.val h)
  have hzne' : (⟨z,hz⟩ : F.Vi 1) ≠ 1 := fun h => hzne (congrArg Subtype.val h)
  exact congrArg Subtype.val ((ha _ hxne).trans (ha _ hzne').symm)

/-- The literal centralizer-to-terminal-quotient argument, conditional only on
the order-eight centralizer count. No quaternion model or fusion premise is used. -/
theorem source_moved_core_return_of_card_eight
    (z : G) (hz : z ∈ F.Vi 1) (hzne : z ≠ 1)
    (t : G) (htT : t ∈ (T : Subgroup G))
    (htout : t ∉ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2)
    (htV : t ∉ centralizer (rankTwoSeed T M : Set G))
    (hc : Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓
      centralizer ({t} : Set G) : Subgroup G) = 8)
    (y : G) (hy : y⁻¹ * z * y = t) : z ∈ conjugate (F.H.pCoreIn 2) y := by
  let h := source_lemma_14_2_4 hG T hempty hM hu hmany hcard e
  obtain ⟨dg,he,_,_,_,_,_⟩ := rankTwo_terminal_hypothesis h F hne g hgP hgH
  let := he
  have hZ := source_center_eq_point_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  have hr := source_full_orthogonal_of_solvable hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
  obtain ⟨hzC,hunique⟩ := source_moved_centralizer_unique_involution
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs z hz hzne t htT htout htV
  let C := (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓ centralizer ({t} : Set G)
  have hp : Nat.card (F.Vi 1) = 2 := by simpa using F.card 1 (by decide)
  have hz2 : orderOf z = 2 := orderOf_eq_prime
    (congrArg Subtype.val (show (⟨z,hz⟩ : F.Vi 1)^2 = 1 from by
      simpa only [hp] using pow_card_eq_one' (x := (⟨z,hz⟩ : F.Vi 1)))) hzne
  have hzp : zpowers z = F.Vi 1 := eq_of_le_of_card_ge (zpowers_le.mpr hz)
    (by rw [Nat.card_zpowers,hz2,hp])
  have hH : F.H = centralizer ({z} : Set G) := by
    change normalizer (F.Vi 1 : Set G) = _
    rw [← hzp]
    exact normalizer_zpowers_eq_centralizer_of_order_two z hz2
  let a := MulAut.conj y
  have hat : a t = z := by
    change y * t * y⁻¹ = z
    rw [← hy]
    group
  let c : C →* F.H := (a.toMonoidHom.comp C.subtype).codRestrict F.H (by
    intro x
    rw [hH]
    apply mem_centralizer_singleton_iff.mpr
    have hh := (show Commute (x : G) t from mem_centralizer_singleton_iff.mp x.property.2).map a.toMonoidHom
    exact hat ▸ hh.eq)
  let q := QuotientGroup.mk' F.terminalHatAction.ker
  let f : C →* F.TerminalHdot := q.comp c
  obtain ⟨j⟩ := ChapterG.Section09.FittingRecognition.Four.full_orthogonal_group_equiv F.terminalRepresentation hr
  let P : Sylow 2 F.TerminalHdot := default
  obtain ⟨eP⟩ := wreath_two_sylow_mulEquiv_dihedral_four
    (P.mapSurjective (f := j.toMonoidHom) j.surjective)
  have hfz : f ⟨z,hzC⟩ = 1 := involution_killed_of_dihedral_sylow hc
    (⟨z,hzC⟩ : C)
    (fun x hx => Subtype.ext (hunique x x.property ((Subgroup.orderOf_coe x).trans hx)))
    P ((j.subgroupMap (P : Subgroup F.TerminalHdot)).trans eP) f
  have hk : q.ker = pCore 2 F.H := by
    rw [QuotientGroup.ker_mk',terminal_kernel_of_center_point F dg hZ]
  have hmem : c ⟨z,hzC⟩ ∈ pCore 2 F.H := hk ▸ (show c ⟨z,hzC⟩ ∈ q.ker from hfz)
  have haQ : a z ∈ F.H.pCoreIn 2 := mem_map_of_mem F.H.subtype hmem
  refine ⟨a z,haQ,?_⟩
  change y⁻¹ * (y * z * y⁻¹) * (y⁻¹)⁻¹ = z
  group

/-- The moved core-return interface from the sole remaining fixed-order input. -/
theorem source_moved_seed_core_return_of_centralizer_card
    (hcount : ∀ t ∈ (T : Subgroup G), orderOf t = 2 →
      t ∉ (F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊔ F.H.pCoreIn 2 →
      t ∉ centralizer (rankTwoSeed T M : Set G) →
      Nat.card ((F.I₂ (sourceResidual M Mc)).pCoreIn 2 ⊓
        centralizer ({t} : Set G) : Subgroup G) = 8) :
    MovedSeedCoreReturn F (sourceResidual M Mc) := by
  intro z hz hzne t ht ht2 htout htV y hy
  exact source_moved_core_return_of_card_eight
    hG T hempty hM hu hmany hcard e hnot F hne g hgP hgH hs
    z hz hzne t ht htout htV (hcount t ht ht2 htout htV) y hy

end CFSG.Quasithin.Chapter14.Section03.NonabelianSource.SourceAbelianReduction
