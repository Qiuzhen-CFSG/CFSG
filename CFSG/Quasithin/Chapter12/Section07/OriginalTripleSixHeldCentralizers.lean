module

public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointCommutator
public import CFSG.Quasithin.Chapter12.Section07.OriginalTripleSixPointComponent
public import CFSG.Quasithin.Chapter12.Section07.HeldIdentification.Centralizers
public import Theory.SpecificGroups.PSL3Four.FieldExtension.Basic
import Theory.SpecificGroups.PSL3.SylowFixedSolvable
import Theory.GroupAction.PerfectCentralQuotient
import Theory.GroupTheory.ConjugateSpanSylow
import Theory.ElementaryAbelian.EightQuotientRank

/-!
# The original point residual has trivial automorphism fixer in its Held component

The actual U has order64 and is normal in Lt, whose two-core quotient is A5.
Thus 256 divides |Lt|. The original central kernel Vt has order4, so the
projection of Lt contains a full Sylow2 of PSL3(4). A nonidentity automorphism
fixing that Sylow has solvable fixed subgroup, whereas the projected Lt is
nontrivial and perfect. Faithful descent through the perfect central quotient
then gives the full pointwise fixer calculation on B=<Lt^C_G(t)>.

Source: Aschbacher--Smith, 12.7.7, printed p.841. These are the actual
pointwise-fixer and seed-centralizer deductions; the subsequent original
scalar-centralizer and Frattini calculations are separate source duties.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter12.Section07
open Section02 ChapterB.QuasisimpleSource
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {K U : Subgroup G}

private theorem pslThreeFour_fixer_of_perfect_sylow_card
    (A : Subgroup Matrix.PSL3Four.PSL) [Group.IsPerfect A]
    (hcard : 64 ∣ Nat.card A) (b : MulAut Matrix.PSL3Four.PSL)
    (hfix : A ≤ b.fixedSubgroup) : b = 1 := by
  obtain ⟨P,hP⟩ := Sylow.exists_subgroup_card_pow_prime (p := 2) (n := 6) hcard
  let Pm := P.map A.subtype
  have hPm : Nat.card Pm = 64 := by
    rw [card_map_of_injective A.subtype_injective]
    exact hP
  have hidx : Pm.index = 315 := by
    have hh := Pm.card_mul_index
    rw [hPm, Matrix.PSL3Four.card_PSL] at hh
    omega
  let S : Sylow 2 Matrix.PSL3Four.PSL :=
    (IsPGroup.of_card (p := 2) (n := 6) hPm).toSylow (by rw [hidx]; decide)
  have hSA : (S : Subgroup Matrix.PSL3Four.PSL) ≤ A := map_subtype_le _
  by_contra hb
  let := Matrix.PSL3.LinearThree.sylow_fixed_solvable Matrix.PSL3Four.F
    (n := 2) (by decide) (by simpa using Matrix.PSL3Four.card_F) S b hb
    (fun x hx => (MulAut.mem_fixedSubgroup b x).mp (hfix (hSA hx)))
  let : Group.IsSolvable A :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hfix)
  let : Nontrivial A := Finite.one_lt_card_iff_nontrivial.mp
    (lt_of_lt_of_le (by decide : 1 < 64) (Nat.le_of_dvd Nat.card_pos hcard))
  exact Group.IsPerfect.not_isSolvable A inferInstance

/-- The literal projection of Lt contains a full Sylow2 of the actual
PSL3(4) quotient: its order is divisible by64. -/
theorem original_tripleSix_held_projected_residual_card
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
    64 ∣ Nat.card ((Lt.subgroupOf B).map
      (e.toMonoidHom.comp (QuotientGroup.mk' (center B)))) := by
  let C := K ⊓ centralizer ({(t : G)} : Set G)
  let Lt := (pResidual 2 C).map C.subtype
  let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
  let A := Lt.subgroupOf B
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hUL : U ≤ Lt := (tripleSixPointCentralizerResidual_commutator D a t ht heven).2
  have hLK : Lt ≤ K := (map_subtype_le _).trans inf_le_left
  have hLB : Lt ≤ B := le_conjugateSpanBy _ _
  have hU64 : Nat.card U = 64 :=
    (Nat.card_congr (tripleSixPointCoordinates D a).toEquiv).trans Atlas.Codes.hexacode_card
  let := D.elementary
  have hUcore : U ≤ Lt.pCoreIn 2 := le_pCoreIn_of_normalizes
    (IsElementaryAbelian.isPGroup 2 U) hUL (hLK.trans D.normalizes)
  have hc64 : 64 ∣ Nat.card (pCore 2 Lt) := by
    have hd := card_dvd_of_le hUcore
    rwa [hU64, pCoreIn, card_map_of_injective Lt.subtype_injective] at hd
  have hquot : Nat.card (Lt ⧸ pCore 2 Lt) = 60 := by
    rw [Nat.card_congr (tripleSixPointResidualQuotientEquiv D a t ht heven).toEquiv,
      nat_card_alternatingGroup]
    norm_num
  have hLt256 : 256 ∣ Nat.card Lt := by
    have hh := (pCore 2 Lt).card_mul_index
    change Nat.card (pCore 2 Lt) * Nat.card (Lt ⧸ pCore 2 Lt) = Nat.card Lt at hh
    rw [hquot] at hh
    rw [←hh]
    exact Nat.mul_dvd_mul hc64 (by decide : 4 ∣ 60)
  have hZ4 : Nat.card (center B) = 4 := by
    have hv := (tripleSixPoint_properties D a t ht).2.2.1
    rw [←hcenter] at hv
    change Nat.card (centerIn B) = 4 at hv
    simpa only [centerIn_eq_map_center, card_map_of_injective B.subtype_injective] using hv
  have hZA : center B ≤ A := by
    intro z hz
    have hv : (z : G) ∈ tripleSixPoint D a t := by
      rw [←hcenter,centerIn_eq_map_center]
      exact mem_map_of_mem B.subtype hz
    exact hUL ((tripleSixPoint_properties D a t ht).2.1 hv)
  have hker : q.ker = center B := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hh := IsElementaryAbelian.card_inf_ker_mul_card_map A q
  rw [hker, inf_eq_right.mpr hZA, hZ4,
    Nat.card_congr (subgroupOfEquivOfLe hLB).toEquiv] at hh
  change 64 ∣ Nat.card (A.map q)
  apply (Nat.mul_dvd_mul_iff_left (by decide : 0 < 4)).mp
  rw [hh]
  exact hLt256

/-- Every automorphism of the original normal closure fixing the original
point residual pointwise is the identity. No involution restriction is needed. -/
theorem original_tripleSix_held_residual_fixer
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
    ∀ b : MulAut B, (∀ l : B, (l : G) ∈ Lt → b l = l) → b = 1 := by
  let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
    (K ⊓ centralizer ({(t : G)} : Set G)).subtype
  let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
  let A := Lt.subgroupOf B
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  let : Group.IsPerfect Lt := tripleSixPointCentralizerResidual_perfect D a t ht heven
  let : Group.IsPerfect B := conjugateSpanBy_isPerfect _ _
  let eA : A ≃* Lt := subgroupOfEquivOfLe (le_conjugateSpanBy Lt _)
  let : Group.IsPerfect A := Group.IsPerfect.ofSurjective
    (f := eA.symm.toMonoidHom) eA.symm.surjective
  let : Group.IsPerfect (A.map q) := Group.IsPerfect.map q
  change ∀ b : MulAut B, (∀ l : B, (l : G) ∈ Lt → b l = l) → b = 1
  intro b hb
  apply MulAut.centralQuotientAction_injective e
  rw [map_one]
  apply pslThreeFour_fixer_of_perfect_sylow_card (A.map q)
    (original_tripleSix_held_projected_residual_card D a t ht heven hcenter e)
  rintro x ⟨l,hl,rfl⟩
  apply (MulAut.mem_fixedSubgroup _ _).mpr
  change MulAut.centralQuotientAction e b (e (QuotientGroup.mk' (center B) l)) = _
  rw [MulAut.centralQuotientAction_apply, hb l hl]
  rfl

/-- Centralizing the actual Lt is equivalent to centralizing its entire
normal closure inside the original point centralizer. -/
theorem original_tripleSix_held_seed_centralizer
    (D : ChosenModule T K U)
    (a : ActionEquiv D.quotientAction Hexacode.evenAction) (t : U) (ht : t ≠ 1)
    (heven : 2 ∣ (centralizer ({(t : G)} : Set G)).relIndex K)
    (hcenter :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      centerIn (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))) = tripleSixPoint D a t)
    (e :
      let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
        (K ⊓ centralizer ({(t : G)} : Set G)).subtype
      let B := conjugateSpanBy Lt (centralizer ({(t : G)} : Set G))
      B ⧸ center B ≃* Matrix.PSL3Four.PSL) :
    let Lt := (pResidual 2 (K ⊓ centralizer ({(t : G)} : Set G) : Subgroup G)).map
      (K ⊓ centralizer ({(t : G)} : Set G)).subtype
    centralizer (Lt : Set G) = centralizer ({(t : G)} : Set G) ⊓
      centralizer (conjugateSpanBy Lt (centralizer ({(t : G)} : Set G)) : Set G) := by
  apply HeldIdentification.centralizer_seed_eq
  · exact (tripleSixPointCentralizerResidual_commutator D a t ht heven).2 t.property
  · exact le_conjugateSpanBy _ _
  · exact le_normalizer_conjugateSpanBy _ _
  · exact original_tripleSix_held_residual_fixer D a t ht heven hcenter e

end CFSG.Quasithin.Chapter12.Section07
