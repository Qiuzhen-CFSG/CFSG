module
public import CFSG.Quasithin.ChapterA.Section01.RankActions.LargeElementary
public import Theory.SpecificGroups.OddThreeSectionRank
public import Theory.Mathieu.TwoRankLower
public import Theory.GroupTheory.PerfectSimpleImage
public import Theory.GroupTheory.PerfectOddIndexNormalizer
public import CFSG.Quasithin.ChapterI.Section03.Balance
public import Theory.GroupAction.PerfectCentralQuotient


/-!
# Mathieu covers centralize small odd cores

A section of odd GL₂ has two-rank at most three, whereas M₂₂ has an actual
rank-four elementary subgroup. Hence every action of a full quasisimple
M₂₂ cover on an odd prime-group of rank at most two is trivial: the
small-rank automorphism representation has prime-group kernel.

In a quasithin ambient group, an elementary sixteen bounds each odd prime
core by A.1.28. The preceding obstruction centralizes those cores. A.1.9
then centralizes the odd core for a Sylow two-subgroup of the cover, and
perfectness with the odd-order theorem gives centralization by the full
cover. Its odd-E orbit is consequently an ordinary component whenever it
is a two-component. A proper ordinary overcomponent supplies a nontrivial
involution on its literal central quotient.

The consumer is the unchanged exterior cubic residual in 4.2.13, p.612.
Source: Aschbacher--Smith A.1.9, A.1.25 and A.1.28, pp.21,25--26;
I.3.2, p.415. No equality with the containing component is asserted.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterI.MathieuPumpup

/-- The native M₂₂ group is not a section of odd-prime GL₂. -/
theorem no_mathieu_gl2_section {p : ℕ} [Fact p.Prime] (hp : Odd p)
    (U : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod p)))
    (f : U →* Sporadic.Mathieu.M22) (hf : Function.Surjective f) : False := by
  let S : Sylow 2 U := Classical.choice inferInstance
  let j := U.subtype.comp (S : Subgroup U).subtype
  let P := S.mapSurjective hf
  have hr := Theory.SpecificGroups.OddThreeSectionRank.gl2_twoGroup_image_twoRank_le_three
    (F := ZMod p) (show GorensteinWalter.IsOddPrimePower (Nat.card (ZMod p)) from
      ⟨p,1,Fact.out,hp,by decide,by simp⟩)
    (Field.two_ne_zero_of_odd_card (ZMod p) (by simpa using hp))
    S.isPGroup' j (U.subtype_injective.comp (S : Subgroup U).subtype_injective)
    (f.subgroupMap (S : Subgroup U)) (f.subgroupMap_surjective _)
  change primeRank 2 P ≤ 3 at hr
  have hl := Sporadic.Mathieu.m22_four_le_twoRank
  rw [P.primeRank_eq] at hl
  omega

/-- Every small-rank odd prime-group action of the full cover is trivial. -/
theorem mathieu_cover_small_odd_action
    {B P : Type*} [Group B] [Finite B] [IsQuasisimple B] [Group P] [Finite P]
    (e : (B ⧸ center B) ≃* Sporadic.Mathieu.M22)
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (hP : IsPGroup p P)
    (hr : primeRank p P ≤ 2) (a : B →* MulAut P) : a = 1 := by
  obtain ⟨f,hf⟩ := ChapterA.RankActions.smallRankAutomorphismRepresentation p hp P hP hr
  let q := e.toMonoidHom.comp (QuotientGroup.mk' (center B))
  have hk : q.ker = center B :=
    (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  let : Group.IsSolvable q.ker := by
    rw [hk]
    exact Group.isSolvable_of_comm (fun a b => Subtype.ext (mem_center_iff.mp a.property b).symm)
  let : IsSimpleGroup (B ⧸ center B) := IsQuasisimple.simple
  let : IsSimpleGroup Sporadic.Mathieu.M22 := e.symm.isSimpleGroup
  have hfa : f.comp a = 1 := hom_eq_one_of_no_simple_section q
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (no_mathieu_gl2_section hp) _
  have hle : a.range ≤ f.ker := by
    rintro _ ⟨b,rfl⟩
    exact DFunLike.congr_fun hfa b
  let : Group.IsNilpotent a.range := (hf.to_le hle).isNilpotent
  let : Group.IsPerfect a.range := Group.IsPerfect.range a
  have hs : Subsingleton a.range := by
    by_contra! hnt
    exact Group.IsPerfect.not_isSolvable a.range inferInstance
  apply MonoidHom.ext
  intro b
  exact congrArg Subtype.val (hs.elim (a.rangeRestrict b) 1)

/-- A Mathieu cover centralizes the ambient odd core in the presence of an elementary sixteen. -/
theorem mathieu_cover_centralizes_oddCore
    {X : Type*} [Group X] [Finite X] (hX : IsQuasithin X)
    (V : Subgroup X) [IsElementaryAbelian 2 V] (hV : 8 < Nat.card V)
    (B : Subgroup X) [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* Sporadic.Mathieu.M22) :
    B ≤ centralizer (pPrimeCore 2 X : Set X) := by
  have hpcores (p : ℕ) [Fact p.Prime] (hp : Odd p) :
      B ≤ centralizer (pCore p X : Set X) := by
    have ha := mathieu_cover_small_odd_action e hp pCore_isPGroup
      (ChapterA.odd_core_rank_of_large_elementary hX V hV p hp)
      ((MulAut.conjNormal : X →* MulAut (pCore p X)).comp B.subtype)
    intro b hb
    rw [← MulAut.conjNormal_ker_eq_centralizer (pCore p X)]
    exact DFunLike.congr_fun ha ⟨b,hb⟩
  let S : Sylow 2 B := Classical.choice inferInstance
  let R := (S : Subgroup B).map B.subtype
  have hR : R ≤ centralizer (pPrimeCore 2 X : Set X) :=
    ChapterA.centralizes_oddCore_of_centralizes_odd_pCores R (S.isPGroup'.map B.subtype)
      (fun p _ hp => (map_subtype_le _).trans (hpcores p hp))
  apply perfect_le_of_normalizes_of_odd_relIndex B _ R le_normalizer_of_normal hR
  have he : R.subgroupOf B = (S : Subgroup B) := comap_map_eq_self_of_injective B.subtype_injective _
  rw [he]
  exact Nat.not_even_iff_odd.mp (fun hh => S.not_dvd_index hh.two_dvd)

/-- A large elementary subgroup makes the whole Mathieu odd-E orbit ordinary. -/
theorem mathieu_orbit_isComponent
    {X : Type*} [Group X] [Finite X] (hX : IsQuasithin X)
    (V : Subgroup X) [IsElementaryAbelian 2 V] (hV : 8 < Nat.card V)
    (B : Subgroup X) [IsQuasisimple B]
    (e : (B ⧸ center B) ≃* Sporadic.Mathieu.M22)
    (hE : (componentOrbit B (oddELayer X)).IsTwoComponent) :
    IsComponent X (componentOrbit B (oddELayer X)) := by
  apply hE.isComponent_of_centralizes_oddCore
  exact iSup_conjugates_le_of_le_normalizer B (oddELayer X) _
    (mathieu_cover_centralizes_oddCore hX V hV B e)
    (by rw [normalizer_eq_top]; exact le_top)

/-- A proper ordinary overcomponent has a genuine involution on its
central quotient. The trivial-action branch identifies the original seed. -/
theorem fixed_component_eq_or_involution
    {X : Type*} [Group X] [Finite X]
    (t : X) (ht : orderOf t = 2)
    (B : Subgroup (centralizer ({t} : Set X))) (hB : IsComponent _ B)
    (E : Subgroup X) (hE : IsComponent X E)
    (hBE : B.map (centralizer ({t} : Set X)).subtype ≤ E)
    (hinv : E.map (MulAut.conj t).toMonoidHom = E) :
    B.map (centralizer ({t} : Set X)).subtype = E ∨
      ∃ a : MulAut E, orderOf a = 2 ∧
        (∀ y : E, (a y : X) = t * (y : X) * t⁻¹) ∧
        orderOf (quotientAut (center E) a) = 2 := by
  classical
  let := hE.2
  by_cases he : B.map (centralizer ({t} : Set X)).subtype = E
  · exact Or.inl he
  right
  have hn : t ∈ normalizer (E : Set X) := mem_normalizer_iff_map_conj_eq.mpr hinv
  let tn : normalizer (E : Set X) := ⟨t,hn⟩
  let a := E.normalizerMonoidHom tn
  have ha (y : E) : (a y : X) = t * (y : X) * t⁻¹ := rfl
  have hapow : a ^ 2 = 1 := by
    have htpow : tn ^ 2 = 1 := Subtype.ext (by
      change t ^ 2 = 1
      simpa only [ht] using pow_orderOf_eq_one t)
    change E.normalizerMonoidHom tn ^ 2 = 1
    rw [←map_pow,htpow,map_one]
  have hane : a ≠ 1 := by
    intro h1
    have hEC : E ≤ centralizer ({t} : Set X) := by
      intro y hy
      have hy' : t * y * t⁻¹ = y := congrArg Subtype.val
        (DFunLike.congr_fun h1 (⟨y,hy⟩ : E))
      exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hy').symm
    have hBC : B ≤ E.subgroupOf (centralizer ({t} : Set X)) :=
      fun b hb => hBE (mem_map_of_mem _ hb)
    have heq := hB.eq_of_le (hE.subgroupOf hEC) hBC
    apply he
    have hm := congrArg (map (centralizer ({t} : Set X)).subtype) heq
    rwa [map_subgroupOf_eq_of_le hEC] at hm
  have hao : orderOf a = 2 := orderOf_eq_prime hapow hane
  exact ⟨a,hao,ha,(orderOf_injective (quotientAut (center E))
    MulAut.quotient_center_injective a).trans hao⟩

end CFSG.Quasithin.ChapterI.MathieuPumpup
