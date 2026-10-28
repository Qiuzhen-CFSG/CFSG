module

public import CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting.NormalizerAction
public import CFSG.Quasithin.ChapterA.Section01.RankActions.Supercritical
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.SolvableExclusion.Three.Noncontained.Extraspecial.Rank
public import Theory.GroupTheory.PGroup.SupercriticalExistence
public import Theory.ElementaryAbelian.ExtraspecialEquiv
public import Theory.ElementaryAbelian.Quotient
public import Theory.GroupTheory.PPerfectHom
public import Theory.Quasithin.Rank

/-!
# The supercritical and extraspecial steps of 13.5.20

A nontrivial two-action on O₃(H*) remains nontrivial on a supercritical
subgroup: its restriction kernel is a three-group. The A×B calculation
then forces the two-core of Y* to act nontrivially there.

A.1.25 applies after deriving nontriviality of O₃(H*) and its rank bound.
A cyclic subgroup of order three cannot admit this two-perfect Y* action.
In the extraspecial order-27 case the genuine cubic residual constructs
an elementary subgroup of order 27, contradicting m₃(H*) ≤ 2. Thus only a
normal elementary-nine subgroup remains. Its binary representation
obstruction and the faithful source action are separate remaining steps.

The cited extraspecial construction retains literal conjugation, constructs
the commuting inverter and cubic, and uses the Heisenberg fixed plane. No
rank-obstruction certificate is an input to the theorem below.
Source: Aschbacher–Smith, combined manuscript, 13.5.20, p.923 (PDF p.940).
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative
open CFSG.Quasithin.Chapter13.Section08.Source
namespace CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting
variable {G : Type*} [Group G] [Finite G]

private theorem supercritical_moved
    {Q : Type*} [Group Q] [Finite Q] (A : Subgroup Q) (hA : IsPGroup 2 A)
    (S : Subgroup Q) [S.Normal] (hS : IsPGroup 3 S)
    (X : Subgroup S) (hX : IsSupercriticalPSubgroup 3 X)
    (hm : ⁅S, A⁆ ≠ ⊥) : ⁅X.map S.subtype, A⁆ ≠ ⊥ := by
  let : X.Characteristic := hX.characteristic
  intro hz
  let a : Q →* MulAut S := MulAut.conjNormal
  have hc : X.map S.subtype ≤ centralizer (A : Set Q) :=
    commutator_eq_bot_iff_le_centralizer.mp hz
  have hle : A.map a ≤ (MulAut.characteristic X).ker := by
    rintro _ ⟨g, hg, rfl⟩
    apply MonoidHom.mem_ker.mpr
    ext x
    change g * ((x : S) : Q) * g⁻¹ = ((x : S) : Q)
    have hh := hc (mem_map.mpr ⟨x, x.property, rfl⟩) g hg
    change g * ((x : S) : Q) = ((x : S) : Q) * g at hh
    rw [hh, mul_inv_cancel_right]
  have hd := IsPGroup.disjoint_of_ne 2 3 (by decide) (A.map a)
    (MulAut.characteristic X).ker (hA.map a)
    (hX.isPGroup_restriction_kernel hS (by decide))
  have he : A.map a = ⊥ := disjoint_self.mp (hd.mono_right hle)
  apply hm
  apply commutator_eq_bot_iff_le_centralizer.mpr
  intro s hs g hg
  have ha : a g = 1 := mem_bot.mp (he ▸ mem_map_of_mem a hg)
  have hh := congrArg (fun f : MulAut S => (f ⟨s, hs⟩ : Q)) ha
  change g * s * g⁻¹ = s at hh
  exact mul_inv_eq_iff_eq_mul.mp hh

private theorem twoPerfect_centralizes_card_three
    {Q : Type*} [Group Q] [Finite Q] (P Y : Subgroup Q) [P.Normal]
    (hP : Nat.card P = 3) (hY : IsPPerfect 2 Y) :
    Y ≤ centralizer (P : Set Q) := by
  let : IsCyclic P := isCyclic_of_prime_card hP
  have ha : IsPGroup 2 (MulAut P) := by
    apply IsPGroup.of_card (n := 1)
    rw [IsCyclic.card_mulAut, hP, Nat.totient_prime Nat.prime_three]
    norm_num
  let a : Y →* MulAut P := (MulAut.conjNormal : Q →* MulAut P).comp Y.subtype
  have ht := hY.hom_eq_one_of_isPGroup ha a
  intro y hy p hp
  have he := congrArg (fun f : Y →* MulAut P => (f ⟨y, hy⟩ ⟨p, hp⟩ : Q)) ht
  change y * p * y⁻¹ = p at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- The extraspecial case is impossible: the source cubic in Y supplies a
literal elementary subgroup of order 27, contradicting the actual three-rank. -/
theorem not_extraspecial_of_twoCore_moves
    {Q : Type*} [Group Q] [Finite Q] (P Y : Subgroup Q) [P.Normal]
    (hr : primeRank 3 Q ≤ 2) (hY : IsPPerfect 2 Y)
    (hYquot : Nat.card (Y ⧸ pCore 2 Y) = 3)
    (hP : Nat.card P = 27) (hexp : ∀ x : P, x ^ 3 = 1)
    (hm : ¬ Y.pCoreIn 2 ≤ centralizer (P : Set Q)) : ¬ IsExtraspecial 3 P := by
  intro he
  let : IsExtraspecial 3 P := he
  let a := (MulAut.conjNormal : Q →* MulAut P).comp Y.subtype
  have ha : (pCore 2 Y).map a ≠ ⊥ := by
    intro hz
    apply hm
    rintro _ ⟨y, hy, rfl⟩
    have heq : a y = 1 := mem_bot.mp (hz ▸ mem_map_of_mem a hy)
    intro p hp
    have hp' := congrArg (fun f : MulAut P => (f ⟨p, hp⟩ : Q)) heq
    change (y : Q) * p * (y : Q)⁻¹ = p at hp'
    exact (mul_inv_eq_iff_eq_mul.mp hp').symm
  obtain ⟨E, _, hE, hEc⟩ :=
    Section08.SolvableExclusion.Three.Extraspecial.elementary_of_cubic_residual
      P ⊤ hP hexp le_top hY hYquot Y.subtype (fun _ => mem_top _) ha
  let : IsElementaryAbelian 3 E := hE
  have hlo : 3 ≤ Group.rank E := IsElementaryAbelian.rank_ge_of_card (p := 3) (by simpa using hEc)
  have hup := (rank_le_primeRank_of_abelian_pGroup 3 E hE.isPGroup hE.toIsMulCommutative).trans hr
  omega

/-- A moved three-core has a normal elementary-nine supercritical subgroup.
Thompson's argument excludes a central two-core action; A.1.25 excludes all
but the elementary and extraspecial models, and the cubic rank argument
eliminates the extraspecial model. The resulting nine-group is an actual
subgroup of H/O₂(H), with its conjugation action retained. -/
theorem exists_normal_nine_of_moved_threeCore
    (H Y V : Subgroup G)
    (hr : primeRank 3 (Hstar H) ≤ 2)
    (himage : starImage H (H ⊓ normalizer (Y : Set G)) =
      normalizer (starImage H Y : Set (Hstar H)))
    (hcore : V ≤ (H ⊓ normalizer (Y : Set G)).pCoreIn 2)
    (hV : IsPGroup 2 V)
    (hY : IsPPerfect 2 (starImage H Y))
    (hYquot : Nat.card (starImage H Y ⧸ pCore 2 (starImage H Y)) = 3)
    (hYV : starImage H Y ≤ centralizer (starImage H V : Set (Hstar H)))
    (hm : ⁅pCore 3 (Hstar H), starImage H V⁆ ≠ ⊥) :
    ∃ P : Subgroup (Hstar H), P.Normal ∧ P ≤ pCore 3 (Hstar H) ∧
      IsElementaryAbelian 3 P ∧ Nat.card P = 9 ∧
      ⁅P, starImage H V⁆ ≠ ⊥ ∧
      ¬ (starImage H Y).pCoreIn 2 ≤ centralizer (P : Set (Hstar H)) := by
  let S := pCore 3 (Hstar H)
  have hS : IsPGroup 3 S := pCore_isPGroup
  have hSne : S ≠ ⊥ := by intro he; apply hm; simp only [S, he, commutator_bot_left]
  let : Nontrivial S := (Subgroup.nontrivial_iff_ne_bot S).mpr hSne
  obtain ⟨X, hX⟩ := hS.exists_supercriticalPSubgroup (by decide : 3 ≠ 2)
  let : X.Characteristic := hX.characteristic
  let P := X.map S.subtype
  let : P.Normal := inferInstanceAs (X.map S.subtype).Normal
  let e : X ≃* P := X.equivMapOfInjective S.subtype S.subtype_injective
  have hP : IsPGroup 3 P := (hS.to_subgroup X).map S.subtype
  have hPm : ⁅P, starImage H V⁆ ≠ ⊥ := supercritical_moved (starImage H V)
    (hV.comap_subtype.map (QuotientGroup.mk' (pCore 2 H))) S hS X hX hm
  have hPc : ¬ (starImage H Y).pCoreIn 2 ≤ centralizer (P : Set (Hstar H)) :=
    twoCore_moves_of_normalizer H Y V himage hcore hV
      (IsPGroup.of_card (n := 1) (by simpa using hYquot)) hYV P hP hPm
  have hmodels := (ChapterA.lemma_A_1_25_1 (by decide : Odd 3) hS
    ((primeRank_subgroup_le 3 S).trans hr) X hX).2
  have hcard : Nat.card X = Nat.card P := Nat.card_congr e.toEquiv
  rcases hmodels with hcyc | hplane | hextra
  · exfalso
    apply hPc
    exact (pCoreIn_le 2 _).trans
      (twoPerfect_centralizes_card_three P (starImage H Y) (hcard.symm.trans hcyc.1) hY)
  · obtain ⟨hc, he⟩ := hplane
    have hx : IsElementaryAbelian 3 X := by
      obtain ⟨f⟩ := he
      exact { toIsMulCommutative := ⟨⟨fun x y => f.injective (by simp only [map_mul]; exact mul_comm _ _)⟩⟩
              exponent_dvd_p := hX.exponent_dvd_p }
    have hp : IsElementaryAbelian 3 P := by
      let := hx
      exact IsElementaryAbelian.of_surjective e.toMonoidHom e.surjective
    exact ⟨P, inferInstance, map_subtype_le X, hp,
      hcard.symm.trans hc, hPm, hPc⟩
  · obtain ⟨hc, he, _⟩ := hextra
    apply False.elim
    apply not_extraspecial_of_twoCore_moves P (starImage H Y) hr hY hYquot
      (hcard.symm.trans hc) ?_ hPc (he.of_mulEquiv e)
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [← map_pow, hX.pow_eq_one y, map_one]

end CFSG.Quasithin.Chapter13.Section05.ComponentReduction.Fitting

end
