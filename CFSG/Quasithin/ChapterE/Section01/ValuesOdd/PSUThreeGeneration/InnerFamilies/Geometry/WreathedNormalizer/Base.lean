module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantLarge.OddCartan.UnitaryPosition.Projective
public import ABG.ChapterII.Section1.WreathedAbelianMaximal

/-!
# The characteristic abelian Sylow base in PSU₃(p)

For p congruent to three modulo four, the exact two-part of p+1 selects
the wreathed GU₂ Sylow construction. The actual involution centralizer and
odd projective kernel transport it to every Sylow subgroup of every stored
PSU₃(p) model. This includes p=3 and arbitrary nondegenerate Hermitian forms.
Uniqueness of the abelian subgroup of the base order proves characteristicity.

The two intrinsic normalizer predicates are interfaces proved in Movement
and Solvability; they are not extra assumptions in the final overgroup theorem.
Source: Aschbacher--Smith A.3.21(b), printed p.55, and E.1.14(7), p.214;
ABG II.1 Lemma 2(ii) and II.2 Lemma 1.
-/

public section

open Subgroup
namespace CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.WreathedNormalizer
open CFSG.Quasithin.ChapterA.Section03
open CFSG.Quasithin.Chapter1.XiEmbedding.InvariantLarge.OddCartan.UnitaryPosition

private theorem gu2_wreathed (p : ℕ) [Fact p.Prime] (hp : Odd p)
    (hmod : p % 4 = 3) (T : Sylow 2 (ABG.GU2 p 1 (by decide))) :
    ABG.IsWreathedGroup T := by
  obtain ⟨r, d, hd, he⟩ := Nat.exists_eq_two_pow_mul_odd (by omega : p + 1 ≠ 0)
  have hr : 2 ≤ r := by
    by_contra hn
    have hcases : r = 0 ∨ r = 1 := by omega
    obtain ⟨k, hk⟩ := hd
    rcases hcases with rfl | rfl <;> simp only [pow_zero, pow_one, one_mul] at he <;> omega
  have hdiv : 2 ^ r ∣ p ^ 1 + 1 := by simpa only [pow_one] using (Dvd.intro d he.symm)
  have hodd : Odd ((p ^ 1 + 1) / 2 ^ r) := by
    rw [pow_one, he, Nat.mul_div_cancel_left _ (by positivity)]
    exact hd
  obtain ⟨P, hP, _⟩ := ABG.SU2Level_wreathed_sylow p 1 hp (by decide) r hr hdiv hodd
  have hT : (T : Subgroup (ABG.GU2 p 1 (by decide))) ≤
      ABG.SU2Level p 1 (by decide) r := by
    intro a ha
    rw [ABG.mem_SU2Level_iff_orderOf_dvd]
    let detU := (Matrix.GeneralLinearGroup.det (n := Fin 2)
      (R := GaloisField p (2 * 1))).comp
      (ABG.unitaryForm 2 p 1 (by decide)).unitarySubgroup.subtype
    have hdo : orderOf (detU a) ∣ 2 ^ r * d := by
      rw [← he]
      simpa only [pow_one, detU, MonoidHom.comp_apply, coe_subtype] using ABG.GU2_det_orderOf_dvd p 1 (by decide) a
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_orderOf_dvd_pow (⟨a, ha⟩ : T)
    have htwo : orderOf (detU a) ∣ 2 ^ k := (orderOf_map_dvd detU a).trans
      (by simpa only [orderOf_mk] using hk)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp htwo
    change orderOf (detU a) ∣ 2 ^ r
    rw [hj] at hdo ⊢
    exact (hd.coprime_two_left.pow_left j).dvd_mul_right.mp hdo
  let e : T ≃* P := (subgroupOfEquivOfLe hT).symm.trans ((T.subtype hT).equiv P)
  exact ⟨r, ABG.wreathed_equiv e.symm hP⟩

/-- The congruence selects the wreathed branch, including p = 3, for every
actual projective unitary form and its specified Sylow subgroup. -/
theorem isPSU_sylow_wreathed {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmod : p % 4 = 3)
    (hmodel : ClassicalGroup.IsPSU K 3 p) (S : Sylow 2 K) :
    ABG.IsWreathedGroup S := by
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨F, hF, hfin, J, hcard, hconj, ⟨e⟩⟩ := hmodel
  obtain ⟨P, ⟨ep⟩⟩ := projectiveUnitary_sylow_equiv J p hcard hconj
    (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  let Q : Sylow 2 (ABG.GU2 p 1 (by decide)) := Classical.choice inferInstance
  obtain ⟨eq⟩ := su3_sylow_equiv_GU2 p hodd P Q
  let es : S ≃* Q := ((e.subgroupMap (S : Subgroup K)).trans ep).trans eq
  obtain ⟨n, hn⟩ := gu2_wreathed p hodd hmod Q
  exact ⟨n, ABG.wreathed_equiv es.symm hn⟩

/-- Uniqueness of the abelian subgroup of the base order makes the base
characteristic; an ambient normalizer cannot change the diagonal choice. -/
theorem base_characteristic {S : Type*} [Group S] {n : ℕ}
    (P : ABG.Wreathed.Presentation S n) : P.U.Characteristic := by
  let : IsMulCommutative P.U := P.abelian_maximal_unique.1
  rw [characteristic_iff_map_eq]
  intro e
  apply P.abelian_eq_U_of_card_eq
  · infer_instance
  · exact card_map_of_injective e.injective

/-- A characteristic abelian index-two subgroup in every Sylow of PSU₃(p),
constructed from the actual matrix model rather than assumed. -/
theorem exists_characteristic_abelian_base {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) (hodd : Odd p) (hmod : p % 4 = 3)
    (hmodel : ClassicalGroup.IsPSU K 3 p) (S : Sylow 2 K) :
    ∃ A : Subgroup S, IsMulCommutative A ∧ A.index = 2 ∧ A.Characteristic := by
  obtain ⟨n, hn⟩ := isPSU_sylow_wreathed hp hodd hmod hmodel S
  obtain ⟨P⟩ := ABG.Wreathed.nonempty_presentation hn
  exact ⟨P.U, P.abelian_maximal_unique.1, P.index_U, base_characteristic P⟩
/-- The intrinsic solvability calculation for the abelian Sylow base. -/
@[expose] def IntrinsicSolvability (K : Type*) [Group K] : Prop :=
  ∀ (S : Sylow 2 K) (A : Subgroup S), IsMulCommutative A → A.index = 2 →
    Group.IsSolvable (normalizer (A.map (S : Subgroup K).subtype : Set K))

/-- The intrinsic movement calculation for a Sylow-central involution. -/
@[expose] def IntrinsicMovement (K : Type*) [Group K] : Prop :=
  ∀ (S : Sylow 2 K) (A : Subgroup S), IsMulCommutative A → A.index = 2 →
    ∀ z : S, orderOf z = 2 → z ∈ center S →
      ¬ normalizer (A.map (S : Subgroup K).subtype : Set K) ≤
        centralizer ({(z : K)} : Set K)

end CFSG.Quasithin.ChapterE.ValuesOdd.PSUThreeGeneration.InnerGeometry.WreathedNormalizer
