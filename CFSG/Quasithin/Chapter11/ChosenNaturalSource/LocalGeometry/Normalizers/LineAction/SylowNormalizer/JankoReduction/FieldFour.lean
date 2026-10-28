module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.LineAction.SylowNormalizer.Flags
public import GorensteinWalter.PSL2Cardinality
public import Theory.SpecificGroups.Janko1.Model.SylowTwo

/-!
# The field parameter in a J₁ containing component

The kernel of Y → K/O₂(K) is a normal two-group, so the order of
Y/O₂(Y) divides the order of K/O₂(K). The actual PSL₂(2ⁿ) marking and
J₁ order then force n = 2: divisibility by sixteen excludes n ≥ 4,
and the PSL₂(8) order excludes n = 3. The argument retains the literal
inclusion and both intrinsic two-core quotients.

This supplies the parameter clause in the JankoConfiguration constructor;
recognition of the J₁ quotient remains with qt-d-1222-natural-line-action.
Source: Aschbacher--Smith, the first paragraph of 3.3.16, printed p.591.
-/

public noncomputable section
open Subgroup

private theorem core_quotient_card_dvd_of_inclusion {G : Type*} [Group G] [Finite G]
    {Y K : Subgroup G} (hYK : Y ≤ K) :
    Nat.card (Y ⧸ pCore 2 Y) ∣ Nat.card (K ⧸ pCore 2 K) := by
  let q := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hYK)
  have hp : IsPGroup 2 q.ker := by
    dsimp only [q]
    rw [← MonoidHom.comap_ker,QuotientGroup.ker_mk']
    exact pCore_isPGroup.comap_of_injective _ (inclusion_injective hYK)
  have hker : q.ker ≤ pCore 2 Y := le_sSup ⟨inferInstance,hp⟩
  have hd : Nat.card (Y ⧸ pCore 2 Y) ∣ Nat.card (Y ⧸ q.ker) := by
    change (pCore 2 Y).index ∣ q.ker.index
    exact index_dvd_of_le hker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange q).toEquiv] at hd
  exact hd.trans q.range.card_subgroup_dvd_card

private theorem binary_rank_one_card {B : Type*} [Group B] {n : ℕ}
    (hm : ClassicalGroup.IsPSL B 2 (2^n)) :
    Nat.card B = 2^n * ((2^n)^2 - 1) := by
  obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := n)
    (by simpa [Nat.card_eq_fintype_card] using hF)
  rw [Nat.card_congr (e.trans (Theory.PSL2.sl2QuotientEquiv F).symm).toEquiv,
    GorensteinWalter.sl2_card_formula,hF]

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {c : Coordinates D S.field} {f : InvariantFlag c}

/-- A literal J₁ containing quotient forces the field order four. No abstract
family label or preselected field parameter is assumed. -/
theorem degree_eq_two_of_janko_containing {K : Subgroup G} (i : Fin 2)
    (hYK : f.Li i ≤ K) (e : K ⧸ pCore 2 K ≃* Janko1.Model) : S.field.degree = 2 := by
  have hd := core_quotient_card_dvd_of_inclusion hYK
  rw [binary_rank_one_card ((invariantFlag_geometry D S f).2.2.model i),
    Nat.card_congr e.toEquiv,Janko1.card_model] at hd
  have hpow : 2 ^ S.field.degree ∣ 175560 := (dvd_mul_right _ _).trans hd
  have hlt : S.field.degree < 4 := by
    by_contra hge
    have hd16 : 16 ∣ 175560 := (pow_dvd_pow 2 (by omega : 4 ≤ S.field.degree)).trans hpow
    norm_num at hd16
  have hcases : S.field.degree = 2 ∨ S.field.degree = 3 := by
    have hn := S.nonbinary
    omega
  rcases hcases with he | he
  · exact he
  · norm_num [he] at hd

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry.Normalizers.SylowNormalizer
