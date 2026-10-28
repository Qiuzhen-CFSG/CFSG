module
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.BenderSylowOvergroups
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.PrimePSL2
public import CFSG.Quasithin.ChapterA.Section03.SourceEmbeddings.QuadraticPSL2
public import Theory.SpecificGroups.Janko1.Model.SylowTwo
public import Theory.SpecificGroups.SL2.BinaryThreeSection

/-!
# Small containing models at the original binary-three point

The smaller subgroup remains a local C-component for the full original
Sylow, with its literal PSL₃(2) two-core quotient. Proper full-Sylow
overgroups exclude the Bender carriers. In odd-prime PSL₂ a strict local
component would be A₅, contradicting the factor seven in the original
quotient. A quadratic odd-prime carrier forces its prime to be seven.
The actual J₁ model has elementary Sylow two-subgroups, so it cannot
contain this quotient through a two-group kernel.

No quasisimplicity of the smaller subgroup is assumed. The quadratic
PSL₂(49) branch is retained for the separate ambient rank argument.
Source: Aschbacher--Smith A.3.12 and the original setting of 15.3.23,
printed pp.47--48 and 1128--1129.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
open ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem binary_three_core_card {B : Subgroup G}
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) :
    Nat.card (B ⧸ pCore 2 B) = 168 :=
  (Nat.card_congr (e.trans Matrix.PSL3Two.equiv.symm).toEquiv).trans
    Matrix.PSL3Two.card_SL

omit [Finite G] in
private theorem seven_dvd_binary_three {B : Subgroup G}
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2)) : 7 ∣ Nat.card B :=
  (show 7 ∣ Nat.card (B ⧸ pCore 2 B) by
    rw [binary_three_core_card e]
    decide).trans (pCore 2 B).card_quotient_dvd_card

/-- A strict original full-Sylow local component cannot have a Bender
containing carrier. This does not require a smaller-component model. -/
theorem binary_three_point_not_bender
    (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents S) (hK : K.IsCComponent) (hBK : B < K)
    (hm : ClassificationModels.IsBenderModel K) : False :=
  hBK.ne (eq_of_solvable_sylow_overgroups S hB hK hBK.le
    (bender_solvable_proper_sylow_overgroup hm))

/-- The strict odd-prime PSL₂ branch would identify the smaller subgroup
with A₅, contrary to its original PSL₃(2) two-core quotient. -/
theorem binary_three_point_not_prime_linear
    (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents S) (hK : K.IsCComponent) (hBK : B < K)
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 p) : False := by
  obtain ⟨_,⟨a⟩⟩ := proper_primePSL2_models S hB hK hBK.le hBK.ne hp ho hm
  have hd := seven_dvd_binary_three e
  rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup] at hd
  norm_num [Nat.factorial] at hd

/-- A strict quadratic odd-prime containing carrier has parameter seven.
The surviving PSL₂(49) row still requires the original ambient geometry. -/
theorem binary_three_point_quadratic_prime_eq_seven
    (S : Sylow 2 G) {B K : Subgroup G}
    (hB : B ∈ localCComponents S) (hK : K.IsCComponent) (hBK : B < K)
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    {p : ℕ} (hp : p.Prime) (ho : Odd p)
    (hm : ClassicalGroup.IsPSL K 2 (p ^ 2)) : p = 7 := by
  obtain ⟨hgt,F,_,_,hF,⟨a⟩⟩ :=
    proper_quadraticPSL2_models S hB hK hBK.le hBK.ne hp ho hm
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
  let : IsSimpleGroup B := a.isSimpleGroup
  have hc := binary_three_core_card e
  have hcore : pCore 2 B = ⊥ := by
    rcases (inferInstance : (pCore 2 B).Normal).eq_bot_or_eq_top with he | he
    · exact he
    · rw [he] at hc
      simp at hc
  have hcard : Nat.card B = 168 := by
    rwa [hcore,Nat.card_congr (QuotientGroup.quotientBot (G := B)).toEquiv] at hc
  have horder := Matrix.ProjectiveSpecialLinearGroup.psl2_card_twice (hF ▸ ho)
  rw [←Nat.card_congr a.toEquiv,hcard,hF] at horder
  have hd : p ∣ 2 ^ 4 * 3 * 7 := by
    change p ∣ 336
    exact ⟨p ^ 2 - 1,horder⟩
  rcases hp.dvd_mul.mp hd with hd | hd
  · rcases hp.dvd_mul.mp hd with hd | hd
    · have hd' := hp.dvd_of_dvd_pow hd
      rcases (Nat.dvd_prime Nat.prime_two).mp hd' with he | he <;> omega
    · rcases (Nat.dvd_prime Nat.prime_three).mp hd with he | he <;> omega
  · rcases (Nat.dvd_prime (by decide : Nat.Prime 7)).mp hd with he | he <;> omega

/-- No subgroup with this original two-core quotient embeds in the actual
J₁ carrier: its elementary Sylow groups cannot support the order-four
element in SL₃(2). No local or quasisimplicity assumption is needed. -/
theorem binary_three_point_not_jankoOne
    {B K : Subgroup G} (hBK : B ≤ K)
    (e : (B ⧸ pCore 2 B) ≃* PSL(3,ZMod 2))
    (a : K ≃* Janko1.Model) : False := by
  let b := e.trans Matrix.PSL3Two.equiv.symm
  let π := b.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 B))
  let f := a.toMonoidHom.comp (inclusion hBK)
  have hf : IsPGroup 2 f.ker := by
    rw [(MonoidHom.ker_eq_bot_iff f).mpr (a.injective.comp (inclusion_injective hBK))]
    exact IsPGroup.of_card (n := 0) (by simp)
  apply Matrix.SpecialLinearGroup.no_binary_three_quotient_of_two_subgroup_exponent
    (X := Janko1.Model) _ π (b.surjective.comp (QuotientGroup.mk'_surjective _)) f hf
  intro P hP x
  obtain ⟨T,hT⟩ := hP.exists_le_sylow
  let := Janko1.SylowTwo.elementary T
  exact (inclusion_injective hT) (by
    rw [map_pow,map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 T) _)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.OriginalSource
