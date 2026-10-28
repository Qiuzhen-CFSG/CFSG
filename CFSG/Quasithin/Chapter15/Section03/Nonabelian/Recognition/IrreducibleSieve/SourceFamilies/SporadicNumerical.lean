module

public import CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve.SourceFamilies.Common
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.PrimeEleven
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.OddSubgroups
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.HigmanSimsRank
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.JankoFourRank
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.Rudvalis
public import CFSG.Quasithin.ChapterG.Section07.SporadicLocal.HeldRank
public import CFSG.Quasithin.ChapterG.Section07.MathieuRecognition.DegreeBounds
public import Theory.Mathieu.M23.Properties.TwoRank
public import Theory.SpecificGroups.Held.Automorphisms.Normalizer
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassB.Closure.Application

/-!
# Degree exclusions for the single sporadic component branches

The elementary abelian source actor embeds in the automorphisms of the
irreducibly acting component. Its rank bounds the source dimension from above.
The certified model automorphism ranks and faithful binary degree bounds
contradict this inequality for M11, M23, J1, J4, HS, He and Ru. Every bound is
transported along the given isomorphism of the actual component.

Source: Aschbacher--Smith, G.7.2--G.7.3 and 15.3.58.
-/

public section
open Subgroup Representation Theory.GroupTheory
open Sporadic.Mathieu Sporadic.LeechRelated
namespace CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
open ChapterG.Section07.SporadicLocal
variable {H W : Type*} [Group H] [Finite H] [AddCommGroup W] [Module (ZMod 2) W]
  [FiniteDimensional (ZMod 2) W]
  {ρ : Representation (ZMod 2) H W} {X K : Subgroup H} {T : Sylow 2 H}
  {v : H} {s : ℕ}

private theorem degree_bound_of_model {D : Type*} [Group D]
    (h : SourceData ρ X T v s) (hK : ComponentData ρ K)
    (e : K ≃* D) {r : ℕ} (hr : primeRank 2 (MulAut D) ≤ r) :
    Module.finrank (ZMod 2) W ≤ 2 * (r + 1) := by
  let : Finite D := Finite.of_injective e.symm e.symm.injective
  have hd := h.degree_le_component_automorphisms hK
  rw [primeRank_equiv 2 (MulAut.congr e)] at hd
  omega

private theorem degree_ten_of_eleven {D : Type*} [Group D]
    (h : SourceData ρ X T v s) (e : K ≃* D) (hD : 11 ∣ Nat.card D) :
    10 ≤ Module.finrank (ZMod 2) W := by
  have hd : 11 ∣ Nat.card K := by
    rw [Nat.card_congr e.toEquiv]
    exact hD
  simpa only [BinaryPrimeDegree.orderOf_two_mod_eleven] using
    BinaryPrimeDegree.orderOf_le_finrank (ρ.comp K.subtype)
      (h.faithful.comp K.subtype_injective) (by decide : Nat.Prime 11) (by decide) hd

theorem SourceData.not_m11_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* M11) : False := by
  have := degree_bound_of_model h hK e m11_automorphism_twoRank_le_three
  have := degree_ten_of_eleven h e m11_eleven_dvd_card
  omega

theorem SourceData.not_j1_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* Janko1.Model) : False := by
  have := degree_bound_of_model h hK e j1_automorphism_twoRank_le_three
  have := degree_ten_of_eleven h e j1_eleven_dvd_card
  omega

theorem SourceData.not_m23_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* M23) : False := by
  have := degree_bound_of_model h hK e m23_automorphism_twoRank_le_four
  have := ChapterG.Section07.MathieuRecognition.eleven_le_finrank_of_m23
    (ρ.comp K.subtype) (h.faithful.comp K.subtype_injective) e
  omega

theorem SourceData.not_hs_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* HS.Carrier) : False := by
  have := degree_bound_of_model h hK e hs_automorphism_twoRank_le_five
  have := hs_finrank_ge_twenty ρ h.faithful K e
  omega

theorem SourceData.not_he_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (e : K ≃* Held.He) : False := by
  have hr := he_automorphism_twoRank_le_six_of_normalizer
    Held.permutationNormalizerQuotient_card_le_two Held.Realization.normalizer_surjective
  have := degree_bound_of_model h hK e hr
  have := he_finrank_ge_twenty ρ h.faithful K e
  omega

theorem SourceData.not_ru_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hsimple : IsSimpleGroup K) (e : K ≃* Rudvalis.Model) : False := by
  let := hsimple
  let : IsSimpleGroup Rudvalis.Model := e.symm.isSimpleGroup
  have := degree_bound_of_model h hK e ru_automorphism_twoRank_le_six
  have := ru_finrank_ge_twenty ρ h.faithful K e
  omega

theorem SourceData.not_j4_component (h : SourceData ρ X T v s)
    (hK : ComponentData ρ K) (hsimple : IsSimpleGroup K)
    (hnonab : ¬ IsMulCommutative K) (e : K ≃* Janko4.Model) : False := by
  let := hsimple
  let : IsQuasisimple K := ChapterA.Section02.Sporadic.SourceAssembly.simple_quasisimple hnonab
  let : IsSimpleGroup Janko4.Model := e.symm.isSimpleGroup
  let : Group.IsPerfect Janko4.Model := Group.IsPerfect.ofSurjective
    (f := e.toMonoidHom) e.surjective
  have := degree_bound_of_model h hK e j4_automorphism_twoRank_le_eleven
  have := j4_finrank_ge_one_hundred_ten ρ h.faithful K e
  omega

end CFSG.Quasithin.Chapter15.Section03.Nonabelian.Recognition.IrreducibleSieve
