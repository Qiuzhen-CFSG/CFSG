module
public import BenderSuzuki.ZD.Recognition.ResidualEmbedding.LocalResidual.NormalComplements.RankOne.ModelGeometry.Source
public import Theory.SpecificGroups.SL2.CardFourEquiv
public import BenderSuzuki.SE.Borel
public import CFSG.Quasithin.ChapterI.Section06To08.UniqueFixedSource
public import Theory.SpecificGroups.PSL2.SylowFixedQuotients.Five

/-!
# The binary short-centralizer Bender alternatives

I.8.5 applied to a normal four-plane with unique fixed cosets gives a perfect
odd central cover of a simple Bender group. Sylow omega order four restricts
the cover to A₅ or PSU₃(4). The actual PSU₃(4) Borel has order 960, so a
five-free local group leaves A₅ with the original four-plane as its Sylow.

Source: Aschbacher--Smith I.8.5 and F.4.42, printed p.295. The consumer is
ShortBender's argument in the original ambient short centralizer.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki BenderSuzuki.MatrixGroups
open BenderSuzuki.PFAppendixIII
open scoped MatrixGroups
namespace CFSG.Quasithin.BinaryShortModels

private instance {E : Type*} [Field E] [Finite E] :
    Finite (Matrix.ProjGenLinGroup (Fin 3) E) :=
  Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective

theorem omega_four_oddCover_cases {G : Type*} [Group G] [Finite G]
    (hp : commutator G = ⊤) (ho : Odd (Nat.card (center G)))
    (hm : BenderSuzuki.IsSimpleBenderGroup (G ⧸ center G))
    (S : Sylow 2 G) (hS : Nat.card (omegaOneAmbient (S : Subgroup G)) = 4) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) ∨
      ∃ (E : Type) (_ : Field E) (_ : Finite E) (J : HermitianForm 3 E),
        J.form = !![0,0,1;0,1,0;1,0,0] ∧ Nat.card E = 16 ∧
        Nat.card {x : E // J.conj x = x} = 4 ∧
        Nonempty (G ≃* ProjectiveSpecialUnitaryMatrixGroup J) := by
  obtain ⟨n,hn,hm⟩ := hm.exists_exponent
  have hpow := (ZD.RankOneModelGeometry.oddCentralCover_omega_geometry hn hp ho hm S).2.2.1
  have hn2 : n = 2 := by
    have he : (2:ℕ)^n=2^2 := hpow.symm.trans hS
    exact Nat.pow_right_injective (by decide : 2≤(2:ℕ)) he
  subst n
  rcases ZD.RankOneModelGeometry.oddCentralCover_model_cases hn hp ho hm with
    ⟨_,⟨e⟩⟩ | ⟨_,m,hm,hbad,_⟩ | ⟨E,hfield,hfinite,J,hJ,hcard,hfixed,hcase⟩
  · obtain ⟨a⟩ := Matrix.ProjectiveSpecialLinearGroup.equiv_alternatingGroup_of_card_four
      (show Nat.card (BinaryGaloisField 2) = 4 by rw [GaloisField.card 2 2 (by decide)]; rfl)
    exact Or.inl ⟨e.trans a⟩
  · omega
  · right
    refine ⟨E,hfield,hfinite,J,hJ,by simpa using hcard,by simpa using hfixed,?_⟩
    rcases hcase with ⟨_,he⟩ | ⟨_,hodd,_⟩
    · exact he
    · norm_num at hodd

theorem unitary_four_borel_card {E : Type*} [Field E] [Finite E]
    (J : HermitianForm 3 E) (hJ : J.form = !![0,0,1;0,1,0;1,0,0])
    (hE : Nat.card E = 16) (hF : Nat.card {x : E // J.conj x = x} = 4)
    (B : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (hB : IsBorelSubgroup B) :
    Nat.card B = 960 := by
  obtain ⟨_,ρ,a,_,_,hU,hr,_,hG,_⟩ := External.huppert_II_10_12 J 4 hE hF hJ
  obtain ⟨R,_,hRU,_,hUN,_,_,_,hR,_,_,_,hreg,_⟩ := hr
  let Ω := {x : Projectivization E (Fin 3 → E) // x ∈
    {x | ∃ (v : Fin 3 → E) (hv : v ≠ 0), x = Projectivization.mk E v hv ∧
      dotProduct (fun i => J.conj (v i)) (J.form.mulVec v) = 0}}
  let : MulAction (ProjectiveSpecialUnitaryMatrixGroup J) Ω := MulAction.compHom Ω ρ
  have hN : normalizer (R : Set (ProjectiveSpecialUnitaryMatrixGroup J)) =
      MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) a :=
    normalizer_eq_stabilizer_of_regular_compl R a hRU
      (by intro he; rw [he,card_bot] at hR; norm_num at hR) hreg hUN
  have hRcard : Nat.card R = 2 ^ (Nat.card (ProjectiveSpecialUnitaryMatrixGroup J)).factorization 2 := by
    rw [hR,hG]
    norm_num
    rw [show 62400 = 2^6 * 975 by decide,
      Nat.factorization_mul (by decide) (by decide),Nat.factorization_pow]
    norm_num [Nat.prime_two.factorization,
      Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 2 ∣ 975)]
  let Q := Sylow.ofCard R hRcard
  obtain ⟨S,hS⟩ := hB.2
  obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (ProjectiveSpecialUnitaryMatrixGroup J) S Q
  have he : (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)).map
      (MulAut.conj g).toMonoidHom = R := by
    exact congrArg Sylow.toSubgroup hg
  have hc := card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (K := normalizer ((S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) : Set (ProjectiveSpecialUnitaryMatrixGroup J)))
    (MulAut.conj g).injective
  have hNm := map_equiv_normalizer_eq (S : Subgroup (ProjectiveSpecialUnitaryMatrixGroup J)) (MulAut.conj g)
  rw [he] at hNm
  rw [hNm,hN] at hc
  rw [←hS] at hc
  have hUc : Nat.card (MulAction.stabilizer (ProjectiveSpecialUnitaryMatrixGroup J) a) = 960 := by
    exact hU
  exact hc.symm.trans hUc

theorem omega_four_five_free_borel_alternating {G : Type*} [Group G] [Finite G]
    (hp : commutator G = ⊤) (ho : Odd (Nat.card (center G)))
    (hm : BenderSuzuki.IsSimpleBenderGroup (G ⧸ center G))
    (S : Sylow 2 G) (hS : Nat.card (omegaOneAmbient (S : Subgroup G)) = 4)
    (B : Subgroup G) (hB : IsBorelSubgroup B) (hfive : ¬ 5 ∣ Nat.card B) :
    Nonempty (G ≃* alternatingGroup (Fin 5)) := by
  rcases omega_four_oddCover_cases hp ho hm S hS with h | ⟨E,hEf,hEn,J,hJ,hE,hF,⟨e⟩⟩
  · exact h
  · have hc := unitary_four_borel_card J hJ hE hF (B.map e.toMonoidHom) (hB.map_mulEquiv e)
    rw [card_map_of_injective e.injective] at hc
    exact (hfive (hc ▸ (by decide : 5 ∣ 960))).elim

end CFSG.Quasithin.BinaryShortModels

namespace CFSG.Quasithin.BinaryShortModels
open Subgroup Theory.GroupTheory

theorem unique_fixed_four_five_free_normalClosure
    {G : Type*} [Group G] [Finite G]
    (V M : Subgroup G) [IsElementaryAbelian 2 V] [(V.subgroupOf M).Normal]
    (hVM : V ≤ M) (hV : Nat.card V = 4) (hfive : ¬ 5 ∣ Nat.card M)
    (hproper : M ≠ ⊤)
    (hfix : ∀ v : G, v ∈ V → v ≠ 1 → ∃! q : G ⧸ M, v • q = q) :
    Nonempty (normalClosure (V : Set G) ≃* alternatingGroup (Fin 5)) ∧
      ∃ S : Sylow 2 (normalClosure (V : Set G)),
        (S : Subgroup (normalClosure (V : Set G))).map
          (normalClosure (V : Set G)).subtype = V := by
  have hVne : V ≠ ⊥ := by intro he; rw [he,card_bot] at hV; omega
  obtain ⟨hquasi,hm,_,hB,S,hSN,hVS⟩ :=
    (CFSG.Quasithin.ChapterI.Section06To08.lemma_I_8_5_structure V M hVM hVne hproper hfix).resolve_left
      (fun h => by have hh := h.1; omega)
  let L := normalClosure (V : Set G)
  let N := M.comap L.subtype
  let : IsQuasisimple L := hquasi
  have ho : Odd (Nat.card (center L)) := by
    have hc := (CFSG.Quasithin.ChapterI.Section06To08.lemma_I_8_5_oddCore_recognition
      V M hVM hVne hproper hfix).resolve_left (fun h => by have hh := h.1; omega)
    have hcent : pPrimeCore 2 L = center L := hc.2.2.1
    rw [←hcent]
    exact Nat.coprime_two_left.mp (pPrimeCore_coprime_card (G := L) (p := 2))
  have hVL : V ≤ L := le_normalClosure
  have hfour : Nat.card (omegaOneAmbient (S : Subgroup L)) = 4 := by
    change Nat.card ((omega₁ S (p := 2)).map (S : Subgroup L).subtype) = 4
    rw [←hVS,Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv,hV]
  have hfN : ¬ 5 ∣ Nat.card N := by
    intro hd
    let j : N →* M := (L.subtype.comp N.subtype).codRestrict M (fun x => x.property)
    have hj : Function.Injective j := by
      intro a b he
      exact Subtype.ext (Subtype.ext (congrArg (fun x : M => (x:G)) he))
    exact hfive (hd.trans (card_dvd_of_injective j hj))
  obtain ⟨e⟩ := omega_four_five_free_borel_alternating
    (show commutator L = ⊤ from Group.IsPerfect.commutator_eq_top) ho hm S hfour N hB hfN
  have hSc : Nat.card S = 4 := by
    rw [←card_map_of_injective (f := e.toMonoidHom) (K := (S : Subgroup L)) e.injective]
    exact Theory.PSL2.SylowFixedQuotients.alternating_sylow_card
      (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  have hVS' : V.subgroupOf L = (S : Subgroup L) := eq_of_le_of_card_ge
    (hVS.trans_le (omegaOneAmbient_le _)) (by
      rw [Nat.card_congr (subgroupOfEquivOfLe hVL).toEquiv,hV,hSc])
  refine ⟨⟨e⟩,S,?_⟩
  rw [←hVS',map_subgroupOf_eq_of_le hVL]

end CFSG.Quasithin.BinaryShortModels
