module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof.HallJankoPoints
public import Theory.SpecificGroups.LeechRelated.AtlasCarriers.HS.SylowOvergroups.PrimeActors
public import Theory.SpecificGroups.Rudvalis.Model.SylowOvergroups.PrimeActors
public import Theory.GroupTheory.PrimeRankOrderBound

/-!
# Higman--Sims and Rudvalis point comparisons in 11.4.2

The native full-Sylow overgroup covers of HS and Ru have quotient maps
with two-group kernels and targets S₅ and GL₃(2). Every subgroup section
modulo its intrinsic two-core therefore has order dividing 840. Apply
this to the literal point image inside the containing quotient.

The complete 11.1.1 point catalogue cannot satisfy this bound. At the
already derived field degree two, the Lie rows have two-rank at least
four. The exceptional PSL₂ primes do not divide 840; the alternating,
ternary and sporadic orders exclude all other quasisimple rows. The
existing point-quasisimplicity comparison excludes the odd extensions.
Thus neither HS nor Ru can properly contain the original point component.
The full containing catalogue now leaves only M₂₂, its triple cover,
M₂₃, J₁ and J₄ in the quasisimple-point branch.

Comparison.Overcomponent applies the reduction to the actual chosen
module. Remaining proper pairs, inner radical placement, strict omega-center
containment and final equality stay with this comparison owner. The positive
normalized-module implication remains with qt-d-1222-normalized-nonff;
earlier-source discharge stays with qt-d-1222-shadow-components.
Source: Aschbacher--Smith A.3.12 and 11.4.2, printed pp.47--48,776--777.
Imported native carrier results retain LICENSES/ATLAS.txt and
LICENSES/ATLAS-CITATION.cff. No new enumeration is used.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
open Chapter1.Section02 ChapterA.Section03 ChapterA.Section03.SourceEmbeddings
open Chapter1.Section02.LocalModels

private theorem fieldFour_lie_rank_four
    {A : Type*} [Group A] [Finite A]
    (hm : LocalGeometry.Components.LieOvergroup A 2) : 4 ≤ primeRank 2 A := by
  cases hm with
  | sl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e]
    have hh := primeRank_quotient_le_of_coprime 2 (center SL(3,F))
      (Nat.coprime_two_left.mpr (Matrix.SL3.odd_card_center F))
    change primeRank 2 PSL(3,F) ≤ _ at hh
    rw [Matrix.PSL3Even.two_rank F (by decide : 0 < 2) hF] at hh
    omega
  | psl3 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Matrix.PSL3Even.two_rank F (by decide : 0 < 2) hF]
  | sp4 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Theory.SpecificGroups.SymplecticFour.EvenTwoRank.rank hF (by decide)]
    decide
  | g2 hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [primeRank_equiv 2 e,Atlas.G2.EvenTwoRank.two_rank F hF]
    decide
  | ree m hm he _ => omega
  | triality hm =>
    obtain ⟨e⟩ := (Triality.Standard.isTrialityGroupAt_binary_iff A 2 (by decide)).mp hm
    rw [primeRank_equiv 2 e]
    exact le_trans (by decide : 4 ≤ 3 * 2)
      (Triality.Standard.TwoRank.twoRank_ge_three_mul 2 (by decide))
  | trialityCube m hm he _ => omega

private theorem exceptional_not_dvd_840 {p : ℕ} (hp : Source.ExceptionalPrime p)
    (hd : p ∣ 840) : False := by
  rw [show 840 = 2^3 * 3 * 5 * 7 by decide] at hd
  simp only [hp.1.dvd_mul] at hd
  have hh : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
    rcases hd with ((hd | hd) | hd) | hd
    · exact .inl (Nat.prime_eq_prime_of_dvd_pow hp.1 Nat.prime_two hd)
    · exact .inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_three).mp hd))
    · exact .inr (.inr (.inl ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_five).mp hd)))
    · exact .inr (.inr (.inr ((Nat.prime_dvd_prime_iff_eq hp.1 (by decide)).mp hd)))
  rcases hp with ⟨_,h5,h8⟩
  rcases hh with rfl | rfl | rfl | rfl <;> norm_num at *

private theorem fieldFour_not_dvd_840
    {A : Type*} [Group A] [Finite A] [IsQuasisimple A]
    (hc : pCore 2 A = ⊥) (hm : LocalGeometry.Components.FieldFourOvergroup A)
    (hd : Nat.card A ∣ 840) : False := by
  have hb : Nat.card A ≤ 840 := Nat.le_of_dvd (by decide) hd
  cases hm with
  | alternating hm =>
    rw [Nat.card_congr hm.some.toEquiv,nat_card_alternatingGroup] at hb
    norm_num [Nat.factorial] at hb
  | alternatingCover hm =>
    have hh := Nat.card_le_card_of_surjective (QuotientGroup.mk' (center A))
      (QuotientGroup.mk'_surjective (center A))
    rw [Nat.card_congr hm.2.2.some.toEquiv,nat_card_alternatingGroup] at hh
    norm_num [Nat.factorial] at hh
    omega
  | primeLinear p hp hm =>
    have hpd : p ∣ Nat.card A := by
      obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
      have hodd : Odd p := hp.1.odd_of_ne_two (by have := hp.2.1; omega)
      rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
        ⟨p,1,hp.1,hodd,by decide,by simpa using hF⟩,hF]
      have he : 2 ∣ p^2-1 := by
        obtain ⟨a,ha⟩ := hodd
        refine ⟨2*a*(a+1),?_⟩
        nlinarith [Nat.sub_add_cancel (show 1 ≤ p^2 by have := hp.1.two_le; nlinarith)]
      apply (Nat.dvd_div_iff_mul_dvd (dvd_mul_of_dvd_right he p)).mpr
      simpa only [Nat.mul_comm] using Nat.mul_dvd_mul (dvd_refl p) he

    exact exceptional_not_dvd_840 hp (hpd.trans hd)
  | linearTwentyFive hm =>
    obtain ⟨F,_,_,hF,⟨e⟩⟩ := hm
    rw [Nat.card_congr e.toEquiv,GorensteinWalter.psl2_card_formula F
      ⟨5,2,by decide,by decide,by decide,by simpa using hF⟩,hF] at hd
    norm_num at hd
  | three u hm =>
    have hh := (odd_ternary_five_card_bounds u hm).2.1
    omega
  | m22 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m22_order] at hb
    omega
  | m22Cover hm =>
    have hh := Nat.card_le_card_of_surjective (QuotientGroup.mk' (center A))
      (QuotientGroup.mk'_surjective (center A))
    rw [Nat.card_congr hm.2.2.some.toEquiv,Sporadic.Mathieu.m22_order] at hh
    omega
  | m23 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.Mathieu.m23_order] at hb
    omega
  | j1 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko1.card_model] at hd
    norm_num at hd
  | j2 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.J2.ExceptionalParabolics.FirstParabolic.card_carrier] at hb
    omega
  | j4 hm =>
    rw [Nat.card_congr hm.some.toEquiv,Janko4.Cardinality.model_card] at hb
    omega
  | hs hm =>
    rw [Nat.card_congr hm.some.toEquiv,Sporadic.LeechRelated.HS.NormalizerIndex.card_carrier] at hb
    omega
  | ru hm =>
    rw [Nat.card_congr hm.some.toEquiv,Rudvalis.model_card] at hb
    omega
  | nilpotentExtension hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _ (by decide : Odd 5) hm).elim
  | elementaryExtension p hp hm =>
    exact (Quasisimple.Classification.not_odd_sl2_extension hc _
      (hp.1.odd_of_ne_two (by have := hp.2.1; omega)) hm).elim


variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}
    {L V : Subgroup G} {D : Chapter12.Section02.ChosenModule T L V}

/-- The complete point catalogue in a strict comparison at field four
has no quasisimple two-core quotient of order dividing 840. -/
theorem ofFlag_point_quotient_not_dvd_840
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    [IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz)]
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hdegree : S.field.degree = 2) :
    ¬ Nat.card ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ∣ 840 := by
  intro hd
  cases ofFlag_overcomponent_alternative S f X z H e h.point_mem_local_family le_rfl with
  | equal he =>
    exact ((h.strict_comparison (fixed_and_transitive D S _ hlinear h1132).1 hne).2.1.ne he).elim
  | lie hm =>
    rw [hdegree] at hm
    have hl := fieldFour_lie_rank_four hm
    have hu : primeRank 2 ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz) ≤ 3 :=
      primeRank_le_of_prime_pow_not_dvd (fun hh => (by decide : ¬ 2^4 ∣ 840) (hh.trans hd))
    omega
  | four _ hm => exact fieldFour_not_dvd_840 (pCore_quotient_pCore_eq_bot 2) hm hd


/-- The native HS and Ru full-Sylow covers bound the literal point
quotient, with all quotient kernels retained. -/
theorem point_quotient_order_dvd_840_in_higmanSims_or_rudvalis
    {E : Closure.Geometry D} (h : EarlierGeometry E) {J : Subgroup G}
    (hJ : J ∈ Chapter1.L G (T : Subgroup G)) (hlt : E.Kz < J)
    (hm : Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Rudvalis.Model)) :
    Nat.card (E.Kz ⧸ pCore 2 E.Kz) ∣ 840 := by
  rcases hm with hm | hm
  · let e := hm.some
    obtain ⟨P,C,hC,hproper,_,⟨a⟩,htop⟩ := proper_local_model_image h.point_mem_local_family hJ
      (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt e
    rw [Nat.card_congr a.toEquiv]
    exact Sporadic.LeechRelated.HS.SylowOvergroups.proper_overgroup_section_order P
      (C ⊔ (P : Subgroup Sporadic.LeechRelated.HS.Carrier)) C le_sup_right
      (local_sup_ne_top_of_ne_top htop P C hC hproper) le_sup_left
  · let e := hm.some
    have hO : pCore 2 Rudvalis.Model = ⊥ := by
      rw [←pCore_map_iso 2 e,pCore_quotient_pCore_eq_bot 2,Subgroup.map_bot]
    have hcover := Rudvalis.SylowOvergroups.oddIndexMaximalCover_of_twoCore_of_radicalCover hO
      Chapter1.XiEmbedding.InvariantThree.SporadicRemaining.rudvalis_oddIndexMaximalTwoCore
      Rudvalis.SylowOvergroups.oddIndexMaximalRadicalCover
    obtain ⟨P,C,hC,hproper,_,⟨a⟩,htop⟩ := proper_local_model_image h.point_mem_local_family hJ
      (sylow_normalizes_overcomponent h hJ hlt.le) (sylow_normalizes_point h) hlt e
    rw [Nat.card_congr a.toEquiv]
    exact Rudvalis.SylowOvergroups.proper_overgroup_section_order hcover P
      (C ⊔ (P : Subgroup Rudvalis.Model)) C le_sup_right
      (local_sup_ne_top_of_ne_top htop P C hC hproper) le_sup_left

/-- Neither HS nor Ru can be a proper containing quotient on the original
flag. Quasisimplicity of the point and the field degree are derived. -/
theorem ofFlag_not_higmanSims_or_rudvalis_overcomponent
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    {J : Subgroup G} (hJ : J ∈ Chapter1.L G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    ¬ (Nonempty ((J ⧸ pCore 2 J) ≃* Sporadic.LeechRelated.HS.Carrier) ∨
      Nonempty ((J ⧸ pCore 2 J) ≃* Rudvalis.Model)) := by
  intro hm
  let := point_quasisimple_in_higmanSims_or_rudvalis h hJ hlt hm
  have hd := (ofFlag_proper_overcomponent_fieldFour S f X z H h hne hlinear h1132 e hJ hlt).1
  exact ofFlag_point_quotient_not_dvd_840 S f X z H h hne hlinear h1132 e hd
    (point_quotient_order_dvd_840_in_higmanSims_or_rudvalis h hJ hlt hm)

/-- The remaining containing carriers after the HS and Ru comparisons.
This is an output of the full catalogue, not a recognition hypothesis. -/
@[expose] def MathieuJankoPointContainer (A : Type*) [Group A] : Prop :=
  Nonempty (A ≃* Sporadic.Mathieu.M22) ∨ IsM22Cover A ∨
  Nonempty (A ≃* Sporadic.Mathieu.M23) ∨ Nonempty (A ≃* Janko1.Model) ∨
  Nonempty (A ≃* Janko4.Model)

/-- The complete quasisimple-point comparison now leaves only the three
Mathieu and two Janko containing rows, on the literal quotient. -/
theorem ofFlag_quasisimple_point_mathieu_janko_containers
    (S : D.NonbinaryNaturalInput)
    {c : LocalGeometry.Coordinates D S.field} (f : LocalGeometry.InvariantFlag c)
    (X : Subgroup G) (z : G) (H : Subgroup G)
    (h : EarlierGeometry (ofFlag S f X z H))
    (hne : (ofFlag S f X z H).Kz ≠ (ofFlag S f X z H).K)
    (hqs : IsQuasisimple ((ofFlag S f X z H).Kz ⧸ pCore 2 (ofFlag S f X z H).Kz))
    (hlinear : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      V ⊓ centralizer (L : Set G) = ⊥)
    (h1132 : ∀ A, Hypothesis1131At D S (c.binarySubspace (f.space 0)) A →
      Proposition1132At D S (c.binarySubspace (f.space 0)) A)
    (e : ((ofFlag S f X z H).L₁ ⧸ pCore 2 (ofFlag S f X z H).L₁) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) S.field.Carrier)
    (hcent : (ofFlag S f X z H).V₁ ≤ centralizer ((ofFlag S f X z H).R₁ : Set G))
    {J : Subgroup G} (hJ : J ∈ Chapter1.LStar G (T : Subgroup G))
    (hlt : (ofFlag S f X z H).Kz < J) :
    S.field.degree = 2 ∧ MathieuJankoPointContainer (J ⧸ pCore 2 J) := by
  obtain ⟨hd,hm⟩ := ofFlag_quasisimple_point_containers
    S f X z H h hne hqs hlinear h1132 e hcent hJ hlt
  refine ⟨hd,?_⟩
  rcases hm with hm | hm | hm | hm | hm | hm | hm
  · exact .inl hm
  · exact .inr (.inl hm)
  · exact .inr (.inr (.inl hm))
  · exact .inr (.inr (.inr (.inl hm)))
  · exact .inr (.inr (.inr (.inr hm)))
  · exact (ofFlag_not_higmanSims_or_rudvalis_overcomponent S f X z H h hne
      hlinear h1132 e hJ.1 hlt (.inl hm)).elim
  · exact (ofFlag_not_higmanSims_or_rudvalis_overcomponent S f X z H h hne
      hlinear h1132 e hJ.1 hlt (.inr hm)).elim

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ComponentGeometry.Comparison.Overcomponent.EmbeddingProof
