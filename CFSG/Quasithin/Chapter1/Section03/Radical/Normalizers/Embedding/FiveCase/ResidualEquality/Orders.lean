module

public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Embedding.FiveCase.Source
/-!
# Orders for the case-(10) residual comparison

Inclusion D ≤ K gives divisibility of |D/O₂(D)| into |K/O₂(K)|.
The proof restricts the quotient map, proves its kernel is a two-group,
and factors through that kernel; it does not posit an embedding of the
intrinsic quotients. The actual PSL₃(5) model then bounds the first order
by 372000. The marked elementary extension has order 3000, and its
preimage differs in order by a power of two.

Source: Aschbacher–Smith, proof of 1.3.8, printed p.513; the matrix order
formula is the checked ATLAS port imported by FiveCase.Source.
-/

@[expose] public section
noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase.ResidualEquality
open Section02 Section02.LocalModels
universe u v
variable {G : Type u} [Group G] [Finite G]

omit [Finite G] in
private theorem quotient_card_dvd_of_kernel_le {H : Type v} [Group H]
    (f : G →* H) (U : Subgroup G) [U.Normal] (hker : f.ker ≤ U) :
    Nat.card (G ⧸ U) ∣ Nat.card H := by
  let g : G ⧸ f.ker →* G ⧸ U :=
    QuotientGroup.map f.ker U (MonoidHom.id G) hker
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective U x
    exact ⟨QuotientGroup.mk' f.ker y, rfl⟩
  have hd := card_dvd_of_surjective g hg
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at hd
  exact hd.trans (card_subgroup_dvd_card f.range)

omit [Finite G] in
private theorem inclusion_quotient_kernel_isTwoGroup {D K : Subgroup G} (hDK : D ≤ K) :
    IsPGroup 2 (((QuotientGroup.mk' (pCore 2 K)).comp (inclusion hDK)).ker) := by
  let f := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hDK)
  let j : f.ker →* pCore 2 K :=
    (inclusion hDK).comp f.ker.subtype |>.codRestrict _ (fun a =>
      (QuotientGroup.eq_one_iff (N := pCore 2 K) _).mp a.property)
  exact pCore_isPGroup.of_injective j (fun a b he => Subtype.ext
    (inclusion_injective hDK (congrArg (fun z : pCore 2 K => (z : K)) he)))

omit [Finite G] in
theorem quotient_card_dvd {D K : Subgroup G} (hDK : D ≤ K) :
    Nat.card (XiQuotient D) ∣ Nat.card (XiQuotient K) := by
  let f := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hDK)
  have hker : f.ker ≤ pCore 2 D :=
    le_sSup ⟨inferInstance, inclusion_quotient_kernel_isTwoGroup hDK⟩
  exact quotient_card_dvd_of_kernel_le f _ hker

theorem psl_three_five_card :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 5)) = 372000 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have h := Atlas.ExceptionalSupport.card_psl_mul (F := ZMod 5) 3
  norm_num [Fin.prod_univ_succ] at h
  rw [Nat.card_eq_fintype_card]
  omega

theorem residual_quotient_card_dvd {𝒦 : GroupClass.{u}} {p r : ℕ} {L : Subgroup G}
    {T : Sylow 2 G} {C : Subgroup (radicalCore p L T)} {K : Subgroup G}
    (h : SourceData 𝒦 p r L T C K)
    (hcase : CaseTen (quotientImage (normalizerResidual L (radicalCore p L T))
      (normalizer (C.map (radicalCore p L T).subtype : Set G)))
      (quotientImage K (normalizer (C.map (radicalCore p L T).subtype : Set G))) 5) :
    Nat.card (XiQuotient (normalizerResidual L (C.map (radicalCore p L T).subtype)))
      ∣ 372000 := by
  obtain ⟨e⟩ := component_model_five h.component.1 h.component.2 hcase.large_model
  have hd := quotient_card_dvd h.residual_le
  rwa [Nat.card_congr e.toEquiv, psl_three_five_card] at hd

theorem marked_five_card {H : Type v} [Group H] [Finite H] {B P : Subgroup H}
    (h : MarkedFiveExtension B P) : Nat.card B = 3000 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨hPB, hP, hn, ⟨e⟩⟩ := h
  let := hn
  have hc := (P.subgroupOf B).card_mul_index
  rw [Nat.card_congr (subgroupOfEquivOfLe hPB).toEquiv, elementary_card hP,
    index_eq_card, Nat.card_congr e.toEquiv, Atlas.card_sl_two] at hc
  norm_num at hc
  exact hc.symm

theorem card_eq_power_two_mul_image {D K : Subgroup G} (hDK : D ≤ K) :
    ∃ a : ℕ, Nat.card D = 2 ^ a * Nat.card (quotientImage D K) := by
  let f := (QuotientGroup.mk' (pCore 2 K)).comp (inclusion hDK)
  obtain ⟨a, ha⟩ := (inclusion_quotient_kernel_isTwoGroup hDK).exists_card_eq
  refine ⟨a, ?_⟩
  have hc := f.ker.card_mul_index
  rw [index_ker, ha] at hc
  have hr : f.range = quotientImage D K := by
    ext x
    constructor
    · rintro ⟨d, rfl⟩
      exact ⟨inclusion hDK d, d.property, rfl⟩
    · rintro ⟨d, hd, rfl⟩
      exact ⟨⟨d, hd⟩, rfl⟩
  rw [hr] at hc
  exact hc.symm

end CFSG.Quasithin.Chapter1.RadicalNormalizers.Embedding.FiveCase.ResidualEquality
