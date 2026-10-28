module

public import Stellmacher.MainDefs
public import FeitThompson.BGsection1.CentralizerLemmas

/-!
# Local correspondence modulo the odd core

Locals containing a fixed Sylow are identified through the odd-core quotient
when all those locals have characteristic two and at least one exists. Their normal two-subgroup
witnesses lie in the Sylow; lifting those witnesses realizes quotient locals
as images. The trivial odd core of a characteristic-two group makes the local
maps injective and hence reflects normalization. This supplies the elementary
local reduction for Stellmacher, Sections 5 and 11, as transcribed in
`refs/latex/stellmacher-n-group.tex`.

The normalized-sup p-group theorem puts each witness inside the fixed Sylow.
The odd-kernel normalizer theorem realizes lifted quotient locals as images.
Local injectivity follows because the intersection with the ambient odd core
lies in the local odd core, which centralizes the self-centralizing two-core
and is therefore trivial. The image of a local reflects containment in another
local by lifting conjugates of the latter's witness. Thus maximality and
distinctness are preserved; `pCore_map_iso` transports characteristic two.
No solvability, ambient two-core, strong-embedding, or classification input is
used. The final theorem supplies the two local hypotheses for the separate
multiple-maximal odd-core quotient setup.
-/

namespace Stellmacher.SectionEleven

private theorem witness_le_sylow
    {H : Type*} [Group H] (S0 : Sylow 2 H) (T : Subgroup H)
    (hT : IsPGroup 2 T) (hS : (S0 : Subgroup H) ≤ Subgroup.normalizer T) :
    T ≤ S0 := by
  have heq := S0.is_maximal' (S0.isPGroup'.to_sup_of_normal_right' hT hS) le_sup_left
  exact le_sup_right.trans heq.le

private theorem local_quotient_injective
    {H : Type*} [Group H] [Finite H] (U : Subgroup H)
    (hchar : Stellmacher.IsCharacteristicTwoType U) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore 2 H)).comp U.subtype) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : pPrimeCore 2 U = ⊥ := by
    have hle : pPrimeCore 2 U ≤ pCore 2 U :=
      (pPrimeCore_le_centralizer_of_normal_pgroup 2 (pCore 2 U)
        (pCore_isPGroup (p := 2) (G := U))).trans hchar
    obtain ⟨power, hpower⟩ := (pCore_isPGroup (p := 2) (G := U)).exists_card_eq
    have hcop : Nat.Coprime (Nat.card (pCore 2 U)) (Nat.card (pPrimeCore 2 U)) := by
      rw [hpower]
      exact (pPrimeCore_coprime_card (p := 2) (G := U)).pow_left power
    exact le_bot_iff.mp ((le_inf hle le_rfl).trans_eq
      (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot)
  have hinter : (pPrimeCore 2 H).comap U.subtype ≤ pPrimeCore 2 U := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    exact Nat.Coprime.of_dvd_right
      (Subgroup.card_comap_dvd_of_injective _ _ U.subtype_injective)
      (pPrimeCore_coprime_card (p := 2) (G := H))
  apply (injective_iff_map_eq_one _).mpr
  intro element helement
  have hmem : element ∈ (pPrimeCore 2 H).comap U.subtype :=
    (QuotientGroup.eq_one_iff (N := pPrimeCore 2 H) (element : H)).mp helement
  have hbot : element ∈ (⊥ : Subgroup U) := hodd ▸ hinter hmem
  exact hbot

private theorem characteristicTwo_transport
    {G H : Type*} [Group G] [Group H] (equiv : G ≃* H)
    (hchar : Subgroup.centralizer (pCore 2 G : Set G) ≤ pCore 2 G) :
    Subgroup.centralizer (pCore 2 H : Set H) ≤ pCore 2 H := by
  have hcore := pCore_map_iso 2 equiv
  intro element helement
  obtain ⟨preimage, rfl⟩ := equiv.surjective element
  rw [← hcore]
  apply Subgroup.mem_map_of_mem
  apply hchar
  rw [Subgroup.mem_centralizer_iff]
  intro other hother
  apply equiv.injective
  have hmem : equiv other ∈ pCore 2 H := by
    rw [← hcore]
    exact Subgroup.mem_map_of_mem equiv.toMonoidHom hother
  simpa only [map_mul] using
    Subgroup.mem_centralizer_iff.mp helement (equiv other) hmem

private theorem normalizes_of_map
    {G H : Type*} [Group G] [Group H] (quotient : G →* H)
    (U T : Subgroup G) (hTU : T ≤ U)
    (hinj : Function.Injective (quotient.comp U.subtype))
    (hmap : U.map quotient ≤ Subgroup.normalizer (T.map quotient)) :
    U ≤ Subgroup.normalizer T := by
  apply Subgroup.le_normalizer_iff.mpr
  intro actor hactor element helement
  have hconj : quotient (actor * element * actor⁻¹) ∈ T.map quotient := by
    simpa only [map_mul, map_inv] using
      (Subgroup.mem_normalizer_iff.mp
        (hmap (Subgroup.mem_map_of_mem quotient hactor)) (quotient element)).mp
        (Subgroup.mem_map_of_mem quotient helement)
  obtain ⟨preimage, hpreimage, heq⟩ := hconj
  have heqU : (⟨preimage, hTU hpreimage⟩ : U) =
      ⟨actor * element * actor⁻¹,
        U.mul_mem (U.mul_mem hactor (hTU helement)) (U.inv_mem hactor)⟩ := hinj heq
  have heqG : preimage = actor * element * actor⁻¹ := congrArg Subtype.val heqU
  exact heqG ▸ hpreimage

private theorem local_image
    {H : Type*} [Group H] [Finite H] (U : Subgroup H)
    (hU : IsTwoLocal U) (hchar : Stellmacher.IsCharacteristicTwoType U) :
    IsTwoLocal (U.map (QuotientGroup.mk' (pPrimeCore 2 H))) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let quotient := QuotientGroup.mk' (pPrimeCore 2 H)
  obtain ⟨T, hTne, hT, rfl⟩ := hU
  have hinj := local_quotient_injective _ hchar
  have hne : T.map quotient ≠ ⊥ := by
    intro hbot
    apply hTne
    apply le_bot_iff.mp
    intro element helement
    have hmem := Subgroup.mem_map_of_mem quotient helement
    rw [hbot] at hmem
    have heq : (⟨element, Subgroup.le_normalizer helement⟩ : Subgroup.normalizer T) = 1 :=
      hinj (by
        change quotient element = quotient 1
        simpa only [map_one, Subgroup.mem_bot] using hmem)
    exact congrArg Subtype.val heq
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  exact ⟨T.map quotient, hne, hT.map quotient,
    (normalizer_map_quotient_eq_map_normalizer 2 T (pPrimeCore 2 H)
      inferInstance (pPrimeCore_coprime_card (p := 2) (G := H))).symm⟩

private theorem local_lift
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (hinj : Function.Injective
      ((QuotientGroup.mk' (pPrimeCore 2 H)).comp (S0 : Subgroup H).subtype))
    (Ubar : Subgroup (H ⧸ pPrimeCore 2 H)) (hUbar : IsTwoLocal Ubar)
    (hSbar : (S0 : Subgroup H).map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ Ubar) :
    ∃ U : Subgroup H, IsTwoLocal U ∧ (S0 : Subgroup H) ≤ U ∧
      U.map (QuotientGroup.mk' (pPrimeCore 2 H)) = Ubar := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let quotient := QuotientGroup.mk' (pPrimeCore 2 H)
  obtain ⟨Q, hQne, hQ, rfl⟩ := hUbar
  have hQS : Q ≤ (S0 : Subgroup H).map quotient :=
    witness_le_sylow (S0.mapSurjective (QuotientGroup.mk'_surjective _)) Q hQ hSbar
  let T : Subgroup H := (S0 : Subgroup H) ⊓ Q.comap quotient
  have hmap : T.map quotient = Q := by
    apply le_antisymm
    · exact Subgroup.map_le_iff_le_comap.mpr inf_le_right
    · intro element helement
      obtain ⟨preimage, hpreimage, rfl⟩ := hQS helement
      exact ⟨preimage, ⟨hpreimage, helement⟩, rfl⟩
  have hT : IsPGroup 2 T := S0.isPGroup'.of_injective
    (Subgroup.inclusion inf_le_left) (Subgroup.inclusion_injective inf_le_left)
  have hTne : T ≠ ⊥ := by
    intro hbot
    apply hQne
    rw [← hmap, hbot, Subgroup.map_bot]
  have hS : (S0 : Subgroup H) ≤ Subgroup.normalizer T :=
    normalizes_of_map quotient _ T inf_le_left hinj (by rwa [hmap])
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  refine ⟨Subgroup.normalizer T, ⟨T, hTne, hT, rfl⟩, hS, ?_⟩
  rw [← hmap]
  exact (normalizer_map_quotient_eq_map_normalizer 2 T (pPrimeCore 2 H)
    inferInstance (pPrimeCore_coprime_card (p := 2) (G := H))).symm

private theorem local_image_reflects_le
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (U V : Subgroup H) (hU : Stellmacher.IsCharacteristicTwoType U)
    (hV : IsTwoLocal V) (hSU : (S0 : Subgroup H) ≤ U)
    (hSV : (S0 : Subgroup H) ≤ V)
    (hle : U.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤
      V.map (QuotientGroup.mk' (pPrimeCore 2 H))) : U ≤ V := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, _, hT, rfl⟩ := hV
  let : Fact (IsPGroup 2 T) := ⟨hT⟩
  apply normalizes_of_map _ U T ((witness_le_sylow S0 T hT hSV).trans hSU)
    (local_quotient_injective U hU)
  rwa [normalizer_map_quotient_eq_map_normalizer 2 T (pPrimeCore 2 H)
    inferInstance (pPrimeCore_coprime_card (p := 2) (G := H))]

/-- Characteristic-two locals and distinct maximal locals over a Sylow descend
through the quotient by the ambient odd core. -/
public theorem multiple_maximal_oddCore_quotient_local_setup
    {H : Type*} [Group H] [Finite H] (S0 : Sylow 2 H)
    (hlocal : ∀ U : Subgroup H, IsTwoLocal U → (S0 : Subgroup H) ≤ U →
      Stellmacher.IsCharacteristicTwoType U)
    (hmultiple : ∃ M1 M2 : Subgroup H, M1 ≠ M2 ∧ IsMaximalTwoLocal M1 ∧
      IsMaximalTwoLocal M2 ∧ (S0 : Subgroup H) ≤ M1 ∧ (S0 : Subgroup H) ≤ M2) :
    (∀ Ubar : Subgroup (H ⧸ pPrimeCore 2 H), IsTwoLocal Ubar →
      (S0 : Subgroup H).map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ Ubar →
      Stellmacher.IsCharacteristicTwoType Ubar) ∧
    (∃ M1 M2 : Subgroup (H ⧸ pPrimeCore 2 H), M1 ≠ M2 ∧
      IsMaximalTwoLocal M1 ∧ IsMaximalTwoLocal M2 ∧
      (S0 : Subgroup H).map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ M1 ∧
      (S0 : Subgroup H).map (QuotientGroup.mk' (pPrimeCore 2 H)) ≤ M2) := by
  let quotient := QuotientGroup.mk' (pPrimeCore 2 H)
  obtain ⟨M1, M2, hne, hmax1, hmax2, hS1, hS2⟩ := hmultiple
  have hinjS : Function.Injective (quotient.comp (S0 : Subgroup H).subtype) := by
    intro first second heq
    have hinj := local_quotient_injective M1 (hlocal M1 hmax1.1 hS1)
    have heqM : (⟨first, hS1 first.property⟩ : M1) =
        ⟨second, hS1 second.property⟩ := hinj heq
    have heqH : (first : H) = (second : H) :=
      congrArg (fun element : M1 => (element : H)) heqM
    exact Subtype.ext heqH
  have hmax (M : Subgroup H) (hM : IsMaximalTwoLocal M)
      (hSM : (S0 : Subgroup H) ≤ M) : IsMaximalTwoLocal (M.map quotient) := by
    refine ⟨local_image M hM.1 (hlocal M hM.1 hSM), ?_⟩
    intro Ubar hUbar hMUbar
    obtain ⟨U, hU, hSU, rfl⟩ := local_lift S0 hinjS Ubar hUbar
      ((Subgroup.map_mono hSM).trans hMUbar)
    have hMU := local_image_reflects_le S0 M U (hlocal M hM.1 hSM)
      hU hSM hSU hMUbar
    exact Subgroup.map_mono (hM.2 hU hMU)
  constructor
  · intro Ubar hUbar hSUbar
    obtain ⟨U, hU, hSU, rfl⟩ := local_lift S0 hinjS Ubar hUbar hSUbar
    have hinj : Function.Injective (quotient.subgroupMap U) := by
      intro first second heq
      exact local_quotient_injective U (hlocal U hU hSU)
        (congrArg Subtype.val heq)
    exact characteristicTwo_transport
      (MulEquiv.ofBijective (quotient.subgroupMap U)
        ⟨hinj, quotient.subgroupMap_surjective U⟩) (hlocal U hU hSU)
  · refine ⟨M1.map quotient, M2.map quotient, ?_, hmax M1 hmax1 hS1,
      hmax M2 hmax2 hS2, Subgroup.map_mono hS1, Subgroup.map_mono hS2⟩
    intro heq
    apply hne
    exact le_antisymm
      (local_image_reflects_le S0 M1 M2 (hlocal M1 hmax1.1 hS1)
        hmax2.1 hS1 hS2 heq.le)
      (local_image_reflects_le S0 M2 M1 (hlocal M2 hmax2.1 hS2)
        hmax1.1 hS2 hS1 heq.ge)

end Stellmacher.SectionEleven
