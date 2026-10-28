module
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.Structure
public import Theory.GroupTheory.QuaternionFaithfulAction
public import Theory.GroupTheory.PGroup.CoprimeFrattiniAction
public import Theory.GroupTheory.PGroup.ExtraspecialAutomorphisms
public import Theory.ElementaryAbelian.AutomorphismLinearEmbedding
/-!
# The original five-normalizer complement action

The marked involution z acts nontrivially on the order125 odd core P.
Consequently its quaternion subgroup acts faithfully, and the source
centralizer order then forces the whole order32 complement to act faithfully.
The coprime Frattini theorem retains faithfulness on P/Φ(P). Once P is
extraspecial this quotient has order25, giving an actual GL₂(5) embedding.

Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
noncomputable section
open Subgroup
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private theorem five_local_two_inf_G5 (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (R : Subgroup G) (hRH : R≤d.toTypeRuSetup.H) (hR32 : Nat.card R=32)
    (hQR : CQ B5≤R) : R⊓G5 B5=CQ B5 := by
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  have hle : CQ B5≤R⊓G5 B5 := le_inf hQR inf_le_right
  have h32 : Nat.card (R⊓G5 B5 : Subgroup G)∣32 := hR32 ▸ card_dvd_of_le inf_le_left
  have h40 : Nat.card (R⊓G5 B5 : Subgroup G)∣40 :=
    q.local_card ▸ card_dvd_of_le (inf_le_inf_right _ hRH)
  exact (eq_of_le_of_card_ge hle (by
    rw [CQ_card B5 q]
    exact Nat.le_of_dvd (by decide) (show Nat.card (R⊓G5 B5 : Subgroup G)∣8 from Nat.dvd_gcd h32 h40))).symm

/-- The original normalizer action of the local order32 complement is faithful. -/
theorem five_local_two_action_faithful (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (R : Subgroup G) (hRH : R≤d.toTypeRuSetup.H) (hRN : R≤normalizer (B5Image B5 : Set G))
    (hR32 : Nat.card R=32) (hQR : CQ B5≤R) :
    Function.Injective ((fiveOddPart B5).normalizerMonoidHom.comp
      (inclusion (hRN.trans (normalizer_B5Image_le_normalizer_fiveOddPart B5)))) := by
  let P := fiveOddPart B5
  let ρ : R→*MulAut P := P.normalizerMonoidHom.comp
    (inclusion (hRN.trans (normalizer_B5Image_le_normalizer_fiveOddPart B5)))
  let θ : CQ B5→*MulAut P := ρ.comp (inclusion hQR)
  obtain ⟨q⟩ := c.fiveQuaternionData_source B5
  obtain ⟨eQ⟩ := q.quaternion
  have hzQ : c.z∈CQ B5 := (q.inf_U.symm ▸ c.z_mem_Z).1
  let z : CQ B5 := ⟨c.z,hzQ⟩
  have hz2 : orderOf z=2 := by rw [← orderOf_coe]; exact SourceCompletion.z_order c
  have hθz : θ z≠1 := by
    intro hh
    have hPC : P≤centralizer ({c.z} : Set G) := by
      intro p hp
      apply mem_centralizer_singleton_iff.mpr
      have he := congrArg (fun a : MulAut P => (a ⟨p,hp⟩ : G)) hh
      change c.z*p*c.z⁻¹=p at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    have he : P=B5Image B5 := by
      exact (inf_eq_left.mpr hPC).symm.trans (c.fiveOddPart_inf_centralizer_z d.card_Z B5 q)
    have hc := congrArg (fun X : Subgroup G => Nat.card X) he
    rw [SourceCompletion.five_oddPart_card c B5,B5Image_card d.card_Z B5] at hc
    norm_num at hc
  have hθ : Function.Injective θ := θ.injective_of_quaternion_involution eQ z hz2 hθz
  apply (MonoidHom.ker_eq_bot_iff ρ).mp
  apply bot_unique
  intro r hr
  apply mem_bot.mpr
  have hrC : (r:G)∈centralizer (P : Set G) := by
    have hh : ρ.ker=(centralizer (P : Set G)).subgroupOf R := by
      rw [← MonoidHom.comap_ker,normalizerMonoidHom_ker]
      rfl
    have hr' : r∈(centralizer (P : Set G)).subgroupOf R := hh ▸ hr
    exact hr'
  have hrG5 : (r:G)∈G5 B5 := centralizer_le (B5Image_le_fiveOddPart d.card_Z B5) hrC
  have hrQ : (r:G)∈CQ B5 := five_local_two_inf_G5 c B5 R hRH hR32 hQR ▸ ⟨r.property,hrG5⟩
  have he : θ ⟨r,hrQ⟩=θ 1 := by exact hr.trans (map_one θ).symm
  exact Subtype.ext (congrArg (fun a : CQ B5 => (a:G)) (hθ he))

/-- The literal action on the Frattini quotient of P is faithful. -/
theorem five_local_two_frattini_action_faithful (c : Choices d)
    (B5 : Sylow 5 d.toTypeRuSetup.H) (R : Subgroup G)
    (hRH : R≤d.toTypeRuSetup.H) (hRN : R≤normalizer (B5Image B5 : Set G))
    (hR32 : Nat.card R=32) (hQR : CQ B5≤R) :
    Function.Injective ((quotientAut (frattini (fiveOddPart B5))).comp
      ((fiveOddPart B5).normalizerMonoidHom.comp
        (inclusion (hRN.trans (normalizer_B5Image_le_normalizer_fiveOddPart B5))))) := by
  apply MonoidHom.injective_frattini_action_of_coprime
    (IsPGroup.of_card (p:=5) (n:=3) (SourceCompletion.five_oddPart_card c B5))
    _ (five_local_two_action_faithful c B5 R hRH hRN hR32 hQR)
  rw [hR32]
  decide

/-- The Frattini quotient has dimension two over the field with five elements. -/
theorem five_oddPart_frattini_card (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    Nat.card (fiveOddPart B5 ⧸ frattini (fiveOddPart B5))=25 := by
  let : IsExtraspecial 5 (fiveOddPart B5) := five_oddPart_extraspecial c B5 hG
  rw [IsExtraspecial.frattini_eq_center (p:=5)]
  have hh := card_eq_card_quotient_mul_card_subgroup (center (fiveOddPart B5))
  rw [SourceCompletion.five_oddPart_card c B5,IsExtraspecial.center_order_p 5 (fiveOddPart B5)] at hh
  omega

/-- The original order32 complement embeds faithfully in GL₂(5). -/
theorem exists_five_local_two_linear_action (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) (R : Subgroup G)
    (hRH : R≤d.toTypeRuSetup.H) (hRN : R≤normalizer (B5Image B5 : Set G))
    (hR32 : Nat.card R=32) (hQR : CQ B5≤R) :
    ∃ f : R→*Matrix.GeneralLinearGroup (Fin 2) (ZMod 5), Function.Injective f := by
  let P := fiveOddPart B5
  let : IsExtraspecial 5 P := five_oddPart_extraspecial c B5 hG
  let : Fact (IsPGroup 5 P) := ⟨IsExtraspecial.isPGroup 5 P⟩
  let : IsElementaryAbelian 5 (P ⧸ frattini P) := isElementaryAbelian_quotient_frattini (p:=5)
  obtain ⟨i,hi⟩ := IsElementaryAbelian.exists_injective_mulAut_generalLinear_of_card_le
    (p:=5) (n:=2) (P ⧸ frattini P) (by rw [five_oddPart_frattini_card c B5 hG]; decide)
  exact ⟨i.comp ((quotientAut (frattini P)).comp (P.normalizerMonoidHom.comp
    (inclusion (hRN.trans (normalizer_B5Image_le_normalizer_fiveOddPart B5))))),
    hi.comp (five_local_two_frattini_action_faithful c B5 R hRH hRN hR32 hQR)⟩

end CFSG.Quasithin.ChapterJ.Section03
