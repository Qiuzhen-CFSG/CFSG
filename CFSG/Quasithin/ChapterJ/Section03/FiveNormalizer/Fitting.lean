module
public import CFSG.Quasithin.ChapterJ.Section03.FiveNormalizer.Action
public import Theory.GroupTheory.GeneralizedFitting.SelfCentralizingPrimeCore
public import Theory.GroupTheory.SelfCentralizingNormalPSubgroup
/-!
# The generalized Fitting subgroup of the source five-normalizer

The faithful complement action on P/Φ(P) forces any element centralizing P
into P. The original extraspecial Sylow P is therefore the five-core and
the entire generalized Fitting subgroup of its actual normalizer.

Source: Aschbacher--Smith J.3.6, printed p.439.
-/

public section
noncomputable section
open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterJ.Section03
open Centralizers Centralizers.Choices
variable {G : Type*} [Group G] [Finite G] {d : LocalSetup G}
private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The actual odd core contains its full ambient centralizer. -/
theorem five_oddPart_self_centralizing (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    centralizer (fiveOddPart B5 : Set G)≤fiveOddPart B5 := by
  let P := fiveOddPart B5
  let : IsExtraspecial 5 P := five_oddPart_extraspecial c B5 hG
  obtain ⟨R,hRH,hRN,hR32,hQR,_,hgen,_⟩ := exists_five_normalizer_product c B5
  have hn := hRN.trans (normalizer_B5Image_le_normalizer_fiveOddPart B5)
  let a : normalizer (P : Set G)→*MulAut (P ⧸ frattini P) :=
    (quotientAut (frattini P)).comp P.normalizerMonoidHom
  let f : R→*MulAut (P ⧸ frattini P) := a.comp (inclusion hn)
  have hf : Function.Injective f := five_local_two_frattini_action_faithful c B5 R hRH hRN hR32 hQR
  intro x hx
  have hxN : x∈normalizer (P : Set G) := Subgroup.centralizer_le_normalizer _ hx
  have hxB : x∈normalizer (B5Image B5 : Set G) :=
    Subgroup.centralizer_le_normalizer _ (centralizer_le (B5Image_le_fiveOddPart d.card_Z B5) hx)
  have hxprod : x∈(P:Set G)*(R:Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left P R hn]
    exact hgen ▸ hxB
  obtain ⟨p,hp,r,hr,hpr⟩ := hxprod
  change p*r=x at hpr
  let pN : normalizer (P:Set G) := ⟨p,P.le_normalizer hp⟩
  let rN : normalizer (P:Set G) := ⟨r,hn hr⟩
  let xN : normalizer (P:Set G) := ⟨x,hxN⟩
  have hax : a xN=1 := by
    have hh : P.normalizerMonoidHom xN=1 := by
      apply MonoidHom.mem_ker.mp
      rw [normalizerMonoidHom_ker]
      exact hx
    exact (congrArg (quotientAut (frattini P)) hh).trans (map_one _)
  have hap : a pN=1 := by
    have hh : P.normalizerMonoidHom pN=MulAut.conj (⟨p,hp⟩ : P) := by ext; rfl
    change quotientAut (frattini P) (P.normalizerMonoidHom pN)=1
    rw [hh]
    apply MonoidHom.mem_ker.mp
    rw [IsExtraspecial.quotientAut_frattini_ker_eq_range_conj (p:=5)]
    exact ⟨⟨p,hp⟩,rfl⟩
  have he : pN*rN=xN := Subtype.ext hpr
  have har : a rN=1 := by
    have hh := congrArg a he
    rw [map_mul,hap,hax,one_mul] at hh
    exact hh
  have hr1 : r=1 := congrArg (fun y:R => (y:G)) (hf (show f ⟨r,hr⟩=f 1 from har.trans (map_one f).symm))
  rw [hr1,mul_one] at hpr
  exact hpr ▸ hp

/-- The normalizer's actual five-core is the restriction of P. -/
theorem five_normalizer_pCore (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    pCore 5 (normalizer (B5Image B5 : Set G))=
      (fiveOddPart B5).subgroupOf (normalizer (B5Image B5 : Set G)) := by
  let P := fiveOddPart B5
  let N := normalizer (B5Image B5 : Set G)
  have hPN : P≤N := (fiveOddPart_le_G5 B5).trans (Subgroup.centralizer_le_normalizer _)
  have hn : N≤normalizer (P : Set G) := normalizer_B5Image_le_normalizer_fiveOddPart B5
  let : (P.subgroupOf N).Normal := (normal_subgroupOf_iff_le_normalizer hPN).mpr hn
  have hp : IsPGroup 5 P := IsPGroup.of_card (n:=3) (SourceCompletion.five_oddPart_card c B5)
  have hle : P.subgroupOf N≤pCore 5 N := le_sSup ⟨inferInstance,hp.comap_subtype⟩
  obtain ⟨S,hS,_,_⟩ := five_oddPart_sylow c B5 hG
  have hSN : (S : Subgroup G)≤N := by rw [hS]; exact hPN
  have hc : pCore 5 N≤((S.subtype hSN) : Subgroup N) :=
    (pCore_isPGroup (p:=5) (G:=N)).le_sylow_of_normal _
  apply le_antisymm _ hle
  simpa only [Sylow.coe_subtype,hS] using hc

/-- J.3.6's generalized Fitting assertion for the literal normalizer. -/
theorem five_normalizer_generalizedFitting (c : Choices d) (B5 : Sylow 5 d.toTypeRuSetup.H)
    (hG : Nat.card G=2^14*3^3*5^3*7*13*29) :
    Theory.GroupTheory.generalizedFitting (normalizer (B5Image B5 : Set G))=
      (fiveOddPart B5).subgroupOf (normalizer (B5Image B5 : Set G)) := by
  rw [← five_normalizer_pCore c B5 hG]
  apply Theory.GroupTheory.generalizedFitting_eq_pCore_of_selfCentralizing 5
  exact centralizer_pCore_le_of_normalized 5 (fiveOddPart B5) _
    (IsPGroup.of_card (n:=3) (SourceCompletion.five_oddPart_card c B5))
    ((fiveOddPart_le_G5 B5).trans (Subgroup.centralizer_le_normalizer _))
    (normalizer_B5Image_le_normalizer_fiveOddPart B5)
    (five_oddPart_self_centralizing c B5 hG)

end CFSG.Quasithin.ChapterJ.Section03
