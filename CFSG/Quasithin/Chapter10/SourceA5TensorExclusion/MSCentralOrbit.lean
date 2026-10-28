module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.CentralOrbit
public import CFSG.Quasithin.Chapter10.SourceA5TensorExclusion.MSInputs
public import CFSG.Quasithin.ChapterB.Section01.QuasisimpleSections.Group
public import Theory.GroupTheory.PResidual.SubnormalSupplement
public import Theory.SpecificGroups.SymplecticFour.SimpleQuotients
public import Theory.SpecificGroups.SymplecticFour.EvenProjective

/-!
# The faithful central orbit in the original tensor branch

The original nonnormal stabilizer T₁ is Sylow in an outside group H. The
source uniqueness argument supplies both MS hypotheses. For a component K
with H=KT₁ and F*(H)=O₂(H), the generic central-orbit theorem then gives an
elementary subgroup W=⟨Ω₁(Z(T₁))^H⟩ with C_H(W)=O₂(H), moved by K.

The symplectic specialization retains the supplied quotient map
K/O₂(K) ≃ Sp₄(4), which supplies simplicity through the actual projective
quotient. It does not assume or conclude natural-module recognition.
The earlier construction of H and K and the subsequent identification of
the whole commutator core remain independent source obligations.

Source: Aschbacher--Smith9.3.6--10 and C.1.31--32, printed pp.733--734
and135--136; initial module reduction for MS93 Main Theorem case(3).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
open ChapterC.MSCentralOrbit

private theorem perfect_twoPerfect {J : Type*} [Group J] [Finite J]
    [Group.IsPerfect J] : IsPPerfect 2 J := by
  intro N hN hp
  let := hN
  have hs : Subsingleton (J ⧸ N) := by
    by_contra! hn
    exact Group.IsPerfect.not_isNilpotent (J ⧸ N) hp.isNilpotent
  apply eq_top_iff.mpr
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

private theorem initial_layer {J : Type*} [Group J] [Finite J]
    (K R : Subgroup J) (hK : K.IsCComponent)
    [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hfit : generalizedFitting J = pCore 2 J)
    (hprod : ∀ g : J, ∃ k ∈ K, ∃ r ∈ R, k * r = g)
    (hodd : ChapterC.MSOddIndexRadical R)
    (hms : ChapterC.MSCharacteristicCondition R) :
    IsElementaryAbelian 2 (omegaOrbit R) ∧
      centralizer (omegaOrbit R : Set J) = pCore 2 J ∧
      ¬ K ≤ centralizer (omegaOrbit R : Set J) := by
  let := hK.perfect
  have hres : pResidual 2 J = K :=
    pResidual_eq_of_subnormal_product K R hK.subnormal perfect_twoPerfect
      hodd.isPGroup hprod
  let : K.Normal := by rw [← hres]; infer_instance
  have hself : centralizer (pCore 2 J : Set J) ≤ pCore 2 J := by
    simpa only [hfit] using
      (ChapterB.QuasisimpleSections.centralizer_generalizedFitting_le (G := J))
  have hne : R ≠ ⊥ := by
    intro hr
    have hn : pCore 2 J = ⊥ := le_bot_iff.mp (hr ▸ hodd.twoCore_le)
    have ht : (⊤ : Subgroup J) ≤ ⊥ := by
      intro j _
      have hc : j ∈ centralizer (pCore 2 J : Set J) := by
        rw [hn]
        intro x hx
        have hx1 : x = 1 := hx
        simp only [hx1, one_mul, mul_one]
      exact hn ▸ hself hc
    exact hK.ne_bot (le_bot_iff.mp (le_top.trans ht))
  exact ⟨omegaOrbit_elementary R hodd.twoCore_le hself,
    omegaOrbit_centralizer K R hodd.isPGroup hne hodd.twoCore_le hself hprod hms,
    component_not_centralizes_omegaOrbit K R hodd.isPGroup hne hprod hms⟩

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original stabilizer supplies the faithful central orbit of an outside component. -/
theorem source_tensor_msCentralOrbit
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    [IsSimpleGroup (K ⧸ pCore 2 K)]
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k * r = g) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
    IsElementaryAbelian 2 (omegaOrbit R) ∧
      centralizer (omegaOrbit R : Set H) = pCore 2 H ∧
      ¬ K ≤ centralizer (omegaOrbit R : Set H) := by
  obtain ⟨hodd, hms⟩ := source_nonnormal_stabilizer_msInputs D hn H hRH hLH hout hs
  exact initial_layer K _ hK hfit hprod hodd hms

/-- Specialization to the literal Sp₄(4) quotient in source9.3.10. -/
theorem source_tensor_sp4_msCentralOrbit
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (H : Subgroup G)
    (hRH : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ H)
    (hLH : L ≤ H) (hout : ¬ H ≤ D.maximalLocal)
    (hs : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ normalizer (L : Set G)) H)
    (K : Subgroup H) (hK : K.IsCComponent)
    {F : Type*} [Field F] [Finite F] (hF : Nat.card F = 4)
    (eK : (K ⧸ pCore 2 K) ≃* Matrix.symplecticGroup (Fin 2) F)
    (hfit : generalizedFitting H = pCore 2 H)
    (hprod : ∀ g : H, ∃ k ∈ K,
      ∃ r ∈ (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H), k * r = g) :
    let R := (((T : Subgroup G) ⊓ normalizer (L : Set G)).subgroupOf H)
    IsElementaryAbelian 2 (omegaOrbit R) ∧
      centralizer (omegaOrbit R : Set H) = pCore 2 H ∧
      ¬ K ≤ centralizer (omegaOrbit R : Set H) := by
  let : CharP F 2 := Theory.SpecificGroups.SymplecticFour.EvenProjective.charTwo_of_card
    (f := 2) hF
  let := Theory.SpecificGroups.SymplecticFour.SimpleQuotients.isSimpleGroup
    (F := F) (by omega)
  let : IsSimpleGroup (K ⧸ pCore 2 K) :=
    (eK.trans Theory.SpecificGroups.SymplecticFour.EvenProjective.equiv).isSimpleGroup
  exact source_tensor_msCentralOrbit D hn H hRH hLH hout hs K hK hfit hprod

end CFSG.Quasithin.Chapter10
