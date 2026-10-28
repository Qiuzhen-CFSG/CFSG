module

public import CFSG.Quasithin.ChapterB.Section01.IrreducibleReduction
public import CFSG.Quasithin.ChapterB.Section01.FittingStructure.MovedFactors.FixedKernel

/-!
# The literal quotient action in B.1.10

Once the fixed-space kernel equals Q = O₂(G), the canonical isomorphism
G/Q ≃ Aut_G(C_V(Q)) constructs a faithful action of the literal quotient.
Its action on vectors and all subgroup images agree with the original
restriction. A moved quasisimple or cubic factor survives, the offender
restricts genuinely, and a noncentral odd normal nilpotent subgroup has a
noncentral image inside the Fitting subgroup of G/Q.

These are the quotient verifications in Aschbacher–Smith B.1.10,
printed p.72 (PDF p.83). The kernel and centralization premises below are
supplied by `FixedKernel`, and the induction consumer discharges them.
-/

@[expose] public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
namespace CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

noncomputable def quotientActionEquiv
    (hk : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G) :
    G ⧸ pCore 2 G ≃* subspaceActionImage ρ (fixedSpace ρ (pCore 2 G)) :=
  (QuotientGroup.quotientMulEquivOfEq ((invariantActionHom_ker ρ _
    (fixedSpace_stable_of_normal ρ (pCore 2 G))).trans hk).symm).trans
    (invariantActionQuotientEquiv ρ _ (fixedSpace_stable_of_normal ρ (pCore 2 G)))

theorem quotientActionEquiv_mk
    (hk : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G) (g : G) :
    quotientActionEquiv ρ hk (QuotientGroup.mk' (pCore 2 G) g) =
      invariantActionHom ρ _ (fixedSpace_stable_of_normal ρ (pCore 2 G)) g := by
  rfl

noncomputable def quotientAction
    (hk : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G) :
    Representation (ZMod 2) (G ⧸ pCore 2 G) (fixedSpace ρ (pCore 2 G)) :=
  (subspaceImageRepresentation ρ _).comp (quotientActionEquiv ρ hk).toMonoidHom

theorem quotientAction_injective
    (hk : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G) :
    Function.Injective (quotientAction ρ hk) :=
  (subspaceImageRepresentation_injective ρ _).comp (quotientActionEquiv ρ hk).injective

theorem quotientAction_apply
    (hk : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G)
    (g : G) (w : fixedSpace ρ (pCore 2 G)) :
    (quotientAction ρ hk (QuotientGroup.mk' (pCore 2 G) g) w : V) = ρ g w := by
  rfl

theorem quotientAction_map
    (hk : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G) (A : Subgroup G) :
    (A.map (QuotientGroup.mk' (pCore 2 G))).map (quotientActionEquiv ρ hk).toMonoidHom =
      restrictedSubgroup ρ (fixedSpace ρ (pCore 2 G)) A := by
  rw [Subgroup.map_map]
  exact invariantActionHom_map ρ _ (fixedSpace_stable_of_normal ρ (pCore 2 G)) A

variable [Finite G]

omit [Finite G] in
private theorem factor_ne_bot {K : Subgroup G}
    (hK : IsQuasisimple K ∨ Nat.card K = 3) : K ≠ ⊥ := by
  rcases hK with hK | hK
  · let : IsQuasisimple K := hK
    let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
    let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
    exact (nontrivial_iff_ne_bot K).mp inferInstance
  · intro hb
    have hh := Subgroup.card_eq_one.mpr hb
    omega

private theorem quotient_injective_on_odd (K : Subgroup G)
    (hK : Nat.Coprime 2 (Nat.card K)) :
    Function.Injective ((QuotientGroup.mk' (pCore 2 G)).subgroupMap K) := by
  let f := (QuotientGroup.mk' (pCore 2 G)).subgroupMap K
  apply (MonoidHom.ker_eq_bot_iff f).mp
  apply bot_unique
  intro x hx
  apply Subtype.ext
  have hq : (x : G) ∈ pCore 2 G :=
    (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val hx)
  have hd : Disjoint K (pCore 2 G) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact hK.symm.pow_right n
  exact (Subgroup.disjoint_def.mp hd x.property hq)

theorem quotient_factor (K : Subgroup G)
    (hK : IsQuasisimple K ∨ Nat.card K = 3) :
    IsQuasisimple (K.map (QuotientGroup.mk' (pCore 2 G))) ∨
      Nat.card (K.map (QuotientGroup.mk' (pCore 2 G))) = 3 := by
  rcases hK with hK | hK
  · let : IsQuasisimple K := hK
    exact Or.inl (irreducibleReduction_image_quasisimple K
      (QuotientGroup.mk' (pCore 2 G)) (QuotientGroup.ker_mk' _))
  · right
    let f := (QuotientGroup.mk' (pCore 2 G)).subgroupMap K
    have hi := quotient_injective_on_odd K (by rw [hK]; decide)
    have hc := Nat.card_congr (MulEquiv.ofBijective f
      ⟨hi, (QuotientGroup.mk' (pCore 2 G)).subgroupMap_surjective K⟩).toEquiv
    exact hc.symm.trans hK

variable [FiniteDimensional (ZMod 2) V]

theorem quotient_bestOffender
    (hk : subspaceKernel ρ (fixedSpace ρ (pCore 2 G)) ⊤ = pCore 2 G)
    (K A : Subgroup G) (hK : IsQuasisimple K ∨ Nat.card K = 3)
    (hKA : K = ⁅K,A⁆) (hA : IsBestOffender ρ A)
    (hQK : pCore 2 G ≤ centralizer (K : Set G)) :
    IsBestOffender (quotientAction ρ hk) (A.map (QuotientGroup.mk' (pCore 2 G))) := by
  let U := fixedSpace ρ (pCore 2 G)
  let q := QuotientGroup.mk' (pCore 2 G)
  have hmove : ¬ U ≤ fixedSpace ρ A := by
    intro hfix
    have hAQ : A ≤ pCore 2 G := by
      rw [← hk]
      intro a ha
      exact ⟨mem_top _, fun v hv => hfix hv ⟨a, ha⟩⟩
    have hh : ⁅K,A⁆ = ⊥ := by
      rw [commutator_comm]
      exact commutator_eq_bot_iff_le_centralizer.mpr (hAQ.trans hQK)
    exact factor_ne_bot hK (hKA.trans hh)
  have hbest := hA.restricted ρ U
    (le_trans le_top (fixedSpace_stable_of_normal ρ (pCore 2 G))) hmove
  let : IsElementaryAbelian 2 A := hA.1.2
  refine ⟨⟨?_, IsElementaryAbelian.map q⟩, ?_⟩
  · intro hz
    apply hbest.1.1
    rw [← quotientAction_map ρ hk A, hz, Subgroup.map_bot]
  · intro B hB
    change weight ((subspaceImageRepresentation ρ U).comp (quotientActionEquiv ρ hk).toMonoidHom) B ≤
      weight ((subspaceImageRepresentation ρ U).comp (quotientActionEquiv ρ hk).toMonoidHom) (A.map q)
    rw [weight_comp_map _ _ (quotientActionEquiv ρ hk).injective,
      weight_comp_map _ _ (quotientActionEquiv ρ hk).injective, quotientAction_map]
    apply hbest.2
    simpa only [quotientAction_map] using (Subgroup.map_mono (f := (quotientActionEquiv ρ hk).toMonoidHom) hB)

theorem quotient_noncentral (N K : Subgroup G) [N.Normal]
    (hN : Nat.Coprime 2 (Nat.card N)) (hne : ⁅N,K⁆ ≠ ⊥) :
    ⁅N.map (QuotientGroup.mk' (pCore 2 G)), K.map (QuotientGroup.mk' (pCore 2 G))⁆ ≠ ⊥ := by
  intro hz
  rw [← map_commutator] at hz
  have hle : ⁅N,K⁆ ≤ pCore 2 G := by
    simpa only [QuotientGroup.ker_mk'] using (map_eq_bot_iff ⁅N,K⁆).mp hz
  have hd : Disjoint N (pCore 2 G) := by
    apply disjoint_of_coprime_natCard
    obtain ⟨n, hn⟩ := (pCore_isPGroup (p := 2) (G := G)).exists_card_eq
    rw [hn]
    exact hN.symm.pow_right n
  exact hne (bot_unique ((le_inf (commutator_le_left N K) hle).trans hd.eq_bot.le))

theorem quotient_not_centralizes_fitting (N K : Subgroup G) [N.Normal]
    [Group.IsNilpotent N] (hN : Nat.Coprime 2 (Nat.card N)) (hne : ⁅N,K⁆ ≠ ⊥) :
    ¬ K.map (QuotientGroup.mk' (pCore 2 G)) ≤
      centralizer (fittingSubgroup (G ⧸ pCore 2 G) : Set (G ⧸ pCore 2 G)) := by
  let q := QuotientGroup.mk' (pCore 2 G)
  let : Group.IsNilpotent (N.map q) :=
    Group.nilpotent_of_surjective (q.subgroupMap N) (q.subgroupMap_surjective N)
  have hNF : N.map q ≤ fittingSubgroup (G ⧸ pCore 2 G) :=
    le_sSup ⟨inferInstance, inferInstance⟩
  intro hc
  apply quotient_noncentral N K hN hne
  rw [commutator_comm]
  exact commutator_eq_bot_iff_le_centralizer.mpr (hc.trans (centralizer_le hNF))

end CFSG.Quasithin.ChapterB.FittingStructure.MovedFactors
