module
public import Theory.Representation.SL3.NaturalParabolicFixed
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockSetup
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.NonblockCentralizer
public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.BlockAlternatingSetup
public import Theory.GroupTheory.SelfCentralizingCorePGroupJoin

/-!
# The cohomological centralizer step in the nonblock MS argument

Let E = Ω₁Z(O₂(KS)) and A = [E,K], retaining the original K and S.
The constrained component makes KS characteristic two, so Ω₁Z(S) lies
in E. A common SL₃ marking of one or two natural summands of A, with L
containing the actual line parabolic, now gives E = A × C_E(K) and
C_E(L) = C_E(K). The proved natural first-cohomology vanishing supplies
the splitting; no fixed-subgroup equality is an input.

Restricting this equality to Ω₁Z(S) feeds the existing crossing-normalizer
argument and proves C_S(K) = 1. The final theorem excludes the actual
central layer of C.1.34(4), since the original MS commutator lies in S.

The natural summands and their common parabolic marking remain explicit
C.1.34/C.4.1 inputs. Their construction, exclusion of case (2), MSData,
SecondaryData and final assembly remain with
`qt-d-1222-rankone-uniqueness-nonblock`. This is not a construction of those
records or a proof of the full nonblock branch.
Source: Aschbacher--Smith, original 4.3.8--10, printed pp.616--617;
C.1.34(2)--(4), pp.136--137, and I.1.6, p.408.
-/

@[expose] public section

open Subgroup Theory.GroupTheory
open scoped MatrixGroups commutatorElement
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
open Nonblock
open Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open Representation.OneCohomology
open Matrix.PSL3.LinearThree
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem SourceConfiguration.nonblock_join_selfCentralizing (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    (Nonblock.K c ⊔ S c) ⊓ centralizer ((Nonblock.K c ⊔ S c).pCoreIn 2 : Set G) ≤
      (Nonblock.K c ⊔ S c).pCoreIn 2 := by
  let e : c.K ≃* Nonblock.K c := c.K.equivMapOfInjective c.H.subtype c.H.subtype_injective
  have hcK : centralizer (pCore 2 (Nonblock.K c) : Set (Nonblock.K c)) ≤ pCore 2 (Nonblock.K c) :=
    (Theory.Quasithin.centralizer_pCore_le_iff 2 e).mp
      (hf ▸ centralizer_generalizedFitting_le c.K)
  have hJ := centralizer_pCore_sup_le 2 (Nonblock.K c) (S c) hcK
    (T.isPGroup'.to_le (show S c ≤ (T : Subgroup G) from inf_le_left))
    (inf_le_right.trans c.normalizer_component.le)
  intro x hx
  refine ⟨⟨x,hx.1⟩, hJ ?_, rfl⟩
  intro y hy
  exact Subtype.ext (mem_centralizer_iff.mp hx.2 y (mem_map_of_mem _ hy))

theorem SourceConfiguration.nonblock_omega_sylow_le_core_omega (c : SourceConfiguration T L)
    (hf : generalizedFitting c.K = pCore 2 c.K) :
    Subgroup.omegaCenterIn (S c) ≤ Subgroup.omegaCenterIn ((Nonblock.K c ⊔ S c).pCoreIn 2) := by
  have hQS : (Nonblock.K c ⊔ S c).pCoreIn 2 ≤ S c :=
    c.block_join_core_le.trans (c.core_sylow.le.trans inf_le_left)
  intro x hx
  obtain ⟨hS,hc,hp⟩ := (mem_omegaCenterIn_iff (S c) x).mp hx
  have hQ := centralizer_le hQS hc
  exact (mem_omegaCenterIn_iff _ _).mpr
    ⟨c.nonblock_join_selfCentralizing hf ⟨mem_sup_right hS,hQ⟩,hQ,hp⟩

namespace Nonblock
abbrev coreOmega (c : SourceConfiguration T L) : Subgroup G :=
  Subgroup.omegaCenterIn ((K c ⊔ S c).pCoreIn 2)
abbrev movedCoreOmega (c : SourceConfiguration T L) : Subgroup G := ⁅coreOmega c,K c⁆

omit [Finite G] in
private theorem coreOmega_normalized (c : SourceConfiguration T L) :
    K c ≤ normalizer (coreOmega c : Set G) :=
  (le_sup_left : K c ≤ K c ⊔ S c).trans
    (((K c ⊔ S c).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (K c ⊔ S c)
        (pCore 2 (K c ⊔ S c : Subgroup G)))).trans
      (normalizer_le_normalizer_omegaCenterIn _))

omit [Finite G] in
private theorem actor_kernel_centralizes {F : Type*} [Field F]
    (c : SourceConfiguration T L)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (g : K c) (hg : linearThreeActor e g = 1) :
    (g : G) ∈ centralizer (coreOmega c : Set G) := by
  have hgQ : g ∈ pCore 2 (K c) := (QuotientGroup.eq_one_iff _).mp
    (e.injective (by simpa [linearThreeActor] using hg))
  have hn : K c ⊔ S c ≤ normalizer (K c : Set G) :=
    (sup_le (map_subtype_le _) inf_le_right).trans c.normalizer_component.le
  have hgJ : (g : G) ∈ (K c ⊔ S c).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left hn (mem_map_of_mem _ hgQ)
  intro z hz
  exact ((mem_omegaCenterIn_iff _ z).mp hz).2.1 g hgJ |>.symm

omit [Finite G] in
private theorem coordinates {F B V : Type*} [Field F] [Group B]
    [AddCommGroup V] [Module F V] {K D : Subgroup G} {f : K →* B}
    {ρ : Representation F B V} (hm : HasSectionModel K D ⊥ f ρ) :
    ∃ e : D ≃* Multiplicative V, ∀ (g : K) (v : V),
      (e.symm (Multiplicative.ofAdd (ρ (f g) v)) : G) =
        g * (e.symm (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ := by
  have hn := hm.2.1
  rw [HasSectionModel, bot_subgroupOf] at hm
  obtain ⟨_,_,_,hbot, e, he⟩ := hm
  let := hbot
  let E : D ≃* Multiplicative V := QuotientGroup.quotientBot.symm.trans e
  have hE (g : K) (v w : D) (hw : (w : G) = g * (v : G) * (g : G)⁻¹) :
      (E w).toAdd = ρ (f g) (E v).toAdd := he g v w hw
  refine ⟨E,?_⟩
  intro g v
  let w : D := D.normalizerMonoidHom ⟨g,hn g.property⟩ (E.symm (Multiplicative.ofAdd v))
  have hw : (w : G) = g * (E.symm (Multiplicative.ofAdd v) : G) * (g : G)⁻¹ :=
    normalizerMonoidHom_apply_apply_coe D _ _
  have hh := hE g (E.symm (Multiplicative.ofAdd v)) w hw
  have hew : E w = Multiplicative.ofAdd (ρ (f g) v) := by
    apply Multiplicative.toAdd.injective
    simpa using hh
  rw [← hew, E.symm_apply_apply]
  exact hw

omit [Finite G] in
private theorem marked_fixed_zero {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V]
    (c : SourceConfiguration T L)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (ρ : Representation F SL(3,F) V)
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e) ρ)
    (hL : lineLocalSL F ≤ (L.subgroupOf (K c)).map (linearThreeActor e))
    (hv : ∀ v : V, (∀ g ∈ lineLocalSL F, ρ g v = v) → v = 0) :
    movedCoreOmega c ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨E,hE⟩ := coordinates hm
  apply bot_unique
  intro a ha
  let aa : movedCoreOmega c := ⟨a,ha.1⟩
  have he0 : (E aa).toAdd = 0 := by
    apply hv
    intro g hg
    obtain ⟨l,hl,rfl⟩ := hL hg
    have hh := hE l (E aa).toAdd
    have hcomm := mem_centralizer_iff.mp ha.2 l hl
    have hh' : (E.symm (Multiplicative.ofAdd (ρ (linearThreeActor e l) (E aa).toAdd)) : G) = a := by
      rw [hh]
      change (l : G) * (E.symm (E aa) : G) * (l : G)⁻¹ = a
      rw [E.symm_apply_apply]
      change (l : G) * a * (l : G)⁻¹ = a
      rw [hcomm, mul_inv_cancel_right]
    have hz := congrArg E (show E.symm (Multiplicative.ofAdd
        (ρ (linearThreeActor e l) (E aa).toAdd)) = aa from Subtype.ext hh')
    simpa using congrArg Multiplicative.toAdd hz
  have he1 : E aa = 1 := Multiplicative.toAdd.injective he0
  exact mem_bot.mpr (congrArg Subtype.val (E.map_eq_one_iff.mp he1))

omit [Finite G] in
private theorem marked_split_and_fixed {F V : Type*} [Field F]
    [AddCommGroup V] [Module F V]
    (c : SourceConfiguration T L)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (ρ : Representation F SL(3,F) V) [Subsingleton (H1 ρ)]
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e) ρ)
    (hL : lineLocalSL F ≤ (L.subgroupOf (K c)).map (linearThreeActor e))
    (hv : ∀ v : V, (∀ g ∈ lineLocalSL F, ρ g v = v) → v = 0) :
    movedCoreOmega c ⊔ (coreOmega c ⊓ centralizer (K c : Set G)) = coreOmega c ∧
    movedCoreOmega c ⊓ (coreOmega c ⊓ centralizer (K c : Set G)) = ⊥ ∧
    coreOmega c ⊓ centralizer (L : Set G) = coreOmega c ⊓ centralizer (K c : Set G) := by
  obtain ⟨E,hE⟩ := coordinates hm
  have hs : Function.Surjective (linearThreeActor e) :=
    e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hdisp (g : K c) (u : coreOmega c) :
      (g : G) * u * (g : G)⁻¹ * (u : G)⁻¹ ∈ movedCoreOmega c := by
    change ⁅(g : G),(u : G)⁆ ∈ ⁅coreOmega c,K c⁆
    rw [commutator_comm]
    exact commutator_mem_commutator g.property u.property
  have hfix := marked_fixed_zero c e ρ hm hL hv
  refine ⟨sup_centralizer_eq_of_conjugation_H1 _ _ _
      (le_normalizer_iff_commutator_le_left.mp (coreOmega_normalized c))
      _ hs ρ E hE (actor_kernel_centralizes c e) hdisp, ?_, ?_⟩
  · apply bot_unique
    exact (le_inf inf_le_left
      (inf_le_right.trans (inf_le_right.trans (centralizer_le c.le_component)))).trans_eq hfix
  exact centralizer_eq_of_conjugation_H1 _ _ _ _ c.le_component _ hs ρ E hE
    (actor_kernel_centralizes c e) hdisp hfix

omit [Finite G] in
theorem natural_omega_split_and_fixed {F : Type*} [Field F] [Finite F]
    (c : SourceConfiguration T L) (hF : 2 < Nat.card F)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := F) 3) ∨
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)))
    (hL : lineLocalSL F ≤ (L.subgroupOf (K c)).map (linearThreeActor e)) :
    movedCoreOmega c ⊔ (coreOmega c ⊓ centralizer (K c : Set G)) = coreOmega c ∧
    movedCoreOmega c ⊓ (coreOmega c ⊓ centralizer (K c : Set G)) = ⊥ ∧
    coreOmega c ⊓ centralizer (L : Set G) = coreOmega c ⊓ centralizer (K c : Set G) := by
  let := SLHigherNatural.H1_subsingleton_sl3_large_field hF
  rcases hm with hm | hm
  · exact marked_split_and_fixed c e _ hm hL Representation.SL3ParabolicNatural.line_fixed_zero
  · let := H1_prod_subsingleton (Representation.specialLinearNatural (k := F) 3)
      (Representation.specialLinearNatural (k := F) 3)
    exact marked_split_and_fixed c e _ hm hL Representation.SL3ParabolicNatural.line_prod_fixed_zero

theorem sylow_centralizer_eq_bot_of_natural_omega {F : Type*} [Field F] [Finite F]
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (hF : 2 < Nat.card F)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := F) 3) ∨
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)))
    (hL : lineLocalSL F ≤ (L.subgroupOf (K c)).map (linearThreeActor e)) :
    S c ⊓ centralizer (K c : Set G) = ⊥ := by
  have he := (natural_omega_split_and_fixed c hF e hm hL).2.2
  apply c.nonblock_sylow_centralizer_eq_bot
  apply le_antisymm
  · intro z hz
    exact ⟨hz.1, (he.le ⟨c.nonblock_omega_sylow_le_core_omega hf hz.1,hz.2⟩).2⟩
  · exact inf_le_inf_left _ (centralizer_le c.le_component)
omit [Finite G] in
private theorem msQ_le_sylow (c : SourceConfiguration T L) :
    msQ (K c) (c.I.pCoreIn 2) ≤ S c := by
  let J := K c ⊔ c.I.pCoreIn 2
  have hSR : S c ≤ normalizer (c.I.pCoreIn 2 : Set G) := by
    rw [c.core_join]
    exact (le_sup_right : S c ≤ c.I ⊔ S c).trans
      ((c.I ⊔ S c).le_normalizer.trans
        (normalizer_le_normalizer_characteristic_image (c.I ⊔ S c)
          (pCore 2 (c.I ⊔ S c : Subgroup G))))
  have hSJ : S c ≤ normalizer (J : Set G) :=
    (le_inf (inf_le_right.trans c.normalizer_component.le) hSR).trans
      (normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hJle : J ≤ K c ⊔ S c := sup_le le_sup_left
    ((c.core_sylow.le.trans inf_le_left).trans le_sup_right)
  have hcore : J.pCoreIn 2 ≤ (K c ⊔ S c).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes hJle
      (sup_le ((le_sup_left : K c ≤ J).trans J.le_normalizer) hSJ)
  have hm : msQ (K c) (c.I.pCoreIn 2) ≤ J.pCoreIn 2 :=
    le_normalizer_iff_commutator_le_left.mp ((le_sup_left : K c ≤ J).trans
      (J.le_normalizer.trans (normalizer_le_normalizer_characteristic_image J (pCore 2 J))))
  exact hm.trans (hcore.trans (c.block_join_core_le.trans (c.core_sylow.le.trans inf_le_left)))

theorem natural_omega_excludes_fourth {F : Type*} [Field F] [Finite F]
    (c : SourceConfiguration T L) (hf : generalizedFitting c.K = pCore 2 c.K)
    (hF : 2 < Nat.card F)
    (e : (K c ⧸ pCore 2 (K c)) ≃* SL(3,F))
    (hm : HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        (Representation.specialLinearNatural (k := F) 3) ∨
      HasSectionModel (K c) (movedCoreOmega c) ⊥ (linearThreeActor e)
        ((Representation.specialLinearNatural (k := F) 3).prod
          (Representation.specialLinearNatural (k := F) 3)))
    (hL : lineLocalSL F ≤ (L.subgroupOf (K c)).map (linearThreeActor e))
    (n : ℕ) (hn : 0 < n) :
    Nat.card (msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) : Subgroup G) ≠ 2 ^ (2*n) := by
  have hc := sylow_centralizer_eq_bot_of_natural_omega c hf hF e hm hL
  have hz : msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) = ⊥ :=
    bot_unique ((inf_le_inf_right _ (msQ_le_sylow c)).trans_eq hc)
  have hh : Nat.card (msQ (K c) (c.I.pCoreIn 2) ⊓ centralizer (K c : Set G) : Subgroup G) = 1 :=
    card_eq_one.mpr hz
  have hp : 1 < 2 ^ (2*n) := one_lt_pow₀ (by decide) (by omega)
  omega
end Nonblock
end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
