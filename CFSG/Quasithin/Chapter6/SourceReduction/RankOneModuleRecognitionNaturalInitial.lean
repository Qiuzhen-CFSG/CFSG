module
public import CFSG.Quasithin.Chapter6.Section01.SourceCentralLine
public import CFSG.Quasithin.Chapter1.Section02.Uniqueness.SourceKnownSimple
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard
public import Stellmacher.OmegaCenterCentralizer
public import Theory.GroupAction.FixedQuotientCentralizer
public import Theory.Representation.FirstCohomologyLinearTransport
public import CFSG.Quasithin.Chapter6.Section01.EscapeSize.Natural

/-!
# Removing the fixed kernel in the initial natural reduction

The fixed-quotient marking retains the isomorphism L/O₂(L) ≃ SL₂(2ⁿ),
the surjective coefficient map on the actual subgroup, its exact centralizer
kernel, and the conjugation equation. Once C_T(L)=1, that coefficient map
is bijective, giving the full natural action without a splitting assumption.

If C_G(Ω₁(Z(T))) escapes M, source 1.2.7 excludes a nonidentity L-fixed
central involution. The p-group center principle then gives C_T(L)=1.
Source 6.1.5 supplies this escape using an actual H-star witness. Thus the
last theorem proves the initial reduction from the separate earlier source
claims 6.1.4 and 6.1.5; neither earlier claim is asserted here. Their proof
and the final 6.1.27 assembly remain with the natural-reduction owner.

Source: Aschbacher–Smith, 6.1.4–6, printed pp.664–669, especially the
fixed-kernel and irreducibility argument in 6.1.6.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter6.Source
variable {G : Type*} [Group G]

/-- The source 6.1.4 conclusion, marked on the literal fixed-point quotient.
The kernel and surjectivity fields give an actual quotient equivalence,
and the actor equality identifies the original map through L/O₂(L). -/
def IsNaturalFixedQuotient (L B : Subgroup G) (n : ℕ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
    letI := ZMod.algebra F 2
    Nat.card F = 2 ^ n ∧
    ∃ e : (L ⧸ pCore 2 L) ≃* Matrix.SpecialLinearGroup (Fin 2) F,
    ∃ m : Representation.ConjugationQuotientModel L B
      ((Representation.specialLinearNatural (k := F) 2).restrictScalars (k := ZMod 2)),
      m.actor = e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 L))

/-- A trivial fixed kernel promotes the quotient model to the whole subgroup. -/
theorem IsNaturalFixedQuotient.natural_of_fixed_eq_bot
    {L B : Subgroup G} {n : ℕ} (h : IsNaturalFixedQuotient L B n)
    (hfixed : B ⊓ centralizer (L : Set G) = ⊥) : IsNaturalModule L B n := by
  obtain ⟨F, _, _, _, hF, e, m, he⟩ := h
  let := ZMod.algebra F 2
  have hker : m.quotient.ker = ⊥ := by
    rw [m.kernel]
    apply eq_bot_iff.mpr
    intro b hb
    exact Subtype.ext (mem_bot.mp (hfixed ▸ (show (b : G) ∈
      B ⊓ centralizer (L : Set G) from ⟨b.property, hb⟩)))
  let f := MulEquiv.ofBijective m.quotient
    ⟨m.quotient.ker_eq_bot_iff.mp hker, m.surjective⟩
  refine ⟨F, inferInstance, inferInstance, inferInstance, hF, e, f, ?_⟩
  intro l b
  have hm := m.equivariant l b
  rw [he] at hm
  have hh : f.symm (Multiplicative.ofAdd
      (Representation.specialLinearNatural 2 (e (QuotientGroup.mk' (pCore 2 L) l))
        (f b).toAdd)) = B.normalizerMonoidHom ⟨l, m.normalizes l.property⟩ b := by
    apply f.injective
    rw [f.apply_symm_apply]
    exact hm.symm
  exact congrArg Subtype.val hh

/-- Every nontrivial sublayer of a natural commutator layer is the whole layer. -/
theorem IsNaturalModule.layer_eq_of_nontrivial
    {L V W : Subgroup G} {n : ℕ} (hnatural : IsNaturalModule L (layer L V) n)
    (hWV : W ≤ V) (hne : layer L W ≠ ⊥) : layer L W = layer L V :=
  (hnatural.invariant_subgroup (layer L W)
    (Subgroup.commutator_mono hWV le_rfl)
    (normalizer_commutator_ge_right W L)).resolve_left hne

namespace Hypothesis611
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L M V : Subgroup G} {n : ℕ}
  (h : Hypothesis611 KnownSimple.IsKnownSimple T L M V n)
include h

/-- Uniqueness of LT excludes an L-fixed central involution when the
omega-centralizer escapes M. -/
theorem centralOmega_disjoint_of_omega_escape
    (hescape : ¬ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M) :
    Stellmacher.omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  have hstar : L ∈ Chapter1.LStar G (T : Subgroup G) := by
    refine ⟨h.local_mem.1.prop, ?_⟩
    intro K hK hLK
    exact le_antisymm (h.local_mem.1.2 hK hLK) hLK
  have hu := Chapter1.Section02.nonsolvable_uniqueness_knownSimple h.simpleQTKE T hstar
  have horbit : componentOrbit L (T : Subgroup G) = L :=
    le_antisymm (iSup_conjugates_le_of_le_normalizer L T L le_rfl
      h.sylow_normalizes_L) (le_componentOrbit L T)
  have huniq : ∀ N : Subgroup G, IsMaximalTwoLocal N →
      L ⊔ (T : Subgroup G) ≤ N → N = M := by
    intro N hN hLN
    have h1 := hu.normalizer_unique N hN
    have h2 := hu.normalizer_unique M h.maximal
    rw [horbit] at h1 h2
    exact (h1 hLN).trans (h2 (sup_le h.L_le h.sylow_le)).symm
  apply eq_bot_iff.mpr
  intro z hz
  by_contra hzone
  have hz1 : z ≠ 1 := fun heq => hzone (mem_bot.mpr heq)
  have hzT := (Stellmacher.mem_omegaOneCenterAmbient_iff _ _).mp hz.1
  have hCC : centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤
      centralizer ({z} : Set G) := centralizer_le (Set.singleton_subset_iff.mpr hz.1)
  obtain ⟨N, hCN, hN⟩ := Finite.exists_le_maximal
    (isTwoLocal_involution_centralizer (orderOf_eq_prime hzT.2.1 hz1))
  have hLC : L ≤ centralizer ({z} : Set G) := by
    intro l hl
    exact mem_centralizer_singleton_iff.mpr (hz.2 l hl)
  have hTC : (T : Subgroup G) ≤ centralizer ({z} : Set G) := by
    intro t ht
    exact mem_centralizer_singleton_iff.mpr (hzT.2.2 t ht)
  exact hescape ((hCC.trans hCN).trans_eq (huniq N hN ((sup_le hLC hTC).trans hCN)))

/-- The finite two-group center principle detects the entire Sylow centralizer. -/
theorem sylow_centralizer_eq_bot_of_omega_escape
    (hescape : ¬ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M) :
    (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ :=
  Stellmacher.inf_centralizer_eq_bot_of_omega_center _ _ T.isPGroup'
    h.sylow_normalizes_L (h.centralOmega_disjoint_of_omega_escape hescape)

/-- The initial natural action follows from its fixed quotient and omega escape. -/
theorem initial_natural_of_fixed_quotient_and_omega_escape
    (hquot : IsNaturalFixedQuotient L (layer L V) n)
    (hescape : ¬ centralizer
      (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) ≤ M) :
    IsNaturalModule L (layer L V) n ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  have hCT := h.sylow_centralizer_eq_bot_of_omega_escape hescape
  exact ⟨hquot.natural_of_fixed_eq_bot
    (bot_unique ((inf_le_inf_right _ h.layer_le_T).trans_eq hCT)), hCT⟩

/-- Source 6.1.6(1–2) from the literal earlier conclusions of 6.1.4 and 6.1.5.
The outside guard supplies the H-star witness required in the printed proof. -/
theorem initial_natural_of_earlier_sources
    (hout : Chapter3.HasMaximalOutside T M)
    (hquot : IsNaturalFixedQuotient L (layer L V) n)
    (hcentral : ∀ H ∈ Chapter3.HStar (T : Subgroup G) M,
      H ≤ centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    IsNaturalModule L (layer L V) n ∧
      (T : Subgroup G) ⊓ centralizer (L : Set G) = ⊥ := by
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside hout
  exact h.initial_natural_of_fixed_quotient_and_omega_escape hquot
    (fun hC => hH.1.2 ((hcentral H hH).trans hC))

end Hypothesis611
end CFSG.Quasithin.Chapter6.Source
