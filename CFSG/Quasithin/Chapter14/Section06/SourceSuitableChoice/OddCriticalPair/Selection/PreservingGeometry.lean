module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddCriticalPair.Selection.ReturnedGeometry

/-!
# Marking an endpoint that preserves the exchanged supports

The index-two product of the dihedral factors normalizes both covering
supports. Faithfulness on their moved sum forces a nontrivial endpoint actor
to move at least one support. If it moves the second, the original element
of T exchanging the factors carries it to the first. Conjugating all data
together preserves reverse containment and exclusion from Mc.

The application to the selected strict endpoint and the suitable-element
consumer is in Selection.StrictOrthogonalSource. No ambient fusion or
rank-eight point placement is assumed here.

Source: Aschbacher--Smith 14.6.13, printed pp.1031--1032.
-/

public section
open Subgroup Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
open OddNormalizer Chapter15.Section03.AbelianAmalgam
open Chapter15.Section03.AbelianAmalgam.GenerationOne
open Chapter13.Section08.ComponentSieve.AlternatingAndLinear.FourStructure.CriticalTransfer
open Chapter13.Section08.SourceCompletion Chapter13.Section08.CriticalGeometry
variable {G : Type*} [Group G]
variable {H U Z : Subgroup G} [IsElementaryAbelian 2 U]

theorem exchanged_supports_normalized
    (a : LocalQuotientAction H U Z) (T : Subgroup G)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (B : Subgroup G) (hBH : B ≤ H) (hB : actorImage H B ≤ actorImage H H0) :
    B ≤ normalizer (firstSupport a H1 : Set G) ∧
      B ≤ normalizer (firstSupport a H2 : Set G) := by
  constructor
  · apply supportPreimage_normalized a _ B hBH
    exact hB.trans (subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
      (actorImage_normalizes H1 H0 (d.first_le.trans d.zero_le) d.normalizes_first))
  · apply supportPreimage_normalized a _ B hBH
    exact hB.trans (subspaceCommutator_invariant_normalizer a.representation
      (le_subspaceStabilizer _ ⊤ (by intros; trivial))
      (actorImage_normalizes H2 H0 (d.second_le.trans d.zero_le) d.normalizes_second))

theorem exchanged_support_noncentral
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (T : Subgroup G) (p : ℕ) (H0 H1 H2 : Subgroup G)
    (d : ExchangedFactorSetup a T p H0 H1 H2)
    (B : Subgroup G) (hBH : B ≤ H) (hB : actorImage H B ≠ ⊥)
    (hf : ∀ g : H ⧸ pCore 2 H,
      (∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation g v = v) → g = 1) :
    ¬ ⁅firstSupport a H1,B⁆ ≤ Z ∨ ¬ ⁅firstSupport a H2,B⁆ ≤ Z := by
  classical
  by_cases h1 : ⁅firstSupport a H1,B⁆ ≤ Z
  · right
    intro h2
    apply hB
    apply _root_.eq_bot_iff.mpr
    intro t ht
    apply Subgroup.mem_bot.mpr
    apply hf t
    intro v hv
    have hv' : v ∈ subspaceCommutator a.representation ⊤ (actorImage H H1) ⊔
        subspaceCommutator a.representation ⊤ (actorImage H H2) := d.split.symm ▸ hv
    obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv'
    rw [map_add,support_fixed_of_commutator_le a hz _ B hBH h1 t ht x hx,
      support_fixed_of_commutator_le a hz _ B hBH h2 t ht y hy]
  · exact Or.inl h1

/-- A nontrivial endpoint actor preserving the two moved planes gives the
literal first-plane marking, after applying the original factor exchanger
if necessary. The same left conjugator retains reverse containment. -/
theorem four_geometry_of_preserving_endpoint
    (a : LocalQuotientAction H U Z) (hz : H ≤ centralizer (Z : Set G))
    (T : Subgroup G) (hTH : T ≤ H)
    (p : ℕ) (H0 H1 H2 : Subgroup G) (d : ExchangedFactorSetup a T p H0 H1 H2)
    (Mc : Subgroup G) (hHMc : H ≤ Mc)
    (g : G) (hout : g ∉ Mc) (hGH : U.map (MulAut.conj g).toMonoidHom ≤ H)
    (hrev : U ≤ H.map (MulAut.conj g).toMonoidHom)
    (hactor : actorImage H (U.map (MulAut.conj g).toMonoidHom) ≤ actorImage H H0)
    (hne : actorImage H (U.map (MulAut.conj g).toMonoidHom) ≠ ⊥)
    (hdim : Module.finrank (ZMod 2) (subspaceCommutator a.representation ⊤ ⊤) = 4)
    (hf : ∀ t : H ⧸ pCore 2 H,
      (∀ v ∈ subspaceCommutator a.representation ⊤ ⊤, a.representation t v = v) → t = 1) :
    Nonempty (FourCriticalGeometry a Mc H1) := by
  have hn := exchanged_supports_normalized a T p H0 H1 H2 d _ hGH hactor
  rcases exchanged_support_noncentral a hz T p H0 H1 H2 d _ hGH hne hf with hc | hc
  · exact ⟨⟨hdim,g,hout,le_inf hGH hn.1,hrev,hc⟩⟩
  · obtain ⟨x,hx,_,hex⟩ := d.exchanged
    let xH : H := ⟨x,hTH hx⟩
    have hU : U.map (MulAut.conj x).toMonoidHom = U :=
      mem_normalizer_iff_map_conj_eq.mp (a.normalizes xH.property)
    have hH : H.map (MulAut.conj x).toMonoidHom = H :=
      mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer xH.property)
    have heZ : Z.map (MulAut.conj x).toMonoidHom = Z :=
      mem_normalizer_iff_map_conj_eq.mp ((hz.trans (Subgroup.centralizer_le_normalizer _)) xH.property)
    have heS : (firstSupport a H2).map (MulAut.conj x).toMonoidHom = firstSupport a H1 := by
      unfold firstSupport
      rw [supportPreimage_conjugate a _ xH,moved_map_conjugate,
        ← actorImage_conjugate H2 (d.second_le.trans d.zero_le) xH,
        exchange_factor_inverse x hex]
    have hm (K : Subgroup G) : (K.map (MulAut.conj g).toMonoidHom).map
        (MulAut.conj x).toMonoidHom = K.map (MulAut.conj (x*g)).toMonoidHom :=
      (conjBy_mul K x g).symm
    refine ⟨⟨hdim,x*g,?_,?_,?_,?_⟩⟩
    · intro hh
      have he := Mc.mul_mem (Mc.inv_mem (hHMc xH.property)) hh
      exact hout (by simpa only [show (xH:G) = x from rfl,inv_mul_cancel_left] using he)
    · apply le_inf
      · have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hGH
        rwa [hm U,hH] at hh
      · have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hn.2
        rwa [hm U,map_equiv_normalizer_eq,heS] at hh
    · have hh := map_mono (f := (MulAut.conj x).toMonoidHom) hrev
      rwa [hU,hm H] at hh
    · intro hh
      apply hc
      apply (map_le_map_iff_of_injective (f := (MulAut.conj x).toMonoidHom)
        (MulAut.conj x).injective).mp
      rw [map_commutator,heS,hm U,heZ]
      exact hh
end CFSG.Quasithin.Chapter14.Section06.OddCriticalPair.Selection
