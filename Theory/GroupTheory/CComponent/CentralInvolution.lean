module

public import Theory.GroupTheory.CComponent.CommutatorDichotomy
public import Theory.GroupTheory.CComponent.FittingCentralizer
public import Theory.PPrimeCore

/-!
# From a moved C-component to an ordinary component

Conjugation by an element that inverts a normal subgroup is central in its
automorphism image. Thus its commutators centralize that subgroup. If the
same element centralizes O₂(G), those commutators centralize F(G).
A C-component containing a nonsolvable subgroup L = [L,z] cannot take the
solvable-radical branch of A.3.3(7); it lies in [G,z], and hence centralizes
F(G). A.3.3(1) makes it quasisimple.

This is the promotion step in Aschbacher–Smith 2.3.9(6), printed p.526.
It distinguishes C-components from ordinary quasisimple components.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G]

/-- Commutators with an inverter centralize the inverted normal subgroup. -/
theorem commutator_top_le_centralizer_of_inverts (B : Subgroup G) [B.Normal]
    (z : G) (hinv : ∀ b ∈ B, z * b * z⁻¹ = b⁻¹) :
    ⁅(⊤ : Subgroup G), zpowers z⁆ ≤ centralizer (B : Set G) := by
  let f : G →* MulAut B := MulAut.conjNormal
  have hf : ∀ b : B, f z b = b⁻¹ := fun b => Subtype.ext (hinv b b.property)
  have hc : zpowers (f z) ≤ centralizer (f.range : Set (MulAut B)) := by
    apply zpowers_le.mpr
    intro a _
    apply MulEquiv.ext
    intro b
    change a (f z b) = f z (a b)
    rw [hf, hf, map_inv]
  have hm : (⁅(⊤ : Subgroup G), zpowers z⁆).map f = ⊥ := by
    rw [map_commutator, ← MonoidHom.range_eq_map, MonoidHom.map_zpowers, commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.mpr hc
  have hk : ⁅(⊤ : Subgroup G), zpowers z⁆ ≤ f.ker := (Subgroup.map_eq_bot_iff _).mp hm
  intro x hx b hb
  have he := congrArg (fun a : MulAut B => ((a ⟨b, hb⟩ : B) : G)) (hk hx)
  change x * b * x⁻¹ = b at he
  exact (mul_inv_eq_iff_eq_mul.mp he).symm

/-- Centralizing the two-core and inverting the odd core makes all
commutators with z centralize the Fitting subgroup. -/
theorem commutator_top_le_centralizer_fitting [Finite G] (z : G)
    (hcentral : ∀ b ∈ pCore 2 G, b * z = z * b)
    (hinv : ∀ b ∈ pPrimeCore 2 G, z * b * z⁻¹ = b⁻¹) :
    ⁅(⊤ : Subgroup G), zpowers z⁆ ≤ centralizer (fittingSubgroup G : Set G) := by
  have hodd := commutator_top_le_centralizer_of_inverts (pPrimeCore 2 G) z hinv
  have htwo : ⁅(⊤ : Subgroup G), zpowers z⁆ ≤ centralizer (pCore 2 G : Set G) := by
    have hz : zpowers z ≤ centralizer (pCore 2 G : Set G) :=
      zpowers_le.mpr hcentral
    exact (commutator_mono le_rfl hz).trans (commutator_le_right _ _)
  apply subgroup_le_centralizer_fitting_of_le_centralizer_pCores
  intro q
  by_cases hq : q.val.val = 2
  · simpa only [hq] using htwo
  · have hqo : pCore q.val.val G ≤ pPrimeCore 2 G := by
      apply le_sSup
      refine ⟨inferInstance, ?_⟩
      obtain ⟨n, hn⟩ := (pCore_isPGroup (p := q.val.val) (G := G)).exists_card_eq
      rw [hn]
      exact ((Nat.coprime_primes Nat.prime_two
        (Nat.prime_of_mem_primeFactors q.val.property)).mpr (Ne.symm hq)).pow_right _
    exact hodd.trans (centralizer_le hqo)

/-- The C-component containing a moved nonsolvable subgroup is an actual
quasisimple component. All action assumptions refer to the original z. -/
theorem component_of_moved_subgroup [Finite G] {L D : Subgroup G}
    (hD : D.IsCComponent) (hLD : L ≤ D) (hL : ¬ Group.IsSolvable L)
    (z : G) (hmoved : L = ⁅L, zpowers z⁆)
    (hcentral : ∀ b ∈ pCore 2 G, b * z = z * b)
    (hinv : ∀ b ∈ pPrimeCore 2 G, z * b * z⁻¹ = b⁻¹) :
    IsComponent G D := by
  have hDC : D ≤ ⁅D, zpowers z⁆ := by
    rcases hD.commutator_le_radical_or_eq_iSup_conjugates (zpowers z) with hr | hm
    · have hLR : L ≤ solvableRadical G := by
        rw [hmoved]
        exact (commutator_mono hLD le_rfl).trans hr
      exact (hL (Group.isSolvable_of_isSolvable_injective
        (inclusion_injective hLR))).elim
    · exact (le_iSup_conjugates D (zpowers z)).trans_eq hm.symm
  have hc : D ≤ centralizer (fittingSubgroup G : Set G) :=
    (hDC.trans (commutator_mono le_top le_rfl)).trans
      (commutator_top_le_centralizer_fitting z hcentral hinv)
  exact ⟨hD.subnormal, hD.isQuasisimple_of_fitting_centralizes (le_centralizer_iff.mp hc)⟩

end Theory.GroupTheory
