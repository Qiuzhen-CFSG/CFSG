module
public import Theory.Representation.BinaryConjugationSection.NormalizingActors
public import Theory.GroupTheory.PCoreLocalSetup
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Fully moved sections with trivial invertible commutant

An actor commuting with B on E induces an operator on E/C_E(B). If the
marked representation has trivial invertible commutant, the operator is
identity. The three-subgroup lemma and E=[E,B] remove its displacement
into the fixed kernel. Thus the actor fixes all of E, including that kernel.

For an overgroup containing the full normalizing Sylow, this applies to its
two-core. A self-centralizing core then contains E in its center. The J₄
natural-plus-dual comparison uses this in Aschbacher--Smith 10.2.9, p.750.
-/

public noncomputable section
open Subgroup
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {B E : Subgroup G} [IsElementaryAbelian 2 E]
  {ρ : Representation (ZMod 2) B W}

theorem centralizes_of_trivial_commutant
    (d : BinaryConjugationSection B E (E ⊓ centralizer (B : Set G)) ρ)
    (htriv : ∀ f : W ≃ₗ[ZMod 2] W, (∀ b w, f (ρ b w) = ρ b (f w)) →
      f = LinearEquiv.refl _ _)
    (Q : Subgroup G) (hQB : Q ≤ normalizer (B : Set G))
    (hQE : Q ≤ normalizer (E : Set G))
    (hcomm : ⁅Q,B⁆ ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E) :
    Q ≤ centralizer (E : Set G) := by
  have hQZ : Q ≤ normalizer (↑(E ⊓ centralizer (B : Set G) : Subgroup G) : Set G) :=
    (le_inf hQE (hQB.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf
  obtain ⟨η,hη⟩ := d.exists_original_quotient_action hQE hQZ
  have hco (q : Q) (b : B) :
      Commute (E.normalizerMonoidHom (inclusion hQE q))
        (E.normalizerMonoidHom (inclusion d.normalized b)) := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [←map_commutatorElement]
    change ⁅inclusion hQE q,inclusion d.normalized b⁆ ∈ E.normalizerMonoidHom.ker
    rw [normalizerMonoidHom_ker]
    exact hcomm (commutator_mem_commutator q.property b.property)
  have hηcomm (q : Q) (b : B) (w : W) : η q (ρ b w) = ρ b (η q w) := by
    obtain ⟨e,he⟩ := d.onto (Multiplicative.ofAdd w)
    have hw : (d.coordinates e).toAdd = w := congrArg Multiplicative.toAdd he
    rw [←hw]
    rw [←d.equivariant,hη,hη,←d.equivariant]
    apply congrArg (fun e : E => (d.coordinates e).toAdd)
    exact DFunLike.congr_fun (hco q b).eq e
  have hfix (q : Q) (w : W) : η q w = w := by
    let f := LinearMap.GeneralLinearGroup.toLinearEquiv (η.asGroupHom q)
    have he := htriv f (hηcomm q)
    exact congrArg (fun e : W ≃ₗ[ZMod 2] W => e w) he
  have hQEfix : ⁅Q,E⁆ ≤ centralizer (B : Set G) := by
    apply commutator_le.mpr
    intro q hq e he
    let a : E := E.normalizerMonoidHom (inclusion hQE ⟨q,hq⟩) ⟨e,he⟩
    have ha : d.coordinates a = d.coordinates ⟨e,he⟩ := by
      apply Multiplicative.toAdd.injective
      exact (hη ⟨q,hq⟩ ⟨e,he⟩).symm.trans (hfix ⟨q,hq⟩ _)
    have hk : d.coordinates (a * (⟨e,he⟩ : E)⁻¹) = 1 := by
      rw [map_mul,map_inv,ha,mul_inv_cancel]
    exact ((d.coordinates_eq_one_iff _).mp hk).2
  have hzero : ⁅⁅E,B⁆,Q⁆ = ⊥ :=
    commutator_commutator_eq_bot_of_rotate
      (commutator_eq_bot_iff_le_centralizer.mpr (by rwa [commutator_comm B Q]))
      (commutator_eq_bot_iff_le_centralizer.mpr hQEfix)
  rw [hmove] at hzero
  exact le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hzero)
end Representation.BinaryConjugationSection
namespace Representation.BinaryConjugationSection
open Subgroup
variable {G W : Type*} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]
  {B E : Subgroup G} [IsElementaryAbelian 2 E]
  {ρ : Representation (ZMod 2) B W}

theorem card_le_overgroup_core_center_of_trivial_commutant
    (d : BinaryConjugationSection B E (E ⊓ centralizer (B : Set G)) ρ)
    (htriv : ∀ f : W ≃ₗ[ZMod 2] W, (∀ b w, f (ρ b w) = ρ b (f w)) →
      f = LinearEquiv.refl _ _)
    (S : Sylow 2 G) (hSB : (S : Subgroup G) ≤ normalizer (B : Set G))
    (hSE : (S : Subgroup G) ≤ normalizer (E : Set G))
    (hcore : B.pCoreIn 2 ≤ centralizer (E : Set G)) (hmove : ⁅E,B⁆ = E)
    (K : Subgroup G) (hBK : B ≤ K) (hSK : (S : Subgroup G) ≤ K)
    (hC : centralizer (pCore 2 K : Set K) ≤ pCore 2 K) :
    Nat.card E ≤ Nat.card (center (pCore 2 K)) := by
  let Q := (pCore 2 K).map K.subtype
  have hQS : Q ≤ S := by
    have h := pCore_isPGroup.le_sylow_of_normal (S.subtype hSK)
    simpa only [Q,Sylow.coe_subtype,map_subgroupOf_eq_of_le hSK] using
      map_mono (f := K.subtype) h
  have hBQ : B ≤ normalizer (Q : Set G) := by
    have h : (⊤ : Subgroup K) ≤ normalizer (pCore 2 K : Set K) := le_normalizer_of_normal
    have hh := (map_mono (f := K.subtype) h).trans (le_normalizer_map K.subtype)
    rw [←MonoidHom.range_eq_map,K.range_subtype] at hh
    exact hBK.trans hh
  have hcomm : ⁅Q,B⁆ ≤ B.pCoreIn 2 :=
    le_pCoreIn_of_normalizes
      ((pCore_isPGroup.map K.subtype).to_le (le_normalizer_iff_commutator_le_left.mp hBQ))
      (le_normalizer_iff_commutator_le_right.mp (hQS.trans hSB))
      (normalizer_commutator_ge_right Q B)
  have hQC : Q ≤ centralizer (E : Set G) :=
    d.centralizes_of_trivial_commutant htriv Q (hQS.trans hSB) (hQS.trans hSE)
      (hcomm.trans hcore) hmove
  have hEC : E ≤ centralizer (Q : Set G) := le_centralizer_iff.mp hQC
  have hEK : E ≤ K := d.section_le.trans hBK
  have hEZ : E.subgroupOf K ≤ (center (pCore 2 K)).map (pCore 2 K).subtype := by
    intro x hx
    have hxc : x ∈ centralizer (pCore 2 K : Set K) := by
      intro y hy
      exact Subtype.ext (hEC hx y (mem_map_of_mem K.subtype hy))
    have hxQ := hC hxc
    exact ⟨⟨x,hxQ⟩,mem_center_iff.mpr (fun y => Subtype.ext (hxc y y.property)),rfl⟩
  have hh := card_le_of_le hEZ
  simpa only [card_map_of_injective (pCore 2 K).subtype_injective,
    Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv] using hh
end Representation.BinaryConjugationSection
