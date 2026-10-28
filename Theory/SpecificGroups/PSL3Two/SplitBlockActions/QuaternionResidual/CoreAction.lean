module

public import Theory.SpecificGroups.PSL3Two.SplitBlockActions.QuaternionResidual.Geometry
public import Theory.GroupTheory.QuaternionCentralProductOrthogonalAction.Kernel
public import Theory.GroupTheory.CharacteristicCentralizerFusion
public import Theory.GroupTheory.QuaternionProductOrderFourCentralizer
public import Theory.GroupTheory.QuaternionCentralProductTransport
public import Theory.SpecificGroups.PSL3Two.InvolutionConjugacy

/-!
# Controlling the extra two-core through the binary block

An element centralizing the quaternion core U need not centralize the source
sixteen merely because it is invisible on U/Z(U). Here the actual block L
supplies the missing control. A normalizer of L fixing V pointwise acts
trivially on L/V, because C_L(V) ≤ V. Conjugating the selected involution a
into U then puts its displacement in [V,a]. The same displacement centralizes
U, so the distinct-center geometry forces it to vanish.

The actual quotient L/V ≃ PSL₃(2) supplies the conjugator: its involutions
form one class, and the quaternion core contains an involution outside V.
Finally, the kernel of Aut(U) → Aut(U/Z(U)) consists of inner automorphisms.
Correcting by U therefore reduces every extra two-core element to the
centralizer calculation, on the literal N(A)/C(A).

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, proof of
14.4.4, printed p.1007, using 12.8.4 and 12.8.9–11. The normalization of
L and the displacement-line separation are explicit earlier-source inputs;
neither U = O₂(H) nor a self-centralizing-core condition is assumed.
-/

open Subgroup
open scoped commutatorElement
namespace Subgroup.QuaternionResidual
variable {G : Type*} [Group G]

/-- Normalization of the actual block controls displacement on the extra generator. -/
public theorem centralizes_of_block_conjugacy
    (L V U : Subgroup G) (hVU : V ≤ U)
    (hLV : L ≤ normalizer (V : Set G))
    (hfaith : L ⊓ centralizer (V : Set G) ≤ V)
    (a : G) (haU : a ∈ normalizer (U : Set G))
    (hdisj : Disjoint (centralizer (U : Set G)) ⁅V, zpowers a⁆)
    (g : G) (hg : g ∈ L) (hga : MulAut.conj g a ∈ U)
    (c : G) (hcU : c ∈ centralizer (U : Set G))
    (hcL : c ∈ normalizer (L : Set G)) : Commute c a := by
  have hcV : c ∈ centralizer (V : Set G) := centralizer_le hVU hcU
  have hcg : ⁅g⁻¹, c⁆ ∈ V := by
    apply hfaith
    constructor
    · have h := (mem_normalizer_iff.mp hcL g).mp hg
      change g⁻¹ * c * (g⁻¹)⁻¹ * c⁻¹ ∈ L
      simpa only [mul_assoc, inv_inv] using L.mul_mem (L.inv_mem hg) h
    · have hn := normalizer_le_normalizer_centralizer V (hLV (L.inv_mem hg))
      have h := (mem_normalizer_iff.mp hn c).mp hcV
      exact (centralizer (V : Set G)).mul_mem h
        ((centralizer (V : Set G)).inv_mem hcV)
  have hfix : c * (g * a * g⁻¹) = (g * a * g⁻¹) * c := (hcU _ hga).symm
  have he : ⁅c, a⁆ = ⁅⁅g⁻¹, c⁆⁻¹, a⁆ := by
    have hh : ⁅g⁻¹, c⁆ * (c * a * c⁻¹) * ⁅g⁻¹, c⁆⁻¹ = a := by
      calc
        _ = g⁻¹ * (c * (g * a * g⁻¹)) * c⁻¹ * g := by
          simp only [commutatorElement_def]; group
        _ = a := by rw [hfix]; group
    have hh' : c * a * c⁻¹ = ⁅g⁻¹, c⁆⁻¹ * a * ⁅g⁻¹, c⁆ := by
      have h := congrArg (fun x => ⁅g⁻¹, c⁆⁻¹ * x * ⁅g⁻¹, c⁆) hh
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using h
    calc
      ⁅c, a⁆ = (⁅g⁻¹, c⁆⁻¹ * a * ⁅g⁻¹, c⁆) * a⁻¹ := by
        change (c * a * c⁻¹) * a⁻¹ = _
        rw [hh']
      _ = ⁅⁅g⁻¹, c⁆⁻¹, a⁆ := by simp only [commutatorElement_def, inv_inv]
  have hm : ⁅c, a⁆ ∈ ⁅V, zpowers a⁆ := by
    rw [he]
    exact commutator_mem_commutator (V.inv_mem hcg) (mem_zpowers a)
  have hcent : ⁅c, a⁆ ∈ centralizer (U : Set G) := by
    have hn := normalizer_le_normalizer_centralizer U haU
    have h := (mem_normalizer_iff.mp hn c⁻¹).mp
      ((centralizer (U : Set G)).inv_mem hcU)
    simpa only [commutatorElement_def, mul_assoc] using
      (centralizer (U : Set G)).mul_mem hcU h
  exact commutatorElement_eq_one_iff_mul_comm.mp (disjoint_def.mp hdisj hcent hm)


variable [Finite G]

/-- The quotient marking supplies the conjugator in the actual block. -/
public theorem exists_block_conjugate_mem_core
    (L V U : Subgroup G) (hUL : U ≤ L) (hVU : V ≤ U)
    [(V.subgroupOf L).Normal]
    (d : QuaternionCentralProductData U) (hV : Nat.card V = 8)
    (e : (L ⧸ V.subgroupOf L) ≃* Matrix.PSL3Two.PSL)
    (a : G) (haL : a ∈ L) (ha : a ^ 2 = 1) (hout : a ∉ U) :
    ∃ g ∈ L, MulAut.conj g a ∈ U := by
  let dL := d.map (subgroupOfEquivOfLe hUL).symm
  have hVU' : V.subgroupOf L ≤ U.subgroupOf L := comap_mono hVU
  have hproper : ¬ U.subgroupOf L ≤ V.subgroupOf L := by
    intro h
    have hc := card_le_of_le h
    rw [Nat.card_congr (subgroupOfEquivOfLe hUL).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe (hVU.trans hUL)).toEquiv,
      d.card, hV] at hc
    omega
  have hclass (x y : L ⧸ V.subgroupOf L) (hx : orderOf x = 2)
      (hy : orderOf y = 2) : IsConj x y := by
    have h := Matrix.PSL3Two.isConj_of_orderOf_eq_two (e x) (e y)
      ((e.orderOf_eq x).trans hx) ((e.orderOf_eq y).trans hy)
    have h' : IsConj (e.symm (e x)) (e.symm (e y)) := e.symm.toMonoidHom.map_isConj h
    simpa only [MulEquiv.symm_apply_apply] using h'
  have ha' : orderOf (⟨a, haL⟩ : L) = 2 := orderOf_eq_prime (Subtype.ext ha)
    (fun h => hout (by simpa only [show a = 1 from congrArg Subtype.val h] using U.one_mem))
  obtain ⟨g, hg⟩ := (quaternion_involution_lifts_and_cover_of_single_quotient_class
    (V.subgroupOf L) (U.subgroupOf L) dL hVU' hproper hclass).2 ⟨a, haL⟩ ha'
  exact ⟨g, g.property, hg⟩

/-- The source displacement line is disjoint from the quaternion center. -/
public theorem core_centralizer_fixes_A_of_block
    (L V U A : Subgroup G) (hUL : U ≤ L) (hVU : V ≤ U)
    [(V.subgroupOf L).Normal]
    (d : QuaternionCentralProductData U) (hV : Nat.card V = 8)
    (e : (L ⧸ V.subgroupOf L) ≃* Matrix.PSL3Two.PSL)
    (hfaith : L ⊓ centralizer (V : Set G) ≤ V)
    (hblock : centralizer (V : Set G) ≤ normalizer (L : Set G))
    (a : G) (haL : a ∈ L) (ha : a ^ 2 = 1) (hout : a ∉ U)
    (haU : a ∈ normalizer (U : Set G))
    (hdisj : Disjoint (U ⊓ centralizer (U : Set G)) ⁅V, zpowers a⁆)
    (hA : A = zpowers a ⊔ ⁅U, zpowers a⁆) :
    centralizer (U : Set G) ≤ centralizer (A : Set G) := by
  have hLV : L ≤ normalizer (V : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hVU.trans hUL)).mp inferInstance
  have hmove : ⁅V, zpowers a⁆ ≤ U :=
    ((le_normalizer_iff_commutator_le_left).mp
      (zpowers_le.mpr (hLV haL))).trans hVU
  have hd : Disjoint (centralizer (U : Set G)) ⁅V, zpowers a⁆ := by
    apply disjoint_def.mpr
    intro x hx hm
    exact disjoint_def.mp hdisj ⟨hmove hm, hx⟩ hm
  obtain ⟨g, hgL, hga⟩ := exists_block_conjugate_mem_core L V U hUL hVU d hV e
    a haL ha hout
  intro c hc
  have hca := centralizes_of_block_conjugacy L V U hVU hLV hfaith a haU hd
    g hgL hga c hc (hblock (centralizer_le hVU hc))
  have hAspan : A ≤ U ⊔ zpowers a := by
    rw [hA]
    exact sup_le le_sup_right (commutator_le_sup U (zpowers a))
  have hsup : U ⊔ zpowers a ≤ centralizer ({c} : Set G) := by
    apply sup_le
    · intro x hx
      exact mem_centralizer_singleton_iff.mpr (hc x hx)
    · exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hca.symm)
  intro x hx
  exact mem_centralizer_singleton_iff.mp (hsup (hAspan hx))


/-- An inner correction separates the actual two-core from the quaternion core. -/
public theorem image_core_intersection_eq
    (U A Q K : Subgroup G) (d : QuaternionCentralProductData U)
    (hUQ : U ≤ Q) (hUK : U ≤ K)
    (hUN : U ≤ normalizer (A : Set G))
    (hQN : Q ≤ normalizer (U : Set G))
    (hquotient : ∀ q : Q,
      quotientAut (center U) (U.normalizerMonoidHom (inclusion hQN q)) = 1)
    (hfix : centralizer (U : Set G) ≤ centralizer (A : Set G)) :
    image A ((K ⊓ normalizer (A : Set G)) ⊓ Q) = image A U := by
  apply le_antisymm
  · rintro x ⟨q, hq, rfl⟩
    have hqQ : (q : G) ∈ Q := hq.2
    let qU : normalizer (U : Set G) := ⟨q, hQN hqQ⟩
    obtain ⟨u, hu⟩ := (d.quotientAut_eq_one_iff_inner
      (U.normalizerMonoidHom qU)).mp (hquotient ⟨q, hqQ⟩)
    have huc (y : G) (hy : y ∈ U) :
        (u : G) * y * (u : G)⁻¹ = (q : G) * y * (q : G)⁻¹ := by
      exact congrArg Subtype.val (DFunLike.congr_fun hu (⟨y, hy⟩ : U))
    have hc : (u : G)⁻¹ * q ∈ centralizer (U : Set G) := by
      intro y hy
      calc
        y * ((u : G)⁻¹ * q) = (u : G)⁻¹ * ((u : G) * y * (u : G)⁻¹) * q := by group
        _ = (u : G)⁻¹ * ((q : G) * y * (q : G)⁻¹) * q := by rw [huc y hy]
        _ = ((u : G)⁻¹ * q) * y := by group
    let uN : normalizer (A : Set G) := ⟨u, hUN u.property⟩
    refine ⟨uN, u.property, ?_⟩
    exact QuotientGroup.eq.mpr (hfix hc)
  · exact image_mono A (le_inf (le_inf hUK hUN) hUQ)

end Subgroup.QuaternionResidual
