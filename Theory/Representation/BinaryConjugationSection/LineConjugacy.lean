module
public import Theory.Representation.BinaryConjugationSection.InvariantImages
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Theory.GroupTheory.CharacteristicCentralizerFusion

/-!
# Lifting transitivity through a binary central kernel

For a literal binary section U/Z, assume an actor H is transitive on
nonzero quotient vectors, normalizes Q, and |Z| = 2 with [U,Q] ≤ Z.
If Q moves U and centralizes Z, then C_U(Q) = Z. Every nonzero
quotient fiber is a Q-orbit, so H is transitive on the actual points
outside Z and on the order-two subgroups outside Z.

The final transport lemma recovers the same conjugates of any subgroup
normalized by N_G(Z) from equality of the marked line conjugates.
This retains the central kernel and the actual conjugator needed in
Aschbacher–Smith, *The Classification of Quasithin Groups*, 13.8.31(1),
printed pp.964–965.
-/

public section
open Subgroup Representation
open scoped commutatorElement
namespace Representation.BinaryConjugationSection
variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]
  {H U Z : Subgroup G} {ρ : Representation (ZMod 2) H W}
  (d : BinaryConjugationSection H U Z ρ)

include d in
/-- Quotient transitivity and nontrivial central commutators determine the fixed subgroup. -/
theorem centralizer_eq_kernel_of_transitive
    (Q : Subgroup G) (hHQ : H ≤ normalizer (Q : Set G))
    (hZQ : Z ≤ centralizer (Q : Set G)) (hmove : ⁅U,Q⁆ ≠ ⊥)
    (htrans : ∀ u v : W, u ≠ 0 → v ≠ 0 → ∃ h : H, ρ h u = v) :
    U ⊓ centralizer (Q : Set G) = Z := by
  apply le_antisymm ?_ (le_inf d.kernel_le hZQ)
  intro x hx
  by_contra hxZ
  have hx0 : (d.coordinates ⟨x,hx.1⟩).toAdd ≠ 0 :=
    fun hh => hxZ ((d.coordinates_eq_one_iff _).mp hh)
  have himage : d.imageSpace (centralizer (Q : Set G)) = ⊤ := by
    apply top_unique
    intro w _
    by_cases hw : w = 0
    · exact hw ▸ (d.imageSpace _).zero_mem
    obtain ⟨h,hh⟩ := htrans _ w hx0 hw
    rw [←hh]
    exact d.imageSpace_apply_mem _ h
      ((hHQ.trans (normalizer_le_normalizer_centralizer Q)) h.property) _
      ((d.mem_imageSpace_iff _ _).mpr ⟨⟨x,hx.1⟩,hx.2,rfl⟩)
  apply hmove
  exact commutator_eq_bot_iff_le_centralizer.mpr
    ((d.le_sup_kernel_of_image_top _ himage).trans (sup_le le_rfl hZQ))

include d in
/-- Correct a quotient conjugator by an element of Q to match the actual points. -/
theorem exists_conjugator_of_transitive_binary_kernel
    (Q : Subgroup G) (hQH : Q ≤ H) (hHQ : H ≤ normalizer (Q : Set G))
    (hZQ : Z ≤ centralizer (Q : Set G)) (hZ : Nat.card Z = 2)
    (hcomm : ⁅U,Q⁆ ≤ Z) (hmove : ⁅U,Q⁆ ≠ ⊥)
    (htrans : ∀ u v : W, u ≠ 0 → v ≠ 0 → ∃ h : H, ρ h u = v)
    (x y : U) (hx : (x:G) ∉ Z) (hy : (y:G) ∉ Z) :
    ∃ h : H, (h:G) * x * (h:G)⁻¹ = y := by
  have hfixed := d.centralizer_eq_kernel_of_transitive Q hHQ hZQ hmove htrans
  have hx0 : (d.coordinates x).toAdd ≠ 0 :=
    fun hh => hx ((d.coordinates_eq_one_iff _).mp hh)
  have hy0 : (d.coordinates y).toAdd ≠ 0 :=
    fun hh => hy ((d.coordinates_eq_one_iff _).mp hh)
  obtain ⟨a,ha⟩ := htrans _ _ hx0 hy0
  let z : U := ⟨(a:G)*x*(a:G)⁻¹,
    (mem_normalizer_iff.mp (d.normalized a.property) x).mp x.property⟩
  have hzcoord : d.coordinates z = d.coordinates y :=
    Multiplicative.toAdd.injective ((d.equivariant a x).trans ha)
  by_cases hzy : z = y
  · exact ⟨a,congrArg Subtype.val hzy⟩
  have hzZ : (z:G) ∉ Z := by
    intro hm
    exact hy ((d.coordinates_eq_one_iff y).mp
      (hzcoord.symm.trans ((d.coordinates_eq_one_iff z).mpr hm)))
  have hzfix : (z:G) ∉ centralizer (Q : Set G) := by
    intro hh
    exact hzZ (hfixed ▸ (show (z:G) ∈ U ⊓ centralizer (Q : Set G) from ⟨z.property,hh⟩))
  obtain ⟨q,hq,hqz⟩ : ∃ q ∈ Q, q*(z:G) ≠ (z:G)*q := by
    simpa only [mem_centralizer_iff,not_forall,exists_prop,SetLike.mem_coe] using hzfix
  have hc : ⁅q,(z:G)⁆ ∈ Z := hcomm (by
    rw [commutator_comm]
    exact commutator_mem_commutator hq z.property)
  have hc1 : ⁅q,(z:G)⁆ ≠ 1 := fun hh => hqz (commutatorElement_eq_one_iff_mul_comm.mp hh)
  have hyz : ((y*z⁻¹:U):G) ∈ Z := by
    apply (d.coordinates_eq_one_iff _).mp
    rw [map_mul,map_inv,hzcoord,mul_inv_cancel]
  have hyz1 : ((y*z⁻¹:U):G) ≠ 1 := by
    intro hh
    have he : y*z⁻¹ = 1 := Subtype.ext hh
    exact hzy (mul_inv_eq_one.mp he).symm
  obtain ⟨_,_,hunique⟩ := (Nat.card_eq_two_iff' (1:Z)).mp hZ
  have he : ⁅q,(z:G)⁆ = ((y*z⁻¹:U):G) := congrArg Subtype.val
    ((hunique ⟨_,hc⟩ (fun hh => hc1 (congrArg Subtype.val hh))).trans
      (hunique ⟨_,hyz⟩ (fun hh => hyz1 (congrArg Subtype.val hh))).symm)
  refine ⟨⟨q,hQH hq⟩ * a,?_⟩
  have he' : q*(z:G)*q⁻¹ = y := by
    have hh := congrArg (fun t : G => t*(z:G)) he
    simpa only [commutatorElement_def,Subgroup.coe_mul,Subgroup.coe_inv,
      mul_assoc,inv_mul_cancel,mul_one] using hh
  change (q*(a:G))*(x:G)*(q*(a:G))⁻¹ = (y:G)
  rw [←he']
  dsimp [z]
  group


include d in
/-- The same correction aligns actual order-two subgroups outside the kernel. -/
theorem exists_line_conjugator_of_transitive_binary_kernel [Finite G]
    (Q : Subgroup G) (hQH : Q ≤ H) (hHQ : H ≤ normalizer (Q : Set G))
    (hZQ : Z ≤ centralizer (Q : Set G)) (hZ : Nat.card Z = 2)
    (hcomm : ⁅U,Q⁆ ≤ Z) (hmove : ⁅U,Q⁆ ≠ ⊥)
    (htrans : ∀ u v : W, u ≠ 0 → v ≠ 0 → ∃ h : H, ρ h u = v)
    (A B : Subgroup G) (hA : Nat.card A = 2) (hB : Nat.card B = 2)
    (hAU : A ≤ U) (hBU : B ≤ U) (hAZ : ¬ A ≤ Z) (hBZ : ¬ B ≤ Z) :
    ∃ h : H, A.conjBy (h:G) = B := by
  obtain ⟨x,hx,hxZ⟩ := SetLike.not_le_iff_exists.mp hAZ
  obtain ⟨y,hy,hyZ⟩ := SetLike.not_le_iff_exists.mp hBZ
  obtain ⟨h,hh⟩ := d.exists_conjugator_of_transitive_binary_kernel Q hQH hHQ
    hZQ hZ hcomm hmove htrans ⟨x,hAU hx⟩ ⟨y,hBU hy⟩ hxZ hyZ
  obtain ⟨_,_,hall⟩ := (Nat.card_eq_two_iff' (1:A)).mp hA
  have hx1 : (⟨x,hx⟩:A) ≠ 1 := fun he => hxZ (by rw [show x = 1 from congrArg Subtype.val he]; exact Z.one_mem)
  refine ⟨h,eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨u,hu,rfl⟩
    by_cases hu1 : u = 1
    · simp [hu1]
    have he : u = x := congrArg Subtype.val
      ((hall ⟨u,hu⟩ (fun he => hu1 (congrArg Subtype.val he))).trans (hall _ hx1).symm)
    change (h:G)*u*(h:G)⁻¹ ∈ B
    rw [he,hh]
    exact hy
  · change Nat.card B ≤ Nat.card (A.map (MulAut.conj (h:G)).toMonoidHom)
    rw [card_map_of_injective (MulAut.conj (h:G)).injective,hA,hB]


end Representation.BinaryConjugationSection

namespace Subgroup
variable {G : Type*} [Group G]

/-- A marked line determines every associated subgroup normalized by its normalizer. -/
theorem conjugates_eq_of_line_conjugates_eq
    (Z U : Subgroup G) (hn : normalizer (Z : Set G) ≤ normalizer (U : Set G))
    (a b : G) (he : Z.conjBy a = Z.conjBy b) :
    U.conjBy a = U.conjBy b := by
  have hz : b⁻¹*a ∈ normalizer (Z : Set G) :=
    mem_normalizer_iff_map_conj_eq.mpr (conjBy_inv_mul_cancel Z he.symm)
  have hu : U.conjBy (b⁻¹*a) = U := mem_normalizer_iff_map_conj_eq.mp (hn hz)
  have hh := congrArg (fun S : Subgroup G => S.conjBy b) hu
  simpa only [conjBy_conjBy,mul_inv_cancel_left] using hh
end Subgroup
