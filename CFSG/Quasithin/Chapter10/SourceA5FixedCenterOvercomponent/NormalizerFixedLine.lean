module
public import CFSG.Quasithin.Chapter10.SourceBaumannBlocks
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.AlternatingFiveSylowFixed

/-!
# The fixed-vector obstruction for a normal original A5 block

A full Sylow two-subgroup of an A5 block fixes at most two vectors in its
natural layer. If a normalizing actor has all its Sylow commutators fixing
a specified nonzero vector, every conjugate of that vector lies in the same
fixed line, so the actor fixes it. For the original Chapter 10 component,
Sylow normalization puts these commutators in Y intersect L, hence in
Y intersect M. The original bound Y intersect M ≤ O₂(H) then applies.

The final source consumer excludes normality of L in C_G(v₂) when the
actual actor Y moves v₁. Its remaining data are the marked source vectors,
actor normalization, and the source two-core bound; no automorphism
classification input or extra recognition callback is introduced.

Source: Aschbacher–Smith, 10.2.1, printed p.743, using the natural A5
Sylow-fixed line from C.1.13(c).
-/

public section

open Subgroup Theory.GroupTheory Stellmacher
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter10
open ChapterC Chapter3.Section02

/-- A commutator-centralized vector with only one nonidentity Sylow-fixed
possibility is fixed by every actor normalizing its module. -/
theorem normalizer_fixes_of_small_fixed_commutator
    {G : Type*} [Group G] [Finite G] (V R Y : Subgroup G)
    (hYV : Y ≤ normalizer (V : Set G))
    (hsmall : Nat.card (V ⊓ centralizer (R : Set G) : Subgroup G) ≤ 2)
    {v : G} (hv : v ∈ V) (hvR : v ∈ centralizer (R : Set G))
    (hcomm : ⁅R,Y⁆ ≤ centralizer ({v} : Set G)) :
    Y ≤ centralizer ({v} : Set G) := by
  by_cases hv1 : v = 1
  · subst v
    intro y hy
    exact mem_centralizer_singleton_iff.mpr (by simp)
  let F := V ⊓ centralizer (R : Set G)
  change Nat.card F ≤ 2 at hsmall
  have hvF : v ∈ F := ⟨hv,hvR⟩
  have hFne : F ≠ ⊥ := fun he => hv1 (mem_bot.mp (he ▸ hvF))
  have hFcard : Nat.card F = 2 := by
    have hh := F.one_lt_card_iff_ne_bot.mpr hFne
    omega
  obtain ⟨z,_,hunique⟩ := (Nat.card_eq_two_iff' (1:F)).mp hFcard
  intro y hy
  have hyvV : y*v*y⁻¹ ∈ V := (mem_normalizer_iff.mp (hYV hy) v).mp hv
  have hyvR : y*v*y⁻¹ ∈ centralizer (R : Set G) := by
    intro r hr
    have hr' := hvR r hr
    have hc2 : ⁅y⁻¹,r⁆ ∈ centralizer ({v} : Set G) := by
      rw [commutator_comm] at hcomm
      exact hcomm (commutator_mem_commutator (Y.inv_mem hy) hr)
    have hh := mem_centralizer_singleton_iff.mp hc2
    rw [commutatorElement_def, inv_inv] at hh
    have he : (y⁻¹*r*y)*v = v*(y⁻¹*r*y) := by
      have ht := congrArg (fun a => a*r) hh
      calc
        (y⁻¹*r*y)*v = (y⁻¹*r*y)*(r⁻¹*(r*v)) := by group
        _ = (y⁻¹*r*y)*(r⁻¹*(v*r)) := by rw [hr']
        _ = ((y⁻¹*r*y*r⁻¹)*v)*r := by group
        _ = (v*(y⁻¹*r*y*r⁻¹))*r := ht
        _ = v*(y⁻¹*r*y) := by group
    calc
      r*(y*v*y⁻¹) = y*((y⁻¹*r*y)*v)*y⁻¹ := by group
      _ = y*(v*(y⁻¹*r*y))*y⁻¹ := by rw [he]
      _ = (y*v*y⁻¹)*r := by group
  have hyv1 : y*v*y⁻¹ ≠ 1 := by
    intro he
    apply hv1
    have hh := congrArg (MulAut.conj y⁻¹) he
    simpa [MulAut.conj_apply,mul_assoc] using hh
  have hvne : (⟨v,hvF⟩:F) ≠ 1 := fun he => hv1 (congrArg Subtype.val he)
  have hyvne : (⟨y*v*y⁻¹,hyvV,hyvR⟩:F) ≠ 1 :=
    fun he => hyv1 (congrArg Subtype.val he)
  have he : y*v*y⁻¹ = v := congrArg Subtype.val
    ((hunique _ hyvne).trans (hunique _ hvne).symm)
  exact mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp he)

/-- The actual normal A5 block and full Sylow fixed line force the actor to
fix the prescribed vector as soon as its block intersection does. -/
theorem alternatingFive_normalizer_fixes_sylow_vector
    {G : Type*} [Group G] [Finite G] (L R Y : Subgroup G)
    (hL : IsAlternatingBlock L 5) (hR : Chapter1.IsSylowIn 2 R L)
    (hYL : Y ≤ normalizer (L : Set G)) (hRY : R ≤ normalizer (Y : Set G))
    {v : G} (hv : v ∈ (blockU L).map L.subtype)
    (hvR : v ∈ centralizer (R : Set G))
    (hintersection : Y ⊓ L ≤ centralizer ({v} : Set G)) :
    Y ≤ centralizer ({v} : Set G) := by
  obtain ⟨P,hP⟩ := hR
  have hsmall : Nat.card ((blockU L).map L.subtype ⊓ centralizer (R : Set G) : Subgroup G) ≤ 2 := by
    let f : ((blockU L).map L.subtype ⊓ centralizer (R : Set G) : Subgroup G) →
        (blockU L ⊓ centralizer (P : Set L) : Subgroup L) := fun x =>
      ⟨⟨x,(map_subtype_le (blockU L)) x.property.1⟩,by
        refine ⟨?_,?_⟩
        · obtain ⟨l,hl,he⟩ := x.property.1
          exact (Subtype.ext he : l = ⟨x,_⟩) ▸ hl
        · intro p hp
          apply Subtype.ext
          exact x.property.2 p (hP ▸ mem_map_of_mem L.subtype hp)⟩
    have hf : Function.Injective f := by
      intro x y he
      exact Subtype.ext (congrArg (fun z : (blockU L ⊓ centralizer (P : Set L) : Subgroup L) =>
        ((z : L) : G)) he)
    exact (Nat.card_le_card_of_injective f hf).trans (hL.sylow_fixed_card_le_two P)
  apply normalizer_fixes_of_small_fixed_commutator ((blockU L).map L.subtype) R Y
    (hYL.trans (normalizer_le_normalizer_characteristic_image L (blockU L)))
    hsmall hv hvR
  have hRL : R ≤ L := hP ▸ map_subtype_le _
  exact (le_inf (le_normalizer_iff_commutator_le_right.mp hRY)
    ((commutator_mono hRL le_rfl).trans
      (le_normalizer_iff_commutator_le_left.mp hYL))).trans hintersection

/-- The original full Sylow intersection fixes the original A5 layer vector.
Thus an actor whose intersection with M fixes that vector cannot move it
while it normalizes the original component. -/
theorem source_a5_normalizer_fixes_original_sylow_vector
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (Y : Subgroup G) (hYL : Y ≤ normalizer (L : Set G))
    (hTY : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (Y : Set G))
    {v : G} (hv : v ∈ (blockU L).map L.subtype)
    (hvT : v ∈ centralizer ((T : Subgroup G) ⊓ L : Set G))
    (hYM : Y ⊓ D.maximalLocal ≤ centralizer ({v} : Set G)) :
    Y ≤ centralizer ({v} : Set G) := by
  have hL := (source_a5_original_block_of_baumann_not_controlled D e hn hout).2.2
  have hLH : L ≤ localJoin T L := (le_componentOrbit L T).trans le_sup_left
  have hc : (L.subgroupOf (localJoin T L)).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  have hS : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ L) L :=
    Chapter1.Section02.IndexTwo.isSylowIn_inf_of_subnormal
      ⟨T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right),
        map_subgroupOf_eq_of_le le_sup_right⟩ hLH hc.subnormal
  have hST : (T : Subgroup G) ⊓ L ≤ (T : Subgroup G) ⊓ normalizer (L : Set G) :=
    inf_le_inf_left _ L.le_normalizer
  apply alternatingFive_normalizer_fixes_sylow_vector L ((T : Subgroup G) ⊓ L) Y
    hL hS hYL (hST.trans hTY) hv hvT
  exact (inf_le_inf_left _ ((le_componentOrbit L T).trans (localOrbit T L).le_normalizer)).trans hYM

/-- Applied to the actual source centralizer, a moving actor excludes the
case in which the original component is normal in that centralizer. The core
bound is the original Y∩M≤O₂(H), and core centralization is supplied by v₁∈W. -/
theorem source_a5_element_centralizer_not_normalizes_of_moved_vector
    {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
    (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal)
    (H Y : Subgroup G) (v₁ v₂ : G)
    (hYX : Y ≤ centralizer ({v₂} : Set G))
    (hTY : (T : Subgroup G) ⊓ normalizer (L : Set G) ≤ normalizer (Y : Set G))
    (hv₁ : v₁ ∈ (blockU L).map L.subtype)
    (hv₁T : v₁ ∈ centralizer ((T : Subgroup G) ⊓ L : Set G))
    (hYM : Y ⊓ D.maximalLocal ≤ H.pCoreIn 2)
    (hcore : H.pCoreIn 2 ≤ centralizer ({v₁} : Set G))
    (hmove : ¬ Y ≤ centralizer ({v₁} : Set G)) :
    ¬ centralizer ({v₂} : Set G) ≤ normalizer (L : Set G) := by
  intro hXL
  exact hmove (source_a5_normalizer_fixes_original_sylow_vector D e hn hout Y
    (hYX.trans hXL) hTY hv₁ hv₁T (hYM.trans hcore))

end CFSG.Quasithin.Chapter10
