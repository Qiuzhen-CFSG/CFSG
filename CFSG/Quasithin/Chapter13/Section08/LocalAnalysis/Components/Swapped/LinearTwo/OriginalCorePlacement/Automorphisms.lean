module

public import Theory.SpecificGroups.Alternating.FiveBorelCentralFactor
public import Theory.GroupTheory.AutomorphismSquareRank
public import CFSG.Quasithin.Chapter13.Section08.LocalAnalysis.Components.Swapped.LinearTwo.BorelDiagonal.BinaryBorel.Actions
public import Theory.SpecificGroups.SL2.CardFourEquiv

/-!
# Inner automorphisms from the marked binary Borel quotient

An automorphism of A₅ fixing a Sylow normalizer modulo its Sylow four-group
is inner: the five-letter realization of Aut(A₅) makes every odd actor
move a cubic element modulo that four-group. For a square of PSL₂(4),
the component automorphism decomposition reduces to this calculation on
both factors. The exchanging case cannot fix the product Borel quotient,
since each of its cyclic factors has order three.

These are the automorphism calculations used to place O₂(L₁T)* inside K₀*
in Aschbacher--Smith, 13.8.16(1), printed pp.952--953 (PDF pp.969--970).
-/

public section
open Subgroup
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.OriginalCorePlacement
open Theory.SpecificGroups.Alternating
local notation "A5" => alternatingGroup (Fin 5)
local notation "S5" => Equiv.Perm (Fin 5)

private theorem five_inner (S : Sylow 2 A5) (a : MulAut A5)
    (ha : ∀ x ∈ normalizer (S : Set A5), a x * x⁻¹ ∈ (S : Subgroup A5)) :
    ∃ z : A5, a = MulAut.conj z := by
  obtain ⟨t, ht⟩ := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
    5 (by decide) (by decide) |>.2 a
  have htapp (x : A5) : (a x : S5) = t * (x : S5) * t⁻¹ := by
    rw [← ht]
    rfl
  obtain ⟨i, hi⟩ := FiveBorelOvergroups.sylow_normalizer_eq_stabilizer S
  let B : Subgroup S5 := A5 ⊓ MulAction.stabilizer S5 i
  have hmap : (normalizer (S : Set A5)).map (A5).subtype = B := by
    rw [hi]
    ext x
    exact ⟨fun ⟨y, hy, he⟩ => he ▸ ⟨y.property, hy⟩,
      fun ⟨hx, hxi⟩ => ⟨⟨x, hx⟩, hxi, rfl⟩⟩
  have hn : t ∈ normalizer (B : Set S5) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    apply eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      rw [← hmap] at hx ⊢
      obtain ⟨x, hx, rfl⟩ := hx
      refine ⟨a x, ?_, htapp x⟩
      have hd := (show (S : Subgroup A5) ≤ normalizer (S : Set A5) from le_normalizer)
        (ha x hx)
      have hh := (normalizer (S : Set A5)).mul_mem hd hx
      rw [inv_mul_cancel_right] at hh
      exact hh
    · exact (card_map_of_injective (MulAut.conj t).injective).ge
  have hti : t i = i := by
    rw [show B = A5 ⊓ MulAction.stabilizer S5 i from rfl,
      FiveBorelCentralFactor.even_stabilizer_normalizer] at hn
    exact hn
  have hteven : t ∈ A5 := by
    apply Equiv.Perm.mem_alternatingGroup.mpr
    by_contra hodd
    obtain ⟨b, hb, hcube, hne⟩ := FiveBorelCentralFactor.odd_actor_cubic_witness i t hti hodd
    have hb' : (⟨b, hb.1⟩ : A5) ∈ normalizer (S : Set A5) := by
      rw [hi]
      exact hb.2
    have hd := (S : Subgroup A5).inv_mem (ha ⟨b, hb.1⟩ hb')
    let c : (S : Subgroup A5) := ⟨(a ⟨b, hb.1⟩ * (⟨b, hb.1⟩ : A5)⁻¹)⁻¹, hd⟩
    have hc : ((c : A5) : S5) = ⁅b, t⁆ := by
      change (((a ⟨b, hb.1⟩ : A5) : S5) * b⁻¹)⁻¹ = _
      rw [htapp]
      simp [commutatorElement_def, mul_assoc]
    have hc3 : c ^ 3 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, hc] using hcube
    have hc1 : c = 1 := by
      apply (S.isPGroup'.powEquiv (by decide : Nat.Coprime 2 3)).injective
      exact hc3.trans (one_pow 3).symm
    exact hne (hc.symm.trans (congrArg (fun c : (S : Subgroup A5) => ((c : A5) : S5)) hc1))
  refine ⟨⟨t, hteven⟩, ?_⟩
  apply MulEquiv.ext
  intro x
  exact Subtype.ext (htapp x)

open CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo

private theorem factor_inner {Q : Type*} [Group Q] [Finite Q]
    (e : Q ≃* A5) (S : Sylow 2 Q) (a : MulAut Q)
    (ha : ∀ x ∈ BinaryBorel.borel S, a x * x⁻¹ ∈ (S : Subgroup Q)) :
    ∃ z : Q, a = MulAut.conj z := by
  let S' := S.mapSurjective (f := e.toMonoidHom) e.surjective
  let a' := MulAut.congr e a
  have hm : (BinaryBorel.borel S).map e.toMonoidHom = normalizer (S' : Set A5) :=
    map_equiv_normalizer_eq _ e
  obtain ⟨z, hz⟩ := five_inner S' a' (by
    intro x hx
    rw [← hm] at hx
    obtain ⟨x, hx, rfl⟩ := hx
    have hh := mem_map_of_mem e.toMonoidHom (ha x hx)
    change e (a x * x⁻¹) ∈ (S' : Subgroup A5) at hh
    change e (a (e.symm (e x))) * (e x)⁻¹ ∈ (S' : Subgroup A5)
    rw [e.symm_apply_apply]
    rw [map_mul, map_inv] at hh
    exact hh)
  refine ⟨e.symm z, ?_⟩
  apply (MulAut.congr e).injective
  rw [show MulAut.congr e a = a' from rfl, hz]
  ext x
  simp [MulAut.congr_apply, MulAut.conj_apply]

/-- Fixing the actual binary Borel modulo its two-core forces inner action. -/
theorem binary_inner {Q : Type*} [Group Q] [Finite Q]
    [Theory.GroupTheory.IsQuasisimple Q]
    (e : Q ≃* A5) (hZ : center Q = ⊥)
    (hmodel : ClassicalGroup.IsPSL Q 2 4)
    (S : Sylow 2 (Q × Q)) (a : MulAut (Q × Q))
    (ha : ∀ x ∈ BinaryBorel.borel S, a x * x⁻¹ ∈ (S : Subgroup (Q × Q))) :
    ∃ z : Q × Q, a = MulAut.conj z := by
  rcases Theory.GroupTheory.AutomorphismSquare.normal_form hZ a with
    ⟨a₁, a₂, rfl⟩ | ⟨a₁, a₂, rfl⟩
  · have hf (x : Q) (hx : x ∈ BinaryBorel.borel (BinaryBorel.firstSylow S)) :
        a₁ x * x⁻¹ ∈ (BinaryBorel.firstSylow S : Subgroup Q) := by
      have hh := ha (x, 1) (by rw [BinaryBorel.borel_eq_prod]; exact ⟨hx, one_mem _⟩)
      rw [BinaryBorel.sylow_eq_prod] at hh
      exact hh.1
    have hs (x : Q) (hx : x ∈ BinaryBorel.borel (BinaryBorel.secondSylow S)) :
        a₂ x * x⁻¹ ∈ (BinaryBorel.secondSylow S : Subgroup Q) := by
      have hh := ha (1, x) (by rw [BinaryBorel.borel_eq_prod]; exact ⟨one_mem _, hx⟩)
      rw [BinaryBorel.sylow_eq_prod] at hh
      exact hh.2
    obtain ⟨z₁, rfl⟩ := factor_inner e _ a₁ hf
    obtain ⟨z₂, rfl⟩ := factor_inner e _ a₂ hs
    exact ⟨(z₁, z₂), rfl⟩
  · have hb : BinaryBorel.borel (BinaryBorel.firstSylow S) ≤
        (BinaryBorel.firstSylow S : Subgroup Q) := by
      intro x hx
      have hh := ha (x, 1) (by rw [BinaryBorel.borel_eq_prod]; exact ⟨hx, one_mem _⟩)
      rw [BinaryBorel.sylow_eq_prod] at hh
      have hh' : x⁻¹ ∈ (BinaryBorel.firstSylow S : Subgroup Q) := by
        have hh1 : a₁ 1 * x⁻¹ ∈ (BinaryBorel.firstSylow S : Subgroup Q) := hh.1
        rw [map_one, one_mul] at hh1
        exact hh1
      exact inv_mem_iff.mp hh'
    have htop : pCore 2 (BinaryBorel.borel (BinaryBorel.firstSylow S)) = ⊤ := by
      rw [BinaryBorel.twoCore]
      exact top_unique (fun x _ => hb x.property)
    have hc := BinaryBorel.torus_card (n := 2) (by decide) hmodel (BinaryBorel.firstSylow S)
    change Nat.card (_ ⧸ pCore 2 _) = 3 at hc
    rw [htop] at hc
    have hz : Nat.card (BinaryBorel.borel (BinaryBorel.firstSylow S) ⧸
        (⊤ : Subgroup (BinaryBorel.borel (BinaryBorel.firstSylow S)))) = 1 := by simp
    omega

end CFSG.Quasithin.Chapter13.Section08.Components.Swapped.LinearTwo.OriginalCorePlacement
