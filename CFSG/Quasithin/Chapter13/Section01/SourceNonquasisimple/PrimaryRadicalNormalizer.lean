module
public import CFSG.Quasithin.Chapter3.Section02.RadicalCentralization.PrimaryRadical
public import CFSG.Quasithin.Chapter1.Section03.Radical.Structure.SourceNormality
public import CFSG.Quasithin.Chapter1.Section03.Radical.Normalizers.Basic
public import Theory.GroupTheory.PGroup.OmegaCoprimeAction

/-!
# The primary radical normalizes the canonical radical core

Let R=O₂(Ξ_p(L)T) and I_p=O^{p′}(O∞(L)). The known-simple local
quotient theorem identifies I_p/O₂(I_p) with O_p(L/O₂(L)). In the actual
higher homocyclic branch this primary factor is abelian.

The canonical radical maps onto its first omega layer. Since
[Ξ_p(L),R]≤O₂(Ξ_p(L))≤O₂(L), the actual action of R fixes that layer.
Coprime action therefore makes R fix the full primary factor, yielding
[I_p,R]≤O₂(L). The original Sylow hypothesis gives O₂(L)≤R, so I_p
normalizes R. This applies to the primary factor alone; it requires no
self-centralizing p-core and no single-prime condition on all of L.

The normalizer conclusion supplies the I_p≤N_G(R) input for the residual
Y=N_L(R)^∞ in the original radical-centralization argument. Faithfulness,
residual generation and characteristic-normalizer control remain with
that source assembly.

Source: Aschbacher--Smith, the coprime omega step in the proof of1.3.8,
printed p.513; the higher primary radical in3.2.14, p.585, and13.1.4(5), p.867.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
open Chapter1 Chapter1.Section02 Chapter1.RadicalNormalizers
universe u
variable {G : Type u} [Group G] [Finite G]

private theorem radicalCore_fixes_primary_core
    {p : ℕ} [Fact p.Prime] (ho : Odd p) (L T : Subgroup G)
    (hT : T ≤ normalizer (L : Set G))
    (hc : IsMulCommutative (pCore p (XiQuotient L))) :
    let R := radicalCore p L T
    let hRL : R ≤ normalizer (L : Set G) :=
      (radicalCore_le_join p L T).trans (sup_le ((XiP_le p L).trans L.le_normalizer) hT)
    let ρ := (quotientAut (pCore 2 L)).comp
      (L.normalizerMonoidHom.comp (inclusion hRL))
    ∀ r : R, ∀ x : pCore p (XiQuotient L), ρ r (x : XiQuotient L) = x := by
  dsimp only
  let R := radicalCore p L T
  have hRL : R ≤ normalizer (L : Set G) :=
    (radicalCore_le_join p L T).trans (sup_le ((XiP_le p L).trans L.le_normalizer) hT)
  let ρ : R →* MulAut (XiQuotient L) := (quotientAut (pCore 2 L)).comp
    (L.normalizerMonoidHom.comp (inclusion hRL))
  let Q := pCore p (XiQuotient L)
  let σ : R →* MulAut Q := (MulAut.characteristic Q).comp ρ
  let := hc
  have hcop : Nat.Coprime (Nat.card R) (Nat.card Q) :=
    IsPGroup.coprime_card_of_ne 2 p (by intro hp; exact (by decide : ¬ Odd 2) (hp.symm ▸ ho))
      R Q (radicalCore_isTwoGroup p L T) pCore_isPGroup
  have hfix : ∀ r : R, ∀ x ∈ omega Q (p := p) 1, σ r x=x := by
    intro r x hx
    apply Subtype.ext
    change ρ r (x : XiQuotient L) = x
    have hximage : (x : XiQuotient L) ∈ (xiPIn p L).map (QuotientGroup.mk' (pCore 2 L)) := by
      rw [xiPIn_map_quotient ho]
      exact mem_map.mpr ⟨x,hx,rfl⟩
    obtain ⟨z,hz,he⟩ := mem_map.mp hximage
    have hzX : (z : G) ∈ XiP p L := mem_map.mpr ⟨z,hz,rfl⟩
    have hcomm := commutator_radicalCore_le p hT
    have hcore := pCoreIn_mono_of_normalizes (p := 2) (XiP_le p L)
      (L.le_normalizer.trans (normalizer_le_normalizer_XiP p L))
    have hm : ⁅(r : G),(z : G)⁆ ∈ L.pCoreIn 2 := by
      apply hcore
      apply hcomm
      rw [commutator_comm]
      exact commutator_mem_commutator r.property hzX
    let b : normalizer (L : Set G) := inclusion hRL r
    let c : L := L.normalizerMonoidHom b z * z⁻¹
    have hcmem : c ∈ pCore 2 L := by
      obtain ⟨w,hw,heq⟩ := mem_map.mp hm
      have hwc : w=c := Subtype.ext heq
      exact hwc ▸ hw
    have hq := (QuotientGroup.eq_one_iff c).mpr hcmem
    change QuotientGroup.mk' (pCore 2 L) c=1 at hq
    dsimp only [c] at hq
    rw [map_mul,map_inv] at hq
    rw [← he]
    change quotientAut (pCore 2 L) (L.normalizerMonoidHom b) (QuotientGroup.mk' (pCore 2 L) z)=_
    rw [quotientAut_apply_mk]
    exact mul_inv_eq_one.mp hq
  have ht := OmegaAction.fixes_of_fixes_omega_one pCore_isPGroup σ hcop hfix
  intro r x
  exact congrArg (fun f : MulAut Q => (f x : XiQuotient L)) (ht r)

/-- The original primary radical commutes with R modulo O₂(L), using only
its actual homocyclic quotient, without a single-prime condition on L. -/
theorem primaryRadical_commutator_radicalCore_le_of_homocyclic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) {a : ℕ}
    (e : Nonempty ((Chapter3.RadicalCentralization.primaryRadical p L ⧸
      pCore 2 (Chapter3.RadicalCentralization.primaryRadical p L)) ≃*
      Multiplicative (Fin 2 → ZMod (p^a)))) :
    ⁅Chapter3.RadicalCentralization.primaryRadical p L,radicalCore p L T⁆ ≤ L.pCoreIn 2 := by
  let I := Chapter3.RadicalCentralization.primaryRadical p L
  let R := radicalCore p L T
  have hIL : I ≤ L := map_subtype_le _
  have hT := radicalLocal_invariant_source hL (uniqueness_local_quotient_sqtk hG hL.2.2) hn
  have hRL : R ≤ normalizer (L : Set G) :=
    (radicalCore_le_join p L T).trans (sup_le ((XiP_le p L).trans L.le_normalizer) hT)
  let ρ : R →* MulAut (XiQuotient L) := (quotientAut (pCore 2 L)).comp
    (L.normalizerMonoidHom.comp (inclusion hRL))
  let eq := Chapter3.RadicalCentralization.primaryRadicalQuotientEquiv hG T hL ho
  let ep := eq.symm.trans e.some
  have hc : IsMulCommutative (pCore p (XiQuotient L)) :=
    ⟨⟨fun x y => ep.injective (by rw [map_mul,map_mul,mul_comm])⟩⟩
  have ht : ∀ r : R, ∀ x : pCore p (XiQuotient L), ρ r (x : XiQuotient L)=x :=
    radicalCore_fixes_primary_core ho L T hT hc
  rw [commutator_comm]
  apply commutator_le.mpr
  intro r hr i hi
  let iL : L := ⟨i,hIL hi⟩
  let b : normalizer (L : Set G) := inclusion hRL ⟨r,hr⟩
  let x : pCore p (XiQuotient L) := eq (QuotientGroup.mk' (pCore 2 I) ⟨i,hi⟩)
  have hx : (x : XiQuotient L)=QuotientGroup.mk' (pCore 2 L) iL :=
    Chapter3.RadicalCentralization.primaryRadicalQuotientEquiv_apply_mk hG T hL ho ⟨i,hi⟩
  have hfix := ht ⟨r,hr⟩ x
  rw [hx] at hfix
  change quotientAut (pCore 2 L) (L.normalizerMonoidHom b) (QuotientGroup.mk' (pCore 2 L) iL)=_ at hfix
  rw [quotientAut_apply_mk] at hfix
  let c : L := L.normalizerMonoidHom b iL * iL⁻¹
  have hc : c ∈ pCore 2 L := by
    apply (QuotientGroup.eq_one_iff c).mp
    change QuotientGroup.mk' (pCore 2 L) c=1
    dsimp only [c]
    rw [map_mul,map_inv,hfix,mul_inv_cancel]
  exact mem_map.mpr ⟨c,hc,rfl⟩

/-- The actual I_p normalizes O₂(Ξ_p(L)T). The two-core of L already lies
in R by the original Sylow hypothesis, so the quotient commutator bound lifts. -/
theorem primaryRadical_normalizes_radicalCore_of_homocyclic
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {L : Subgroup G} (hL : L ∈ Chapter1.L G T)
    (hn : ¬ IsQuasisimple (XiQuotient L)) {p : ℕ} [Fact p.Prime]
    (ho : Odd p) {a : ℕ}
    (e : Nonempty ((Chapter3.RadicalCentralization.primaryRadical p L ⧸
      pCore 2 (Chapter3.RadicalCentralization.primaryRadical p L)) ≃*
      Multiplicative (Fin 2 → ZMod (p^a)))) :
    Chapter3.RadicalCentralization.primaryRadical p L ≤ normalizer (radicalCore p L T : Set G) := by
  have hT := radicalLocal_invariant_source hL (uniqueness_local_quotient_sqtk hG hL.2.2) hn
  exact le_normalizer_iff_commutator_le_right.mpr
    ((primaryRadical_commutator_radicalCore_le_of_homocyclic hG T hL hn ho e).trans
      (twoCore_le_radicalCore p hL.2.1 hT))

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple
