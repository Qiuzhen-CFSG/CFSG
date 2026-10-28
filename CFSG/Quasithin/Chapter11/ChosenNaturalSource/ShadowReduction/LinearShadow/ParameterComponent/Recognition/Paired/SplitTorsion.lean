module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.HallTorus
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanPlane


/-!
# The two actual Hall torsion lines in the original Cartan plane

The Hall factor is cyclic of order 2^n(H)-1 by HallTorus. Its literal
Ω₁(Oₚ(A intersect K)) is therefore a line of order p. The already constructed
Sylow actor moves it to a disjoint conjugate line in the same original
Ω₁(Oₚ(A)). That subgroup has order p², so multiplication identifies these
two lines with the entire subgroup, preserving both ambient inclusions.
Index two of the component normalizer proves that the same actor exchanges
the two lines. The constructed prime-order moved point is retained as well.

This discharges the direct-product description of the actual prime torsion,
without assuming abelianness or a product decomposition of the whole Hall
subgroup. Preservation by the actor's square is weaker than centralization:
the fixed-point construction is still a separate local obligation. Recognition
at the true generation minimum also remains explicit. Both stay with the
parameter-component owner; qt-d-1222-shadow-linear-geometry retains final
source discharge, including the genuine preceding 11.0.4 clauses.
Source: Aschbacher--Smith 11.3.5(2), printed pp.771--772.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

namespace Paired
/-- The literal omega-core of a cyclic group has order p when p divides its order. -/
theorem primeTorsion_card_of_cyclic (B : Subgroup G) [IsCyclic B]
    (p : ℕ) [Fact p.Prime] (hd : p ∣ Nat.card B) :
    Nat.card (primeTorsion B p) = p := by
  let : IsMulCommutative B := inferInstance
  let : IsElementaryAbelian p (primeTorsion B p) := primeTorsion_elementary B p
  let j := inclusion (primeTorsion_le B p)
  let : IsCyclic (primeTorsion B p) := isCyclic_of_injective j (inclusion_injective _)
  have hdiv : Nat.card (primeTorsion B p) ∣ p := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p p _
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdiv with he | he
  · exact (primeTorsion_ne_bot B p hd (Subgroup.card_eq_one.mp he)).elim
  · exact he

private theorem prime_plane_split (A B : Subgroup G) [IsCyclic B]
    (hBA : B ≤ A) (hAB : A ≤ normalizer (B : Set G))
    (p : ℕ) [Fact p.Prime] (hdp : p ∣ Nat.card B)
    [IsElementaryAbelian p (primeTorsion A p)]
    (hq : Nat.card (primeTorsion A p) = p ^ 2)
    (t : G) (ht : t ∈ normalizer (A : Set G))
    (hdis : Disjoint B (B.map (MulAut.conj t).toMonoidHom))
    (hsq : t ^ 2 ∈ normalizer (B : Set G)) :
    let C := primeTorsion B p
    let E := C.map (MulAut.conj t).toMonoidHom
    Nat.card C = p ∧ Nat.card E = p ∧ Disjoint C E ∧
      primeTorsion A p = C ⊔ E ∧
      E.map (MulAut.conj t).toMonoidHom = C ∧
      ∃ e : C × E ≃* primeTorsion A p,
        ∀ x y, (e (x,y) : G) = (x : G) * (y : G) := by
  let C := primeTorsion B p
  let E := C.map (MulAut.conj t).toMonoidHom
  have hc : Nat.card C = p := primeTorsion_card_of_cyclic B p hdp
  have he : Nat.card E = p := (card_map_of_injective (MulAut.conj t).injective).trans hc
  have hCQ : C ≤ primeTorsion A p := primeTorsion_mono_of_normalizes A B p hBA hAB
  have hEQ : E ≤ primeTorsion A p := (map_mono hCQ).trans_eq
    (mem_normalizer_iff_map_conj_eq.mp (primeTorsion_normalizer A p ht))
  have hd : Disjoint C E := hdis.mono (primeTorsion_le B p)
    (map_mono (primeTorsion_le B p))
  have hcomm : C ≤ centralizer (E : Set G) := fun x hx y hy =>
    (setLike_mul_comm (hCQ hx) (hEQ hy)).symm
  obtain ⟨e,heval⟩ := exists_mulEquiv_prod_sup_of_disjoint_of_commuting C E hd hcomm
  have hsup : primeTorsion A p = C ⊔ E := by
    apply (eq_of_le_of_card_ge (sup_le hCQ hEQ) ?_).symm
    rw [← Nat.card_congr e.toEquiv, Nat.card_prod, hc, he, hq, pow_two]
  have hswap : E.map (MulAut.conj t).toMonoidHom = C := by
    change (C.map _).map _ = C
    rw [map_map]
    have hf : (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom =
        (MulAut.conj (t ^ 2)).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_two]
      group
    rw [hf]
    exact mem_normalizer_iff_map_conj_eq.mp (primeTorsion_normalizer B p hsq)
  exact ⟨hc,he,hd,hsup,hswap,e.trans (MulEquiv.subgroupCongr hsup.symm),heval⟩
end Paired

/-- For the constructed source Hall subgroup and same exchange element, the
literal p-torsion is the internal direct product of the two original Hall
factor lines. The square preserves the first line; it is not asserted to
centralize it. -/
theorem ComponentSeed.exists_paired_split_cartan_torsion (s : ComponentSeed T H K)
    (h : Hypothesis1131At D S U₁ H) (pr : Preceding1133 D S U₁ H)
    (hc : ¬ Proposition1132At D S U₁ H)
    (hs : (S.field.degree : ℕ∞) ≤ @ChapterE.globalS G _ V D.elementary)
    (hn : ¬ (K.subgroupOf H).Normal)
    (hm : ClassicalGroup.IsPSL (K ⧸ pCore 2 K) 2 (2 ^ ChapterE.generationParameter H))
    (hk : ChapterE.generationParameter H = S.field.degree ∨
      ChapterE.generationParameter H = 2 * S.field.degree)
    (c : Coordinates D S.field)
    (halt : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∨
      Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree))
    (hres : ∀ r : ℕ, r.Prime →
      ((Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) ∧
          r ∣ 2 ^ S.field.degree - 1 ∧ 3 < r) ∨
        (Source.IsSp (L ⧸ pCore 2 L) 2 (2 ^ S.field.degree) ∧
          r ∣ (2 ^ S.field.degree) ^ 2 - 1)) →
      primeToResidual r (normalizer (L : Set G)) =
        L.subgroupOf (normalizer (L : Set G)))
    (hcubic : Source.IsSL (L ⧸ pCore 2 L) 3 (2 ^ S.field.degree) →
      Even S.field.degree → ∀ x ∈ normalizer (L : Set G), orderOf x = 3 → x ∈ L) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ p ∣ 2 ^ S.field.degree - 1 ∧
      ∃ A : Subgroup G, A ≤ H ⊓ normalizer (L : Set G) ∧
        IsHallSubgroup OddHall.oddPrimes (A.subgroupOf (H ⊓ normalizer (L : Set G))) ∧
        Odd (Nat.card A) ∧ IsCyclic (A ⊓ K : Subgroup G) ∧
        Nat.card (A ⊓ K : Subgroup G) = 2 ^ ChapterE.generationParameter H - 1 ∧
        ∃ (t : T) (X : Subgroup G),
          (t : G) ∈ normalizer (A : Set G) ∧ (t : G) ∉ normalizer (K : Set G) ∧
          IsCartan T L X ∧ Paired.primeTorsion A p ≤ X ∧
          IsElementaryAbelian p (Paired.primeTorsion A p) ∧
          Nat.card (Paired.primeTorsion A p) = p ^ 2 ∧
          Paired.primeTorsion A p = Paired.primeTorsion X p ∧
          (let C := Paired.primeTorsion (A ⊓ K) p
           let E := C.map (MulAut.conj (t : G)).toMonoidHom
           Nat.card C = p ∧ Nat.card E = p ∧ Disjoint C E ∧
             Paired.primeTorsion A p = C ⊔ E ∧
             E.map (MulAut.conj (t : G)).toMonoidHom = C ∧
             ∃ e : C × E ≃* Paired.primeTorsion A p,
               ∀ x y, (e (x,y) : G) = (x : G) * (y : G)) ∧
          ∃ x ∈ Paired.primeTorsion (A ⊓ K) p, orderOf x = p ∧
            (t : G)*x*(t : G)⁻¹ ≠ x := by
  obtain ⟨p,hp,hp2,hd,A,hA,hHall,ho,t,X,htA,htK,hX,hQX,hQE,hQc,hfull,_,_,hdis,
    x,hx,hox,hmx⟩ := s.exists_paired_cartan_prime_plane h pr hc hs hn hm hk c halt hres hcubic
  let : Fact p.Prime := ⟨hp⟩
  let := hQE
  have hf : 0 < ChapterE.generationParameter H :=
    S.field.degree_pos.trans_le (degree_le_parameter h pr hc hs)
  obtain ⟨hcyc,hcard⟩ := s.paired_hall_factor_cyclic_card h pr hc hs hn hf hm A hA hHall
  let := hcyc
  have hxAK : x ∈ A ⊓ K := ⟨Paired.primeTorsion_le A p hx.1,hx.2⟩
  have hpx : p ∣ Nat.card (A ⊓ K : Subgroup G) := by
    rw [←hox, orderOf_coe (⟨x,hxAK⟩ : (A ⊓ K : Subgroup G))]
    exact orderOf_dvd_natCard _
  have hAN := s.paired_odd_normalizes h pr hc hs hn A (hA.trans inf_le_left) ho
  have hAB : A ≤ normalizer ((A ⊓ K : Subgroup G) : Set G) :=
    (le_inf A.le_normalizer hAN).trans inf_normalizer_le_normalizer_inf
  have hsqK : (t : G) ^ 2 ∈ normalizer (K : Set G) := by
    let N := (normalizer (K : Set G)).subgroupOf H
    have hi : N.index = 2 := by
      dsimp only [N]
      rw [subgroupOf_normalizer_eq s.component.1]
      exact s.paired_normalizer_index h pr hc hs hn
    exact N.sq_mem_of_index_two hi (⟨t,h.outside.1.1.2 t.property⟩ : H)
  have hsq : (t : G) ^ 2 ∈ normalizer ((A ⊓ K : Subgroup G) : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨(normalizer (A : Set G)).pow_mem htA 2,hsqK⟩
  have hsplit := Paired.prime_plane_split A (A ⊓ K) inf_le_left hAB p hpx hQc t htA hdis hsq
  have hxp : x ∈ Paired.primeTorsion (A ⊓ K) p :=
    (Paired.mem_primeTorsion_iff (A ⊓ K) p x).mpr ⟨hxAK,hox ▸ pow_orderOf_eq_one x⟩
  exact ⟨p,hp,hp2,hd,A,hA,hHall,ho,hcyc,hcard,t,X,htA,htK,hX,hQX,hQE,hQc,hfull,
    hsplit,x,hxp,hox,hmx⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
