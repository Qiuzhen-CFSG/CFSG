module
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.CartanPlacement
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.LinearShadow.ParameterComponent.Recognition.Paired.TorusApplication
public import Theory.GroupTheory.PCoreImage
public import Theory.ElementaryAbelian.PrimePlane

/-!
# The literal paired Hall prime plane in an actual Cartan

Relative normality transports omega-cores through the original inclusions.
Once the genuine 11.0.4 clauses put the Hall p-torsion in L, it is exactly
the p-torsion computed in the abelian normal intersection A intersect L.
The same Sylow exchange element moves a Cauchy element of A intersect K.
That element and its conjugate span two disjoint lines in the Cartan.
The Cartan's prime rank is two, so the source torsion has order p squared
and equals the entire p-torsion of that Cartan.

The source application constructs the Hall subgroup, prime, Cartan and
moved element. PSL2 recognition at the actual generation minimum and the
genuine preceding residual/cubic clauses remain explicit. The common
field action and paired exclusion remain with this parameter-component
owner; the earlier-source and doubled-exclusion discharge stays with
qt-d-1222-shadow-linear-geometry. This is not the full 11.3.5 theorem.
Source: Aschbacher--Smith, 11.0.4 and 11.3.5(2), pp.760,771--772.
-/

@[expose] public noncomputable section
open Subgroup Theory.GroupTheory
open CFSG.Quasithin.Chapter11.ChosenNaturalSource.LocalGeometry
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : Chapter12.Section02.ChosenModule T L V} {S : D.NonbinaryNaturalInput}
    {U₁ : Submodule (ZMod 2) D.chosenCentralQuotient} {H K : Subgroup G}

namespace Paired

omit [Finite G] in
/-- Relative normality transports the literal omega-core upwards. -/
theorem primeTorsion_mono_of_normalizes (A B : Subgroup G) (p : ℕ)
    (hBA : B ≤ A) (hn : A ≤ normalizer (B : Set G)) :
    primeTorsion B p ≤ primeTorsion A p := by
  have hc : B.pCoreIn p ≤ A.pCoreIn p := pCoreIn_mono_of_normalizes hBA hn
  rw [primeTorsion,map_le_iff_le_comap]
  apply (closure_le _).mpr
  intro b hb
  change (b : G) ∈ primeTorsion A p
  refine ⟨⟨b,hc b.property⟩,subset_closure ?_,rfl⟩
  apply Subtype.ext
  exact congrArg (fun z : B.pCoreIn p => (z : G)) hb

/-- If the omega-core is contained in an abelian normal intersection, it
is exactly the omega-core computed inside that intersection. -/
theorem primeTorsion_eq_intersection (A L : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative (A ⊓ L : Subgroup G)]
    (hn : A ≤ normalizer (L : Set G)) (hL : primeTorsion A p ≤ L) :
    primeTorsion A p = primeTorsion (A ⊓ L) p := by
  apply le_antisymm
  · rw [primeTorsion,map_le_iff_le_comap]
    apply (closure_le _).mpr
    intro a ha
    have haP : (a : G) ∈ primeTorsion A p := ⟨a,subset_closure ha,rfl⟩
    apply (mem_primeTorsion_iff (A ⊓ L) p a).mpr
    refine ⟨⟨primeTorsion_le A p haP,hL haP⟩,?_⟩
    simpa only [pow_one,coe_pow,coe_one] using congrArg Subtype.val ha
  · exact primeTorsion_mono_of_normalizes A (A ⊓ L) p inf_le_left
      ((le_inf A.le_normalizer hn).trans inf_normalizer_le_normalizer_inf)

/-- Prime elements in the abelian normal intersection belong to the
original omega-core, including when the whole odd Hall group is not abelian. -/
theorem mem_primeTorsion_of_intersection (A L : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative (A ⊓ L : Subgroup G)] (hn : A ≤ normalizer (L : Set G))
    (x : G) (hx : x ∈ A ⊓ L) (hp : x ^ p = 1) : x ∈ primeTorsion A p :=
  primeTorsion_mono_of_normalizes A (A ⊓ L) p inf_le_left
    ((le_inf A.le_normalizer hn).trans inf_normalizer_le_normalizer_inf)
    ((mem_primeTorsion_iff (A ⊓ L) p x).mpr ⟨hx,hp⟩)

/-- An exchanged prime element gives two independent lines in the actual
abelian p-subgroup. A rank-two ambient torus then forces exact rank two. -/
theorem primeRank_two_of_exchanged_element (Q X B : Subgroup G)
    [IsMulCommutative Q] (hQX : Q ≤ X) (p : ℕ) [Fact p.Prime]
    (hX : primeRank p X = 2) (t : G) (ht : t ∈ normalizer (Q : Set G))
    (hd : Disjoint B (B.map (MulAut.conj t).toMonoidHom))
    (x : G) (hxQ : x ∈ Q) (hxB : x ∈ B) (ho : orderOf x = p) :
    primeRank p Q = 2 := by
  let C := zpowers x
  let E := C.map (MulAut.conj t).toMonoidHom
  have hCQ : C ≤ Q := zpowers_le.mpr hxQ
  have hEQ : E ≤ Q := by
    rintro _ ⟨a,ha,rfl⟩
    exact (ht a).mp (hCQ ha)
  have hCE : Disjoint C E := hd.mono (zpowers_le.mpr hxB)
    (map_mono (f := (MulAut.conj t).toMonoidHom) (zpowers_le.mpr hxB))
  have hcomm : C ≤ centralizer (E : Set G) := by
    intro a ha b hb
    exact setLike_mul_comm (hEQ hb) (hCQ ha)
  have hcard : Nat.card C = p := by simpa only [C,Nat.card_zpowers] using ho
  have hC := Theory.Quasithin.one_le_primeRank_of_dvd_card (G := C) (p := p)
    (by rw [hcard])
  have hE : primeRank p C = primeRank p E :=
    primeRank_equiv p ((MulAut.conj t).subgroupMap C)
  have hadd := primeRank_sup_eq_add_of_disjoint_commuting C E hCE hcomm p
  have hl := Theory.GroupTheory.primeRank_le_of_injective p (inclusion (sup_le hCQ hEQ))
    (inclusion_injective (sup_le hCQ hEQ))
  have hu := Theory.GroupTheory.primeRank_le_of_injective p (inclusion hQX) (inclusion_injective hQX)
  omega

/-- A p-plane inside a rank-two abelian Cartan is its entire p-torsion.
Thus the subgroup in the source is not replaced by an arbitrary plane. -/
theorem prime_plane_eq_cartan_torsion (Q X : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsElementaryAbelian p Q] [IsMulCommutative X] (hQX : Q ≤ X)
    (hc : Nat.card Q = p ^ 2) (hr : primeRank p X = 2) :
    Q = primeTorsion X p := by
  have hQR : Q ≤ primeTorsion X p := by
    intro x hx
    exact (mem_primeTorsion_iff X p x).mpr
      ⟨hQX hx,elemPow_eq_one_of_isElementaryAbelian x hx⟩
  let := primeTorsion_elementary X p
  have hRX := primeTorsion_le X p
  have hRE := IsElementaryAbelian.subgroupOf (p := p) hRX
  have hbound := (primeRank_le_iff_elementary_card_le X).mp hr.le
    ((primeTorsion X p).subgroupOf X) hRE
  rw [Nat.card_congr (subgroupOfEquivOfLe hRX).toEquiv] at hbound
  exact eq_of_le_of_card_ge hQR (hc ▸ hbound)

end Paired

/-- The original Hall prime gives the literal elementary p-plane, contained
in an actual source Cartan, and a moved element for the same Sylow actor.
The only model input is recognition at the true generation minimum. -/
theorem ComponentSeed.exists_paired_cartan_prime_plane (s : ComponentSeed T H K)
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
        Odd (Nat.card A) ∧
        ∃ (t : T) (X : Subgroup G),
          (t : G) ∈ normalizer (A : Set G) ∧
          (t : G) ∉ normalizer (K : Set G) ∧
          IsCartan T L X ∧ Paired.primeTorsion A p ≤ X ∧
          IsElementaryAbelian p (Paired.primeTorsion A p) ∧
          Nat.card (Paired.primeTorsion A p) = p ^ 2 ∧
          Paired.primeTorsion A p = Paired.primeTorsion X p ∧
          Paired.primeTorsion A p = Paired.primeTorsion (A ⊓ L) p ∧
          (t : G) ∈ normalizer (Paired.primeTorsion A p : Set G) ∧
          Disjoint (A ⊓ K) ((A ⊓ K).map (MulAut.conj (t : G)).toMonoidHom) ∧
          ∃ x ∈ Paired.primeTorsion A p ⊓ K, orderOf x = p ∧
            (t : G)*x*(t : G)⁻¹ ≠ x := by
  obtain ⟨p,hp,hp2,hd,A,hA,hHall,ho,t,htA,htK,hdis,x,hx,hox,hmx⟩ :=
    s.exists_paired_hall_prime_element_at_parameter h pr hc hs hn hm hk
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨X,hX,hAX⟩ := s.paired_linear_odd_intersection_cartan h pr hc hs hn hm halt
    c A (hA.trans inf_le_left) ho
  let j := (c.cartanTorusEquiv hX).toMonoidHom.comp (inclusion hAX)
  have hj : Function.Injective j := (c.cartanTorusEquiv hX).injective.comp (inclusion_injective hAX)
  let : IsMulCommutative (A ⊓ L : Subgroup G) :=
    .of_comm fun a b => hj (by simp only [map_mul,mul_comm])
  have hQL := Paired.source_primeTorsion_le S A hA p hp hd halt hres hcubic
  have hQN := Paired.primeTorsion_eq_intersection A L p (hA.trans inf_le_right) hQL
  have hQX : Paired.primeTorsion A p ≤ X :=
    (le_inf (Paired.primeTorsion_le A p) hQL).trans hAX
  have hQE : IsElementaryAbelian p (Paired.primeTorsion A p) := by
    rw [hQN]
    exact Paired.primeTorsion_elementary (A ⊓ L) p
  let := hQE
  have htQ := Paired.primeTorsion_normalizer A p htA
  have hxL := Paired.source_prime_order_mem S A hA p hp hd halt hres hcubic x hx.1 hox
  have hxQ := Paired.mem_primeTorsion_of_intersection A L p (hA.trans inf_le_right)
    x ⟨hx.1,hxL⟩ (hox ▸ pow_orderOf_eq_one x)
  have hr := Paired.primeRank_two_of_exchanged_element (Paired.primeTorsion A p) X (A ⊓ K)
    hQX p (c.cartan_primeRank hX hp hd) t htQ hdis x hxQ hx hox
  have hcard := IsElementaryAbelian.card_eq_prime_sq_of_primeRank_two hr
  let : IsMulCommutative X := .of_comm fun a b => (c.cartanTorusEquiv hX).injective
    (by simp only [map_mul,mul_comm])
  have hfull := Paired.prime_plane_eq_cartan_torsion (Paired.primeTorsion A p) X p
    hQX hcard (c.cartan_primeRank hX hp hd)
  exact ⟨p,hp,hp2,hd,A,hA,hHall,ho,t,X,htA,htK,hX,hQX,hQE,
    hcard,hfull,hQN,htQ,hdis,
    x,⟨hxQ,hx.2⟩,hox,hmx⟩

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.ShadowReduction.ParameterComponent
