module
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.FixedSubgroup
public import CFSG.Quasithin.ChapterE.Section06.FixedPointBounds.ParabolicCartan.Inputs
public import Theory.NumberTheory.BinarySignedTorus
public import Theory.GroupTheory.PCoreLocalSetup
public import CFSG.Quasithin.Chapter13.Section03.SourceCompletion.HallAction
/-!
# The original Hall core and its selected torus actor

Choose a prime greater than three in the exact reflected cyclic torus of
order 2ⁿ−1. Its order-p subgroup lies in O_p(Y), where Y is the original
abelian Hall group. Characteristic invariance and the actual Frattini
factorization make O_p(Y) permute with the original Sylow subgroup. The
native unitary action theorem then centralizes the original module and
component quotient. The selected subgroup retains the same torus and its
escaping relative normalizer. No invariance of the cyclic torus is asserted.

Source: Aschbacher–Smith 12.2.11(c), pp.798–799, using the actual E.2.2
Hall–Cartan witness and the reflected-torus normalizer argument of 4.4.13.
The subsequent 4.4.3 normalizer-control step is a separate earlier theorem.
-/
public section
open Subgroup
open scoped Pointwise IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section03.SourceCompletion
open ChapterB ChapterE ChapterE.Section06.FixedPointBounds.ParabolicCartan
variable {X : Type*} [Group X] [Finite X]
private theorem prime_gt_three {n : ℕ} (hn : 2 < n) :
    ∃ p : ℕ, p.Prime ∧ 3 < p ∧ p ∣ 2 ^ n - 1 := by
  by_cases h3 : n = 3
  · subst n
    exact ⟨7, by decide, by decide, by decide⟩
  · exact Nat.BinarySignedTorus.exists_prime_gt_three_dvd_sub (by omega)

omit [Finite X] in
/-- Each characteristic prime core of the actual Hall group permutes with
its marked Sylow subgroup, by the supplied Frattini factorization. -/
theorem hall_prime_core_permutes {n : ℕ} {S : Sylow 2 X}
    {hP : IsMinimalParabolicOver S ⊤} (d : IntrinsicHallCartanData S hP n) (p : ℕ) :
    (d.witness.abelianGroup.pCoreIn p : Set X) * (S : Set X) =
      (S : Set X) * (d.witness.abelianGroup.pCoreIn p : Set X) := by
  exact permutes_of_factorization d.frattini
    ((pCoreIn_le p _).trans d.normalizes)
    (inf_le_right.trans (normalizer_le_normalizer_characteristic_image _ (pCore p _)))

/-- The original cyclic torus supplies an order-p subgroup with p>3 inside
the characteristic Hall p-core. The torus itself need not be Sylow invariant. -/
theorem hall_torus_prime_selection {n : ℕ} {S : Sylow 2 X}
    {hP : IsMinimalParabolicOver S ⊤} (d : IntrinsicHallCartanData S hP n) (hn : 2 < n) :
    ∃ (p : ℕ) (A : Subgroup X), p.Prime ∧ 3 < p ∧ Nat.card A = p ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.cyclicGroup ∧
      A ≤ d.witness.abelianGroup.pCoreIn p := by
  obtain ⟨p,hp,hp3,hd⟩ := prime_gt_three hn
  let : Fact p.Prime := ⟨hp⟩
  have hd' : p ^ 1 ∣ Nat.card d.witness.cyclicGroup := by simpa [d.witness.card] using hd
  obtain ⟨A0,hA0⟩ := Sylow.exists_subgroup_card_pow_prime p hd'
  let A := A0.map d.witness.cyclicGroup.subtype
  have hc : Nat.card A = p := by
    change Nat.card (A0.map d.witness.cyclicGroup.subtype) = p
    rw [card_map_of_injective d.witness.cyclicGroup.subtype_injective]
    simpa only [pow_one] using hA0
  have hAD : A ≤ d.witness.cyclicGroup := map_subtype_le _
  have hAY := hAD.trans d.witness.cyclic_le
  let := d.witness.abelian
  have hYA : d.witness.abelianGroup ≤ centralizer (A : Set X) :=
    (le_centralizer_iff_isMulCommutative.mpr inferInstance).trans (centralizer_le hAY)
  have hAe : IsElementaryAbelian p A := {
    toIsMulCommutative := (isCyclic_of_prime_card hc).isMulCommutative
    exponent_dvd_p := hc ▸ Group.exponent_dvd_nat_card }
  have hAp : IsPGroup p A := IsPGroup.of_card (n := 1) (by simpa using hc)
  exact ⟨p,A,hp,hp3,hc,hAe,hAD,
    le_pCoreIn_of_normalizes hAp hAY (hYA.trans (Subgroup.centralizer_le_normalizer _))⟩
variable {G : Type*} [Group G] [Finite G] {V : Subgroup G}
  [IsElementaryAbelian 2 V]
open Atlas.G2.Natural.BinaryPointFlag

/-- The same selected torus yields an elementary odd actor centralizing the
original unitary module and acting trivially on the original component
quotient, while its actual relative normalizer escapes N(L). -/
theorem unitary_torus_prime_actor
    (T : Sylow 2 G) (L H U : Subgroup G) (hTH : (T : Subgroup G) ≤ H)
    {n : ℕ} {hP : IsMinimalParabolicOver (T.subtype hTH) ⊤}
    (d : IntrinsicHallCartanData (T.subtype hTH) hP n) (hn : 2 < n)
    (hmax : minimalParabolicMax (T.subtype hTH) hP = (normalizer (L : Set G)).subgroupOf H)
    (hescape : ∀ (p : ℕ) (_ : Fact p.Prime) (A : Subgroup H), Odd p →
      A ≤ d.witness.cyclicGroup → IsPGroup p A →
      ¬ normalizer (A : Set H) ≤ minimalParabolicMax (T.subtype hTH) hP)
    (hLN : L ≤ normalizer (V : Set G)) (hNL : normalizer (V : Set G) ≤ normalizer (L : Set G))
    (hTN : (T : Subgroup G) ≤ normalizer (V : Set G))
    (hTI : ∀ g ∈ normalizer (L : Set G), V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
      V.map (MulAut.conj g).toMonoidHom = V)
    (hU : U ≠ ⊥) (hUV : U ≤ V) (hHU : H ≤ normalizer (U : Set G))
    (hres : pResidual 2 L = ⊤) (hfaith : L ⊓ centralizer (V : Set G) ≤ L.pCoreIn 2)
    (e : inducedAutomizer V L ≃* Atlas.G2.Natural.BinaryNormalizer.Derived)
    (E0 : Additive V ≃ₗ[F] Atlas.G2.Natural.Space F)
    (he0 : ∀ (l : inducedAutomizer V L) v, E0 (automizerRepresentation V l v) =
      Atlas.G2.Natural.derivedAction F (e l) (E0 v)) :
    ∃ (p : ℕ) (A : Subgroup G), p.Prime ∧ 3 < p ∧ Nat.card A = p ∧
      IsElementaryAbelian p A ∧ A ≤ d.witness.cyclicGroup.map H.subtype ∧
      A ≤ H ⊓ normalizer (L : Set G) ∧ A ≤ centralizer (V : Set G) ∧
      ⁅A,L⁆ ≤ L.pCoreIn 2 ∧ ¬ H ⊓ normalizer (A : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨p,A,hp,hp3,hAc,hAe,hAD,hAB⟩ := hall_torus_prime_selection d hn
  let : Fact p.Prime := ⟨hp⟩
  let : IsElementaryAbelian p A := hAe
  let B := (d.witness.abelianGroup.pCoreIn p).map H.subtype
  have hBH : B ≤ H ⊓ normalizer (L : Set G) := by
    refine le_inf (map_subtype_le _) ?_
    apply map_le_iff_le_comap.mpr
    exact (pCoreIn_le p _).trans (d.hall_le.trans hmax.le)
  have hBp : IsPGroup p B := (isPGroup_pCoreIn p _).map H.subtype
  have hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G) := by
    have hh := congrArg (Set.image H.subtype) (hall_prime_core_permutes d p)
    have hsmap : H.subtype '' ((T.subtype hTH) : Set H) = (T : Set G) := by
      change (((T : Subgroup G).subgroupOf H).map H.subtype : Set G) = _
      rw [map_subgroupOf_eq_of_le hTH]
      exact Sylow.coe_coe T
    simpa only [Set.image_mul, hsmap, B, coe_map] using hh
  obtain ⟨hBC,_,hBL⟩ := source_hall_prime_trivial_component_action hp3 T L B H U
    hLN hNL hTN hTI hU hUV hHU hBH hBp hres hfaith hperm e E0 he0
  have hAB' : A.map H.subtype ≤ B := map_mono hAB
  refine ⟨p,A.map H.subtype,hp,hp3,?_,IsElementaryAbelian.map H.subtype,
    map_mono hAD,hAB'.trans hBH,hAB'.trans hBC,
    (commutator_mono hAB' le_rfl).trans hBL,?_⟩
  · simpa only [card_map_of_injective H.subtype_injective] using hAc
  · intro hN
    apply hescape p inferInstance A (hp.odd_of_ne_two (by omega)) hAD hAe.isPGroup
    rw [hmax]
    intro x hx
    exact hN ⟨x.property, A.le_normalizer_map H.subtype (mem_map.mpr ⟨x,hx,rfl⟩)⟩

end CFSG.Quasithin.Chapter13.Section03.SourceCompletion
