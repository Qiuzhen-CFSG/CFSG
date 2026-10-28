module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Denominator
public import Theory.GroupTheory.CommutatorPreimageFrattini
public import Theory.ElementaryAbelian.Join

/-!
# Elementary structure of the actual opposite-core quotient

O₂(I) normalizes both W and Wʸ. Consequently the two core intersections
commute modulo W∩Wʸ. Their squares lie in V by the preceding Frattini
bound. Their images generate Q/N, so this literal quotient is elementary
abelian. In particular Φ(Q)≤N, without using natural-module recognition.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement IsMulCommutative
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

private theorem elementary_of_squares {A : Type*} [Group A]
    (hs : ∀ a : A, a ^ 2 = 1) : IsElementaryAbelian 2 A where
  toIsMulCommutative := ⟨⟨fun x y => Commute.of_orderOf_dvd_two
    (fun a => orderOf_dvd_of_pow_eq_one (hs a)) x y⟩⟩
  exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hs

private theorem elementary_quotient_of_join {H : Type*} [Group H]
    (A B N : Subgroup H) [N.Normal] (hgen : A ⊔ B = ⊤)
    (hA : ∀ a ∈ A, a ^ 2 ∈ N) (hB : ∀ b ∈ B, b ^ 2 ∈ N)
    (hc : ⁅A,B⁆ ≤ N) : IsElementaryAbelian 2 (H ⧸ N) := by
  let π := QuotientGroup.mk' N
  have hel (C : Subgroup H) (hs : ∀ c ∈ C, c ^ 2 ∈ N) :
      IsElementaryAbelian 2 (C.map π) := by
    apply elementary_of_squares
    rintro ⟨x,c,hc,rfl⟩
    apply Subtype.ext
    change π c ^ 2 = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff (N := N) (c ^ 2)).mpr (hs c hc)
  let : IsElementaryAbelian 2 (A.map π) := hel A hA
  let : IsElementaryAbelian 2 (B.map π) := hel B hB
  have hcomm : ⁅A.map π,B.map π⁆ = ⊥ := by
    rw [← map_commutator]
    exact (Subgroup.map_eq_bot_iff _).mpr ((QuotientGroup.ker_mk' N).symm ▸ hc)
  have hj : IsElementaryAbelian 2 (A.map π ⊔ B.map π : Subgroup (H ⧸ N)) := by
    rw [sup_comm]
    exact IsElementaryAbelian.sup_of_le_centralizer
      (commutator_eq_bot_iff_le_centralizer.mp hcomm)
  have ht : A.map π ⊔ B.map π = ⊤ := by
    rw [← Subgroup.map_sup, hgen, map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]
  let : IsElementaryAbelian 2 (⊤ : Subgroup (H ⧸ N)) := ht ▸ hj
  apply elementary_of_squares
  intro x
  exact elemPow_eq_one_of_isElementaryAbelian (A := (⊤ : Subgroup (H ⧸ N))) x (mem_top x)

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The two core intersections commute modulo their actual intersection. -/
theorem core_factors_commutator_le_intersection (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ⁅auxiliaryW E ⊓ (oppositeJoin (auxiliaryW E) y).pCoreIn 2,
      (auxiliaryW E).map (MulAut.conj y).toMonoidHom ⊓
        (oppositeJoin (auxiliaryW E) y).pCoreIn 2⁆ ≤
      auxiliaryW E ⊓ (auxiliaryW E).map (MulAut.conj y).toMonoidHom := by
  have hn := large_core_normalizes_pair E m hy
  exact le_inf
    ((commutator_mono inf_le_left inf_le_right).trans
      (le_normalizer_iff_commutator_le_left.mp (hcore.trans hn.1)))
    ((commutator_mono inf_le_right inf_le_left).trans
      (le_normalizer_iff_commutator_le_right.mp (hcore.trans hn.2)))

/-- Q/N is elementary for the literal relative-normal denominator. -/
theorem quotient_elementary (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    let _ := denominator_normal_in_corePair E m hy hW hPhi
    IsElementaryAbelian 2
      (corePair (auxiliaryW E) y ⧸ (pairDenominator E y).subgroupOf (corePair (auxiliaryW E) y)) := by
  let Q := corePair (auxiliaryW E) y
  let N := pairDenominator E y
  let A := auxiliaryW E ⊓ (oppositeJoin (auxiliaryW E) y).pCoreIn 2
  let B := (auxiliaryW E).map (MulAut.conj y).toMonoidHom ⊓
    (oppositeJoin (auxiliaryW E) y).pCoreIn 2
  let _ := denominator_normal_in_corePair E m hy hW hPhi
  have hp : IsPGroup 2 (auxiliaryW E) :=
    (isPGroup_pCoreIn 2 E.G₁).to_le ((auxiliaryW_le_W E).trans hW)
  have hyV : E.V₁.map (MulAut.conj y).toMonoidHom ≤ V :=
    (map_mono (f := (MulAut.conj y).toMonoidHom) E.V₁_le).trans
      (mem_normalizer_iff_map_conj_eq.mp (D.normalizes hy)).le
  have hPhiB : (frattini ((auxiliaryW E).map (MulAut.conj y).toMonoidHom)).map
      ((auxiliaryW E).map (MulAut.conj y).toMonoidHom).subtype ≤ V := by
    rw [frattini_image_map _ _ (MulAut.conj y).injective]
    exact (map_mono hPhi).trans hyV
  have hs (C : Subgroup G) (hp : IsPGroup 2 C)
      (hf : (frattini C).map C.subtype ≤ V) (c : G) (hc : c ∈ C) : c ^ 2 ∈ N := by
    let : Fact (IsPGroup 2 C) := ⟨hp⟩
    exact mem_sup_right (hf (mem_map_of_mem C.subtype
      (pth_power_mem_frattini_of_isPGroup (p := 2) (⟨c,hc⟩ : C))))
  apply elementary_quotient_of_join (A.subgroupOf Q) (B.subgroupOf Q) (N.subgroupOf Q)
  · rw [← subgroupOf_sup (show A ≤ Q from le_sup_left) (show B ≤ Q from le_sup_right)]
    exact subgroupOf_self _
  · intro a ha
    exact hs _ hp (hPhi.trans E.V₁_le) a ha.1
  · intro b hb
    exact hs _ (hp.map _) hPhiB b hb.1
  · apply commutator_le.mpr
    intro a ha b hb
    exact mem_sup_left (core_factors_commutator_le_intersection E m hy hcore
      (commutator_mem_commutator ha hb))

/-- The Frattini bound required by 11.5.6(4), before any recognition step. -/
theorem corePair_frattini_le_denominator (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    (frattini (corePair (auxiliaryW E) y)).map (corePair (auxiliaryW E) y).subtype ≤
      pairDenominator E y := by
  let _ := denominator_normal_in_corePair E m hy hW hPhi
  have hp := (isPGroup_pCoreIn 2 _).to_le (source_corePair_properties E m hy hcore).1
  have hf := frattini_le_of_elementary_quotient hp _
    (quotient_elementary E m hy hW hPhi hcore)
  rintro _ ⟨q,hq,rfl⟩
  exact hf hq

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
