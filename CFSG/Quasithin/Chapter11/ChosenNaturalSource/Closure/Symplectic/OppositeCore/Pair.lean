module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.Algebra
public import Theory.GroupTheory.CoprimeCentralizerDecomposition
public import Theory.GroupTheory.PCoreImage

/-!
# Core normalization and transfer for the actual opposite pair

Both generators are normalized by O₂(LT): W is a G₁-invariant closure,
and conjugation by y∈L preserves O₂(LT). Thus the geometric bound
O₂(I)≤O₂(LT) discharges both normalization premises of corePair_properties.
The original O₂(L), not merely O₂(I), also has its I-commutators in Q.

The transfer uses X₁=C_X(L₁/O₂(L₁)), the literal denominator (W∩Wʸ)V,
and N_M₁(V₁ʸ). Coprime action splits Q into its X₁-commutator and fixed
subgroup. The Cartan bound and the actual Frattini supplement place the
first factor in O₂(G₁); the denominator bound places the second there.

The natural-module fixed-space bound, the core-image bound, and the
supplement/action conclusions remain explicit inputs here. Their source
construction is not asserted by this module.
Source: Aschbacher--Smith 11.5.7, printed p.783.
-/

public noncomputable section

open Subgroup Theory.GroupTheory
open scoped commutatorElement

private theorem normalizes_join {G : Type*} [Group G] (A B C : Subgroup G)
    (hAC : A ≤ normalizer (C : Set G)) (hAB : ⁅A,B⁆ ≤ C) :
    A ≤ normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  apply le_normalizer_iff.mpr
  intro a ha x hx
  have h : B ⊔ C ≤ (B ⊔ C).comap (MulAut.conj a).toMonoidHom := by
    apply sup_le
    · intro b hb
      have hh := (B ⊔ C).mul_mem
        (mem_sup_right (hAB (commutator_mem_commutator ha hb))) (mem_sup_left hb)
      change a * b * a⁻¹ ∈ B ⊔ C
      simpa only [commutatorElement_def, mul_assoc, inv_mul_cancel, mul_one] using hh
    · intro c hc
      exact mem_sup_right (le_normalizer_iff.mp hAC a ha c hc)
  exact h hx

private theorem core_transfer {G : Type*} [Group G]
    (P N H S : Subgroup G) (hp : IsPGroup 2 P)
    (hPH : P ≤ H) (hNH : N ≤ H) (hSH : S ≤ H)
    (hHN : H ≤ normalizer (N : Set G)) (hSP : S ≤ normalizer (P : Set G))
    (hgen : H ≤ N ⊔ S) (hc : ⁅P,N⁆ ≤ N.pCoreIn 2) :
    P ≤ H.pCoreIn 2 := by
  let C := N.pCoreIn 2
  have hHC : H ≤ normalizer (C : Set G) :=
    hHN.trans (normalizer_le_normalizer_characteristic_image N (pCore 2 N))
  have hNQ : N ≤ normalizer ((P ⊔ C : Subgroup G) : Set G) :=
    normalizes_join N P C (hNH.trans hHC) (by rw [commutator_comm]; exact hc)
  have hSQ : S ≤ normalizer ((P ⊔ C : Subgroup G) : Set G) :=
    (le_inf hSP (hSH.trans hHC)).trans (normalizer_inf_normalizer_le_normalizer_sup P C)
  have hQp : IsPGroup 2 (P ⊔ C : Subgroup G) := by
    rw [sup_comm]
    exact (isPGroup_pCoreIn 2 N).to_sup_of_normal_left' hp (hPH.trans hHC)
  exact le_sup_left.trans (le_pCoreIn_of_normalizes hQp
    (sup_le hPH ((pCoreIn_le 2 N).trans hNH)) (hgen.trans (sup_le hNQ hSQ)))

namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- The three-space closure lies in the full chosen closure. -/
theorem U_le_W : E.U ≤ E.W :=
  conjugateSpanBy_mono (D.centralQuotientPreimage_le E.threeSpace) le_rfl

/-- Both branches of the source temporary W lie in W_H. -/
theorem auxiliaryW_le_W : auxiliaryW E ≤ E.W := by
  classical
  unfold auxiliaryW
  split
  · exact le_rfl
  · exact U_le_W E

/-- The actual temporary W is G₁-invariant in both branches. -/
theorem G₁_normalizes_auxiliaryW : E.G₁ ≤ normalizer (auxiliaryW E : Set G) := by
  classical
  unfold auxiliaryW
  split <;> exact le_normalizer_conjugateSpanBy _ _

omit [Finite G] in
private theorem large_core_le_sylow : (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ T := by
  simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
    pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)

/-- O₂(LT) normalizes both original opposite generators. -/
theorem large_core_normalizes_pair (m : MarkedFlag E) {y : G} (hy : y ∈ L) :
    (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤ normalizer (auxiliaryW E : Set G) ∧
      (L ⊔ (T : Subgroup G)).pCoreIn 2 ≤
        normalizer ((auxiliaryW E).map (MulAut.conj y).toMonoidHom : Set G) := by
  let R := (L ⊔ (T : Subgroup G)).pCoreIn 2
  have hn : R ≤ normalizer (auxiliaryW E : Set G) :=
    large_core_le_sylow.trans (m.sylow_le_point_normalizer.trans (G₁_normalizes_auxiliaryW E))
  have hyR : y ∈ normalizer (R : Set G) :=
    ((L ⊔ (T : Subgroup G)).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
      (mem_sup_left hy)
  refine ⟨hn, ?_⟩
  change R ≤ _
  rw [← mem_normalizer_iff_map_conj_eq.mp hyR]
  exact (map_mono hn).trans ((auxiliaryW E).le_normalizer_map _)

/-- The source core bound discharges both abstract core-pair normalizations. -/
theorem source_corePair_properties (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    corePair (auxiliaryW E) y ≤ (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ∧
      ((corePair (auxiliaryW E) y).subgroupOf (oppositeJoin (auxiliaryW E) y)).Normal ∧
      ⁅(oppositeJoin (auxiliaryW E) y).pCoreIn 2, oppositeJoin (auxiliaryW E) y⁆ ≤
        corePair (auxiliaryW E) y := by
  have hn := large_core_normalizes_pair E m hy
  exact corePair_properties _ _ (hcore.trans hn.1) (hcore.trans hn.2)

/-- X₁ uses the kernel of the action on the literal L₁/O₂(L₁). -/
@[expose] def cartanKernel : Subgroup G := E.X ⊓ coreQuotientCentralizer E.L₁

/-- The literal denominator; its inclusion and relative normality in Q
are further geometric conclusions, not built into this definition. -/
@[expose] def pairDenominator (y : G) : Subgroup G :=
  ((auxiliaryW E) ⊓ (auxiliaryW E).map (MulAut.conj y).toMonoidHom) ⊔ V

/-- The actual supplement N_M₁(V₁ʸ) in the Frattini argument. -/
@[expose] def oppositePointStabilizer (y : G) : Subgroup G :=
  E.M₁ ⊓ normalizer (E.V₁.map (MulAut.conj y).toMonoidHom : Set G)

/-- The source denominator already lies in O₂(G₁). -/
theorem pairDenominator_le_core (hV : V ≤ E.G₁.pCoreIn 2)
    (hW : E.W ≤ E.G₁.pCoreIn 2) (y : G) :
    pairDenominator E y ≤ E.G₁.pCoreIn 2 :=
  sup_le (inf_le_left.trans ((auxiliaryW_le_W E).trans hW)) hV

/-- Apply coprime action and core transfer to the actual Q. The natural
quotient and preceding Cartan argument must supply the displayed inputs. -/
theorem corePair_le_point_core_of_cartan (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) y)
    (hodd : Odd (Nat.card (cartanKernel E)))
    (hfixed : corePair (auxiliaryW E) y ⊓ centralizer (cartanKernel E : Set G) ≤
      pairDenominator E y)
    (hG : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ E.M₁)
    (hM : E.M₁ = E.L₁ ⊔ oppositePointStabilizer E y)
    (hnorm : oppositePointStabilizer E y ≤
      normalizer ((⁅corePair (auxiliaryW E) y, cartanKernel E⁆ : Subgroup G) : Set G))
    (hcartan : ⁅⁅corePair (auxiliaryW E) y, cartanKernel E⁆, E.K ⊔ E.Y⁆ ≤
      (E.K ⊔ E.Y).pCoreIn 2) :
    corePair (auxiliaryW E) y ≤ E.G₁.pCoreIn 2 := by
  let Q := corePair (auxiliaryW E) y
  let P := ⁅Q, cartanKernel E⁆
  have hprops := source_corePair_properties E m hy hcore
  have hQI : Q ≤ oppositeJoin (auxiliaryW E) y := hprops.1.trans (pCoreIn_le 2 _)
  have hIQ : oppositeJoin (auxiliaryW E) y ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer hQI).mp hprops.2.1
  have hXQ : cartanKernel E ≤ normalizer (Q : Set G) := hXI.trans hIQ
  have hQp : IsPGroup 2 Q := (isPGroup_pCoreIn 2 _).to_le hprops.1
  have hPQ : P ≤ Q := le_normalizer_iff_commutator_le_left.mp hXQ
  have hPG : P ≤ E.G₁ := hPQ.trans (hprops.1.trans
    (hcore.trans (large_core_le_sylow.trans m.sylow_le_point_normalizer)))
  have hgen : E.G₁ ≤ (E.K ⊔ E.Y) ⊔ oppositePointStabilizer E y := by
    apply hG.trans
    apply sup_le le_sup_left
    rw [hM]
    exact sup_le
      (((le_conjugateSpanBy E.L₁ E.G₁).trans le_sup_left).trans le_sup_left) le_sup_right
  have hPcore : P ≤ E.G₁.pCoreIn 2 :=
    core_transfer P (E.K ⊔ E.Y) E.G₁ (oppositePointStabilizer E y)
      (hQp.to_le hPQ) hPG (sup_le E.K_le_G₁ E.Y_le_G₁)
      (inf_le_left.trans inf_le_right) (normalizes_KY E) hnorm hgen hcartan
  have hcop : Nat.Coprime (Nat.card (cartanKernel E)) (Nat.card Q) := by
    obtain ⟨n, hn⟩ := hQp.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  let : Group.IsNilpotent Q := hQp.isNilpotent
  have hsplit := eq_commutator_sup_centralizer_of_solvable_coprime Q (cartanKernel E)
    hXQ inferInstance hcop
  exact hsplit.le.trans (sup_le hPcore
    (hfixed.trans (pairDenominator_le_core E hV hW y)))

/-- The original core of L, acting on the pair, has commutators in Q. -/
theorem original_core_opposite_commutator (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2) :
    ⁅L.pCoreIn 2, oppositeJoin (auxiliaryW E) y⁆ ≤ corePair (auxiliaryW E) y := by
  let R := L.pCoreIn 2
  let I := oppositeJoin (auxiliaryW E) y
  let W := auxiliaryW E
  let Z := W.map (MulAut.conj y).toMonoidHom
  let Q := corePair W y
  have hT : E.G₁.pCoreIn 2 ≤ T := by
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le m.sylow_le_point_normalizer] using
      pCoreIn_le_sylow E.G₁ (T.subtype m.sylow_le_point_normalizer)
  have hWL : W ≤ L ⊔ (T : Subgroup G) :=
    ((auxiliaryW_le_W E).trans hW).trans (hT.trans le_sup_right)
  have hZL : Z ≤ L ⊔ (T : Subgroup G) := by
    rw [← mem_normalizer_iff_map_conj_eq.mp
      ((L ⊔ (T : Subgroup G)).le_normalizer (mem_sup_left hy))]
    exact map_mono hWL
  have hIL : I ≤ L ⊔ (T : Subgroup G) := sup_le hWL hZL
  have hnormal : L ⊔ (T : Subgroup G) ≤ normalizer (L : Set G) :=
    sup_le L.le_normalizer D.sylow_normalizes_component
  have hIR : I ≤ normalizer (R : Set G) := (hIL.trans hnormal).trans
    (normalizer_le_normalizer_characteristic_image L (pCore 2 L))
  have hRbig : R ≤ (L ⊔ (T : Subgroup G)).pCoreIn 2 :=
    pCoreIn_mono_of_normalizes le_sup_left hnormal
  have hn := large_core_normalizes_pair E m hy
  have hRW : R ≤ normalizer (W : Set G) := hRbig.trans hn.1
  have hRZ : R ≤ normalizer (Z : Set G) := hRbig.trans hn.2
  have hcap : R ⊓ I ≤ I.pCoreIn 2 := le_pCoreIn_of_normalizes
    ((isPGroup_pCoreIn 2 L).to_le inf_le_left) inf_le_right
    ((le_inf hIR I.le_normalizer).trans inf_normalizer_le_normalizer_inf)
  have hw : ⁅W,R⁆ ≤ W ⊓ I.pCoreIn 2 := by
    have hc := le_normalizer_iff_commutator_le_left.mp hRW
    exact le_inf hc ((le_inf
      (le_normalizer_iff_commutator_le_right.mp (le_sup_left.trans hIR))
      (hc.trans le_sup_left)).trans hcap)
  have hz : ⁅Z,R⁆ ≤ Z ⊓ I.pCoreIn 2 := by
    have hc := le_normalizer_iff_commutator_le_left.mp hRZ
    exact le_inf hc ((le_inf
      (le_normalizer_iff_commutator_le_right.mp (le_sup_right.trans hIR))
      (hc.trans le_sup_right)).trans hcap)
  have hprops := source_corePair_properties E m hy hcore
  have hIQ : I ≤ normalizer (Q : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hprops.1.trans (pCoreIn_le 2 _))).mp hprops.2.1
  rw [commutator_comm]
  exact commutator_sup_le_of_relative_normal I W Z R Q hIQ le_sup_left le_sup_right
    (hw.trans le_sup_left) (hz.trans le_sup_right)

/-- Transfer the bound through any of the source L₁-conjugates. -/
theorem original_core_conjugate_commutator (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hQ : corePair (auxiliaryW E) y ≤ E.G₁.pCoreIn 2) {l : G} (hl : l ∈ E.L₁) :
    ⁅L.pCoreIn 2, (oppositeJoin (auxiliaryW E) y).map (MulAut.conj l).toMonoidHom⁆ ≤
      E.G₁.pCoreIn 2 := by
  have h := map_mono (f := (MulAut.conj l).toMonoidHom)
    ((original_core_opposite_commutator E m hy hW hcore).trans hQ)
  rw [map_commutator] at h
  have hlR : l ∈ normalizer (L.pCoreIn 2 : Set G) :=
    (L.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image L (pCore 2 L))) (E.L₁_le hl)
  have hlQ : l ∈ normalizer (E.G₁.pCoreIn 2 : Set G) :=
    (E.G₁.le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image E.G₁ (pCore 2 E.G₁)))
      ((residualIn_le _).trans inf_le_right hl)
  have heR : (L.pCoreIn 2).map (MulAut.conj l).toMonoidHom = L.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp hlR
  have heQ : (E.G₁.pCoreIn 2).map (MulAut.conj l).toMonoidHom = E.G₁.pCoreIn 2 :=
    mem_normalizer_iff_map_conj_eq.mp hlQ
  rwa [heR, heQ] at h

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic
