module

public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Elementary
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.OppositeCore.NaturalQuotient.Normalizers
public import CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.RadicalAction.Cartan
public import Theory.GroupAction.CoprimeHall

/-!
# Applying 11.5.6 to the opposite-core Cartan commutator

For P=[Q,X₁], coprime commutator idempotence gives [P,X₁]=P. Once the
full Cartan preserves Q, it preserves P as well, so [P,X]=P. The literal
elementary quotient supplies Φ(P)≤Φ(Q)≤N≤O₂(G₁). Part (4) now applies
with every Frattini and Sylow premise discharged. Part (5) puts P in
O₂(KT), and restriction bounds [P,K] by O₂(K). Relative normality of
K and Y in G₁ combines the two bounds into [P,KY]≤O₂(KY).
Source: Aschbacher--Smith 11.5.6(4--5), 11.5.7, printed pp.781,783.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement
namespace CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient

private theorem normalizes_commutator {G : Type*} [Group G] (H A B : Subgroup G)
    (hA : H ≤ normalizer (A : Set G)) (hB : H ≤ normalizer (B : Set G)) :
    H ≤ normalizer (⁅A,B⁆ : Subgroup G) := by
  intro h hh
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator, mem_normalizer_iff_map_conj_eq.mp (hA hh),
    mem_normalizer_iff_map_conj_eq.mp (hB hh)]

private theorem coprime_commutator_idempotent {G : Type*} [Group G] [Finite G]
    (Q A : Subgroup G) (hAQ : A ≤ normalizer (Q : Set G))
    (hq : IsPGroup 2 Q) (hodd : Odd (Nat.card A)) : ⁅Q,A⁆ = ⁅⁅Q,A⁆,A⁆ := by
  have hcop : Nat.Coprime (Nat.card A) (Nat.card Q) := by
    obtain ⟨n,hn⟩ := hq.exists_card_eq
    rw [hn]
    exact hodd.coprime_two_right.pow_right n
  let : Group.IsNilpotent Q := hq.isNilpotent
  let : Normalizes A Q := ⟨hAQ⟩
  have hm := commutatorAction_subgroup_conj_map_eq_commutator Q A hAQ
  apply le_antisymm
  · calc
      ⁅Q,A⁆ = (commutatorAction₂ (A := A) (G := Q)).map Q.subtype := by
        rw [commutatorAction₂_eq_commutatorAction_of_solvable_coprime inferInstance hcop, hm]
      _ ≤ ⁅⁅Q,A⁆,A⁆ := ?_
    rw [commutatorAction₂, commutatorSubgroup, MonoidHom.map_closure, closure_le]
    rintro _ ⟨v,⟨a,q,hq,rfl⟩,rfl⟩
    have hqm : (q : G) ∈ ⁅Q,A⁆ := by
      rw [← hm]
      exact mem_map_of_mem _ hq
    change (q : G)⁻¹ * ((a : G) * (q : G) * (a : G)⁻¹) ∈ ⁅⁅Q,A⁆,A⁆
    simpa only [commutatorElement_def, inv_inv, mul_assoc] using
      commutator_mem_commutator ((⁅Q,A⁆).inv_mem hqm) a.property
  · exact le_normalizer_iff_commutator_le_left.mp (normalizer_commutator_ge_right Q A)

open CFSG.Quasithin.Chapter12.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
    {D : ChosenModule T L V} (E : Geometry D)

/-- Normality of X₁ in X follows from its actual quotient-centralizer definition. -/
theorem cartan_normalizes_kernel (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁) :
    E.X ≤ normalizer (cartanKernel E : Set G) := by
  have hn : E.X ≤ normalizer ((L ⊓ E.G₁ : Subgroup G) : Set G) :=
    (le_inf (hXL.trans L.le_normalizer) (hXG.trans E.G₁.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hL : E.X ≤ normalizer (E.L₁ : Set G) :=
    hn.trans (normalizer_le_normalizer_characteristic_image _ (solvableResidual _))
  exact (le_inf E.X.le_normalizer
    (hL.trans (normalizer_normalizes_coreQuotientCentralizer E.L₁))).trans
    inf_normalizer_le_normalizer_inf

/-- The full-commutator premise of 11.5.6(4) is derived from coprime action. -/
theorem cartan_commutator_full (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) y)
    (hodd : Odd (Nat.card (cartanKernel E)))
    (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hXQ : E.X ≤ normalizer (corePair (auxiliaryW E) y : Set G)) :
    ⁅⁅corePair (auxiliaryW E) y,cartanKernel E⁆,E.X⁆ =
      ⁅corePair (auxiliaryW E) y,cartanKernel E⁆ := by
  have hp := source_corePair_properties E m hy hcore
  have hIQ := (normal_subgroupOf_iff_le_normalizer
    (hp.1.trans (pCoreIn_le 2 _))).mp hp.2.1
  have hid := coprime_commutator_idempotent _ _ (hXI.trans hIQ)
    ((isPGroup_pCoreIn 2 _).to_le hp.1) hodd
  apply le_antisymm
  · exact le_normalizer_iff_commutator_le_left.mp
      (normalizes_commutator _ _ _ hXQ (cartan_normalizes_kernel E hXL hXG))
  · exact hid.le.trans (commutator_mono le_rfl (show cartanKernel E ≤ E.X from inf_le_left))

/-- The Cartan commutator can equally be computed using the full opposite
two-core. Coprime idempotence and [O₂(I),I]≤Q supply the reverse inclusion. -/
theorem core_cartan_commutator_eq (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) y)
    (hodd : Odd (Nat.card (cartanKernel E))) :
    ⁅(oppositeJoin (auxiliaryW E) y).pCoreIn 2,cartanKernel E⁆ =
      ⁅corePair (auxiliaryW E) y,cartanKernel E⁆ := by
  have hp := source_corePair_properties E m hy hcore
  have hn := hXI.trans ((oppositeJoin (auxiliaryW E) y).le_normalizer.trans
    (normalizer_le_normalizer_characteristic_image _ (pCore 2 _)))
  have hid := coprime_commutator_idempotent _ _ hn (isPGroup_pCoreIn 2 _) hodd
  exact le_antisymm
    (hid.le.trans (commutator_mono ((commutator_mono le_rfl hXI).trans hp.2.2) le_rfl))
    (commutator_mono hp.1 le_rfl)

/-- The stabilizer preserves P when its conjugates of the actual Cartan
kernel are conjugate under O₂(I). The geometric torus comparison is kept
explicit; normalization of P is derived here. -/
theorem stabilizer_normalizes_commutator_of_core_conjugacy
    (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) y)
    (hodd : Odd (Nat.card (cartanKernel E)))
    (hconj : ∀ s ∈ oppositePointStabilizer E y,
      ∃ r ∈ (oppositeJoin (auxiliaryW E) y).pCoreIn 2,
        (cartanKernel E).map (MulAut.conj s).toMonoidHom =
          (cartanKernel E).map (MulAut.conj r).toMonoidHom) :
    oppositePointStabilizer E y ≤
      normalizer (⁅corePair (auxiliaryW E) y,cartanKernel E⁆ : Subgroup G) := by
  have hp := source_corePair_properties E m hy hcore
  have hIQ := (normal_subgroupOf_iff_le_normalizer
    (hp.1.trans (pCoreIn_le 2 _))).mp hp.2.1
  have hRP : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      normalizer (⁅corePair (auxiliaryW E) y,cartanKernel E⁆ : Subgroup G) := by
    rw [← core_cartan_commutator_eq E m hy hcore hXI hodd]
    exact normalizer_commutator_ge_left _ _
  intro s hs
  obtain ⟨r,hr,he⟩ := hconj s hs
  apply mem_normalizer_iff_map_conj_eq.mpr
  rw [map_commutator,
    mem_normalizer_iff_map_conj_eq.mp (opposite_stabilizer_normalizes_corePair E y hs)]
  change ⁅corePair (auxiliaryW E) y,(cartanKernel E).map (MulAut.conj s).toMonoidHom⁆ = _
  rw [he]
  have hrQ : (corePair (auxiliaryW E) y).map (MulAut.conj r).toMonoidHom =
      corePair (auxiliaryW E) y :=
    mem_normalizer_iff_map_conj_eq.mp (hIQ (pCoreIn_le 2 _ hr))
  calc
    _ = (⁅corePair (auxiliaryW E) y,cartanKernel E⁆).map (MulAut.conj r).toMonoidHom := by
      rw [map_commutator, hrQ]
    _ = _ := mem_normalizer_iff_map_conj_eq.mp (hRP hr)

/-- The complete Cartan bound for P=[Q,X₁], including its actual Frattini premise.
Only the preceding 11.5.6 conclusions and geometric normalizations are inputs. -/
theorem cartan_commutator_KY_le_core (m : MarkedFlag E) {y : G} (hy : y ∈ L)
    (hV : V ≤ E.G₁.pCoreIn 2) (hW : E.W ≤ E.G₁.pCoreIn 2)
    (hPhi : (frattini (auxiliaryW E)).map (auxiliaryW E).subtype ≤ E.V₁)
    (hcore : (oppositeJoin (auxiliaryW E) y).pCoreIn 2 ≤
      (L ⊔ (T : Subgroup G)).pCoreIn 2)
    (hXI : cartanKernel E ≤ oppositeJoin (auxiliaryW E) y)
    (hodd : Odd (Nat.card (cartanKernel E)))
    (hXL : E.X ≤ L) (hXG : E.X ≤ E.G₁)
    (hXpoint : E.X ≤ normalizer (E.V₁.map (MulAut.conj y).toMonoidHom : Set G))
    (hfour : ∀ P : Subgroup G, ⁅P,E.X⁆ = P → P ≤ (T : Subgroup G) →
      (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 → ⁅P,E.Y⁆ ≤ E.Y.pCoreIn 2)
    (hfive : ⁅(L ⊔ (T : Subgroup G)).pCoreIn 2,E.X⁆ ≤
      (E.K ⊔ (T : Subgroup G)).pCoreIn 2) :
    ⁅⁅corePair (auxiliaryW E) y,cartanKernel E⁆,E.K ⊔ E.Y⁆ ≤
      (E.K ⊔ E.Y).pCoreIn 2 := by
  have hXQ := cartan_normalizes_corePair E y hXG hXpoint
  let Q := corePair (auxiliaryW E) y
  let P := ⁅Q,cartanKernel E⁆
  have hp := source_corePair_properties E m hy hcore
  have hIQ := (normal_subgroupOf_iff_le_normalizer
    (hp.1.trans (pCoreIn_le 2 _))).mp hp.2.1
  have hPQ : P ≤ Q := le_normalizer_iff_commutator_le_left.mp (hXI.trans hIQ)
  have hQT : Q ≤ T := by
    apply (hp.1.trans hcore).trans
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (L ⊔ (T : Subgroup G)) (T.subtype le_sup_right)
  have hPG : P ≤ E.G₁ := hPQ.trans (hQT.trans m.sylow_le_point_normalizer)
  have hPphi : (frattini P).map P.subtype ≤ E.G₁.pCoreIn 2 :=
    (frattini_image_le_of_le hPQ ((isPGroup_pCoreIn 2 _).to_le hp.1)).trans
      ((corePair_frattini_le_denominator E m hy hW hPhi hcore).trans
        (pairDenominator_le_core E hV hW y))
  have hfull := cartan_commutator_full E m hy hcore hXI hodd hXL hXG hXQ
  have hPY := hfour P hfull (hPQ.trans hQT) hPphi
  have hPKT : P ≤ (E.K ⊔ (T : Subgroup G)).pCoreIn 2 :=
    (commutator_mono (hp.1.trans hcore) (show cartanKernel E ≤ E.X from inf_le_left)).trans hfive
  have hKQ : E.K ≤ normalizer
      (((E.K ⊔ (T : Subgroup G)).pCoreIn 2) : Set G) :=
    (le_sup_left.trans (E.K ⊔ (T : Subgroup G)).le_normalizer).trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))
  have hPK : ⁅P,E.K⁆ ≤ E.K.pCoreIn 2 :=
    (le_inf (le_normalizer_iff_commutator_le_right.mp (hPG.trans E.G₁_normalizes_K))
      ((commutator_mono hPKT le_rfl).trans
        (le_normalizer_iff_commutator_le_left.mp hKQ))).trans
      (inf_pCoreIn_le_of_le 2 (show E.K ≤ E.K ⊔ (T : Subgroup G) from le_sup_left))
  have hKY : E.K ⊔ E.Y ≤ E.G₁ := sup_le E.K_le_G₁ E.Y_le_G₁
  have hKcore := pCoreIn_mono_of_normalizes (p := 2)
    (show E.K ≤ E.K ⊔ E.Y from le_sup_left) (hKY.trans E.G₁_normalizes_K)
  have hYcore := pCoreIn_mono_of_normalizes (p := 2)
    (show E.Y ≤ E.K ⊔ E.Y from le_sup_right) (hKY.trans (G₁_normalizes_Y E))
  change ⁅P,E.K ⊔ E.Y⁆ ≤ _
  rw [commutator_comm]
  apply commutator_sup_le_of_relative_normal (E.K ⊔ E.Y) E.K E.Y P _
    ((E.K ⊔ E.Y).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 _))) le_sup_left le_sup_right
  · rw [commutator_comm]
    exact hPK.trans hKcore
  · rw [commutator_comm]
    exact hPY.trans hYcore

end CFSG.Quasithin.Chapter11.ChosenNaturalSource.Closure.Symplectic.NaturalQuotient
