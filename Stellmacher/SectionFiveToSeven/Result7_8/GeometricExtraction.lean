module
public import Stellmacher.SectionFiveToSeven.Result7_8.PrescribedActorConfiguration
public import Stellmacher.SectionFiveToSeven.Result7_6.GraphFacts
public import Stellmacher.SectionFiveToSeven.Result7_6.CoreFacts
public import Stellmacher.TwoResidualConjugator
public import Theory.GroupTheory.DihedralTwoCore

/-!
# Geometric extraction of a prescribed (7.8) actor

Convert the proved quotient configuration of (7.8) into its geometric form
at an actual graph edge. The generated subgroup E and its actor coatom A₀
remain fixed, so an additional Baumann bound for those witnesses is retained
by callers. Replace the supplied self-containing conjugator by x in O²(E),
preserving A conjugated by x, and define the new neighbor m by Γ.act x⁻¹ l.
The result identifies A₀ with A intersect G_m, keeps the prescribed actor
outside G_m, and proves generation at the new edge and [E,A₀]≤Q_d.

The Frattini containment makes the image of A in the actual quotient model
elementary abelian. Hence its second product factor is abelian, and the
odd-dihedral product has central two-core. Since A₀ lies in O₂(E), its
commutators with E lie in the prescribed kernel E intersect Q_d. This puts
A₀ inside G_m. Conversely an outside-coatom actor in G_m would generate E
with A conjugated by x inside a two-group: it normalizes Q_m, which contains
that conjugate of A. This contradicts A₀=A intersect O₂(E). Conjugation by
x in E transfers the original edge generation to the new edge.

The quotient model is used with its stated kernel and actor-image data;
its abstract product equivalence is not assumed to identify a particular
central factor. All raw inputs here are conclusions of the proved (7.8)
configuration, with either ordinary or selected-Baumann extraction.
This generic edge theorem serves (8.4)(6) and (9.3). Its existing SectionNine
namespace and public names are preserved for current consumers.
Source: Stellmacher (9.3)(i)–(v), Journal of Algebra 190 (1997), p.49,
`refs/files/stellmacher-n-group.pdf`, applying (7.8) and Sylow conjugacy.
-/
namespace Stellmacher.SectionNine
open SectionsFiveToSeven CosetGraphContext SevenSix
open scoped Pointwise commutatorElement
universe u
attribute [local instance] QuotientDihedralProduct.barL_group QuotientDihedralProduct.barL_finite

public structure NineThreeGeometricData
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (Γ : CosetGraphContext G S P1 P2) (d l : Γ.Vertex)
    (A E A0 : Subgroup G) (actor : G) where
  x : G
  residual_mem : x ∈ twoResidualAmbient E
  group_le : E ≤ stabilizer Γ d
  generated : E = A ⊔ A.conjBy x
  neighbor : Γ.act x⁻¹ l ∈ neighborhood Γ d
  actor_outside : actor ∉ stabilizer Γ (Γ.act x⁻¹ l)
  coatom_eq : A0 = A ⊓ stabilizer Γ (Γ.act x⁻¹ l)
  coatom_card : Nat.card A = 2 * Nat.card A0
  conjugate_core_le : A.conjBy x ≤ q Γ (Γ.act x⁻¹ l)
  edge_generated : E ⊔ (stabilizer Γ d ⊓ stabilizer Γ (Γ.act x⁻¹ l)) = stabilizer Γ d
  actor_generated : ∀ b : G, b ∈ A → b ∉ stabilizer Γ (Γ.act x⁻¹ l) →
    E = Subgroup.closure ({b} : Set G) ⊔ A.conjBy x
  coatom_commutator : ⁅E, A0⁆ ≤ q Γ d

private theorem quotient_coatom_commutator
    {G : Type u} [Group G] [Finite G]
    (E Q A A0 : Subgroup G) (hAE : A ≤ E) (hA0 : A0 ≤ A)
    (hAp : IsPGroup 2 A) (hPhi : SectionsFiveToSeven.frattiniAmbient A ≤ Q)
    (hA0core : A0 ≤ twoCoreAmbient E)
    (model : QuotientDihedralProduct E Q A0) : ⁅E,A0⁆ ≤ Q := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : A →* model.barL := model.quotientMap.comp (Subgroup.inclusion hAE)
  have hPhiKer : frattini A ≤ f.ker := by
    intro a ha
    change model.quotientMap (Subgroup.inclusion hAE a) = 1
    apply MonoidHom.mem_ker.mp
    rw [model.quotient_kernel]
    exact ⟨hAE a.property, hPhi (Subgroup.mem_map_of_mem A.subtype ha)⟩
  let _ := elementaryAbelian_range_of_frattini_le_ker f hAp hPhiKer
  have hbar : model.barA0 ≤ f.range := by
    rw [model.barA0_image]
    rintro z ⟨a, _, rfl⟩
    exact ⟨⟨a, hA0 a.property⟩, rfl⟩
  let _ : IsMulCommutative model.barA0 :=
    IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
      setLike_mul_comm (s := f.range) (hbar ha) (hbar hb)
  have hcentral := dihedralProduct_twoCore_le_center model.barL model.barA0
    (model.p ^ model.n) model.p_odd.pow model.model
  have hmap : (pCore 2 E).map model.quotientMap ≤ pCore 2 model.barL :=
    le_sSup ⟨pCore_normal.map model.quotientMap model.quotient_surjective,
      pCore_isPGroup.map model.quotientMap⟩
  rw [Subgroup.commutator_comm]
  apply Subgroup.commutator_le.mpr
  intro a ha e he
  obtain ⟨aE, haE, hae⟩ := hA0core ha
  change (aE : G) = a at hae
  let eE : E := ⟨e, he⟩
  have hc := Subgroup.mem_center_iff.mp
    (hcentral (hmap (Subgroup.mem_map_of_mem model.quotientMap haE)))
      (model.quotientMap eE)
  have hk : ⁅aE,eE⁆ ∈ model.quotientMap.ker := by
    apply MonoidHom.mem_ker.mpr
    rw [map_commutatorElement, commutatorElement_def, ← hc]
    simp [mul_assoc]
  have hq := (model.quotient_kernel ▸ hk).2
  change ⁅(aE : G), e⁆ ∈ Q at hq
  simpa only [hae] using hq

public theorem nine_three_geometric_extraction
    {G : Type u} [Group G] [Finite G] {S P1 P2 : Subgroup G}
    (h : SectionSevenHypotheses G S P1 P2)
    (Γ : CosetGraphContext G S P1 P2)
    (d l : Γ.Vertex) (hl : l ∈ neighborhood Γ d)
    (A E A0 : Subgroup G) (hA : A ≤ q Γ l)
    (hPhi : SectionsFiveToSeven.frattiniAmbient A ≤ q Γ d)
    (actor : G) (haA : actor ∈ A) (ha0 : actor ∉ A0)
    (y : G) (hyE : y ∈ E) (hEP : E ≤ stabilizer Γ d)
    (hgen : E = A ⊔ A.conjBy y) (h0A : A0 ≤ A)
    (hcard : Nat.card A = 2 * Nat.card A0)
    (h0core : A0 = A ⊓ twoCoreAmbient E)
    (hedge : E ⊔ (stabilizer Γ l ⊓ stabilizer Γ d) = stabilizer Γ d)
    (hmodel : Nonempty (QuotientDihedralProduct E (q Γ d) A0))
    (hby : ∀ b : G, b ∈ A → b ∉ A0 →
      E = Subgroup.closure ({b} : Set G) ⊔ A.conjBy y) :
    Nonempty (NineThreeGeometricData Γ d l A E A0 actor) := by
  classical
  obtain ⟨x,hxR,hxA⟩ := exists_twoResidual_conjugator A E y hyE hgen
  have hxE : x ∈ E := Subgroup.map_subtype_le _ hxR
  have hxP : x ∈ stabilizer Γ d := hEP hxE
  have hAE : A ≤ E := hgen ▸ le_sup_left
  have hgenx : E = A ⊔ A.conjBy x := by rw [hxA]; exact hgen
  have hbx (b : G) (hb : b ∈ A) (hb0 : b ∉ A0) :
      E = Subgroup.closure ({b} : Set G) ⊔ A.conjBy x := by rw [hxA]; exact hby b hb hb0
  let m := Γ.act x⁻¹ l
  have hGm : stabilizer Γ m = (stabilizer Γ l).conjBy x := by
    rw [show m = Γ.act x⁻¹ l from rfl, stabilizer_act, inv_inv]
    rfl
  have hQm : q Γ m = (q Γ l).conjBy x := by
    rw [show m = Γ.act x⁻¹ l from rfl, q_act, inv_inv]
    rfl
  have hAxQm : A.conjBy x ≤ q Γ m := by
    rw [hQm]
    exact Subgroup.map_mono hA
  have hQlGl : q Γ l ≤ stabilizer Γ l := by
    rw [q,Γ.twoCoreAt_def]
    exact Subgroup.map_subtype_le _
  have hQdGl : q Γ d ≤ stabilizer Γ l :=
    ((lemma_seven_three h Γ).sylow_and_core d l hl default).2.2
  have hA2 : IsPGroup 2 A := by
    have hQ2 : IsPGroup 2 (q Γ l) := by
      rw [q, Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := stabilizer Γ l)).map _
    exact hQ2.to_le hA
  have h0Q : A0 ≤ twoCoreAmbient E := h0core ▸ inf_le_right
  obtain ⟨model⟩ := hmodel
  have hcomm := quotient_coatom_commutator E (q Γ d) A A0 hAE h0A hA2 hPhi h0Q model
  have h0m : A0 ≤ stabilizer Γ m := by
    intro a ha
    have hdelta : x⁻¹ * a * x * a⁻¹ ∈ q Γ d := by
      simpa only [commutatorElement_def, inv_inv] using
        hcomm (Subgroup.commutator_mem_commutator (E.inv_mem hxE) ha)
    have hconj : x⁻¹ * a * x ∈ stabilizer Γ l := by
      have hm := (stabilizer Γ l).mul_mem (hQdGl hdelta) (hQlGl (hA (h0A ha)))
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm
    rw [hGm]
    exact ⟨x⁻¹ * a * x, hconj, by simp [mul_assoc]⟩
  have hm0 : A ⊓ stabilizer Γ m ≤ A0 := by
    intro b hb
    by_contra hb0
    let C := Subgroup.closure ({b} : Set G)
    have hCA : C ≤ A := (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr hb.1)
    have hCp : IsPGroup 2 C := hA2.to_le hCA
    have hQp : IsPGroup 2 (q Γ m) := by
      rw [q, Γ.twoCoreAt_def]
      exact (pCore_isPGroup (p := 2) (G := stabilizer Γ m)).map _
    have hCN : C ≤ Subgroup.normalizer (q Γ m : Set G) :=
      (Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr
        (stabilizer_le_normalizer_q Γ m hb.2))
    have hEp : IsPGroup 2 E := by
      apply (hCp.to_sup_of_normal_right' hQp hCN).to_le
      rw [hbx b hb.1 hb0]
      exact sup_le_sup_left hAxQm C
    have htop : (⊤ : Subgroup E) ≤ pCore 2 E :=
      le_sSup ⟨inferInstance, hEp.to_subgroup ⊤⟩
    have hbE := hAE hb.1
    have hbcore : b ∈ twoCoreAmbient E :=
      Subgroup.mem_map_of_mem E.subtype (htop (show (⟨b,hbE⟩ : E) ∈ ⊤ from trivial))
    exact hb0 (h0core.symm ▸ ⟨hb.1,hbcore⟩)
  have h0eq : A0 = A ⊓ stabilizer Γ m := le_antisymm (le_inf h0A h0m) hm0
  have haOut : actor ∉ stabilizer Γ m := fun ha => ha0 (hm0 ⟨haA,ha⟩)
  have hfixd : Γ.act x⁻¹ d = d :=
    (Set.ext_iff.mp (Γ.stabilizer_def d) x⁻¹).mp ((stabilizer Γ d).inv_mem hxP)
  have hm : m ∈ neighborhood Γ d := by
    apply (SevenSix.mem_neighborhood_iff_adjacent Γ).mpr
    have ha := adjacent_act Γ x⁻¹ ((SevenSix.mem_neighborhood_iff_adjacent Γ).mp hl)
    simpa only [hfixd] using ha
  have hEmap : E.conjBy x = E := Subgroup.mem_normalizer_iff_map_conj_eq.mp (E.le_normalizer hxE)
  have hPmap : (stabilizer Γ d).conjBy x = stabilizer Γ d :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp ((stabilizer Γ d).le_normalizer hxP)
  have hnewedge : E ⊔ (stabilizer Γ d ⊓ stabilizer Γ m) = stabilizer Γ d := by
    have hh := congrArg (Subgroup.map (MulAut.conj x).toMonoidHom) hedge
    rw [Subgroup.map_sup, Subgroup.map_inf _ _ _ (MulAut.conj x).injective] at hh
    change E.conjBy x ⊔ ((stabilizer Γ l).conjBy x ⊓
      (stabilizer Γ d).conjBy x) = (stabilizer Γ d).conjBy x at hh
    rw [hEmap,hPmap,← hGm,inf_comm] at hh
    exact hh
  refine ⟨⟨x,hxR,hEP,hgenx,hm,haOut,h0eq,hcard,hAxQm,hnewedge,?_,hcomm⟩⟩
  intro b hb hbOut
  exact hbx b hb (fun hb0 => hbOut (h0m hb0))
end Stellmacher.SectionNine
