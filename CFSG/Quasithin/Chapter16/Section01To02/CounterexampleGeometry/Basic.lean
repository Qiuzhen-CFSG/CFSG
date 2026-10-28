module

public import CFSG.Quasithin.Chapter16.Section01To02.SourceHypothesis
public import Theory.GroupTheory.GeneralizedFitting.RelativeComponent
public import Theory.GroupTheory.PResidual.PrimeTo

/-!
# The nonnormal component geometry in §16.2

We retain the actual local orbit L₀ = ⟨L^{C_G(z)}⟩ and H = N_G(L₀).
Conjugation in this module follows the book: L^g = g⁻¹ L g. A two-element
orbit witness records the output still to be constructed from A.3.8; it is
not an additional hypothesis of Theorem 16.2.4.

The normalizer argument places all components in N_G(L^u), using the
normality of C_G(L^u) there. The printed proof places L^u inside its own
centralizer, which is impossible for a quasisimple group.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*, combined
1 March 2004 manuscript, pp.1174–1176, Lemmas 16.2.5–16.2.10.
The source-theorem assembly, including construction of the witnesses below,
remains separate from these conditional deductions.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter16.CounterexampleGeometry
open Subgroup Theory.GroupTheory
universe u
variable {G : Type u} [Group G]

/-- Right conjugation, matching the superscripts in the source. -/
def conjugate (A : Subgroup G) (g : G) : Subgroup G :=
  A.map (MulAut.conj g⁻¹).toMonoidHom

@[simp] theorem conjugate_one (A : Subgroup G) : conjugate A 1 = A := by
  have he : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [conjugate, inv_one, he, map_id]

@[simp] theorem conjugate_conjugate (A : Subgroup G) (g h : G) :
    conjugate (conjugate A g) h = conjugate A (g * h) := by
  simp only [conjugate, map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem conjugate_injective (g : G) : Function.Injective (fun A : Subgroup G => conjugate A g) := by
  intro A B he
  have := congrArg (fun X => conjugate X g⁻¹) he
  simpa using this

theorem mem_normalizer_iff_conjugate_eq (A : Subgroup G) (g : G) :
    g ∈ normalizer (A : Set G) ↔ conjugate A g = A := by
  rw [← Subgroup.inv_mem_iff (H := normalizer (A : Set G)),
    mem_normalizer_iff_map_conj_eq]
  rfl

theorem normalizer_conjugate (A : Subgroup G) (g : G) :
    normalizer (conjugate A g : Set G) = conjugate (normalizer (A : Set G)) g :=
  (map_equiv_normalizer_eq A (MulAut.conj g⁻¹)).symm

/-- The marked second component and the subgroup ⟨z⟩L^u of 16.2.6–8. -/
def involutionContainer (z : G) (L : Subgroup G) (u : G) : Subgroup G :=
  zpowers z ⊔ conjugate L u

/-- The counterexample assumptions, without any conclusions of 16.2.5–10. -/
structure CounterexampleSetup [Finite G] (K : GroupClass.{u})
    (T : Sylow 2 G) (z : G) (L : Subgroup G) : Prop where
  global : Hypothesis1611 K G
  localSetup : CentralComponentSetup T z L
  not_normal : ¬ (L.subgroupOf (involutionCentralizer z)).Normal

/-- A two-element orbit witness. Its construction from the counterexample
and A.3.8 is an outstanding proof obligation, not a source assumption. -/
structure TwoComponentOrbit (T : Sylow 2 G) (z : G) (L : Subgroup G) (u : G) : Prop where
  mem_sylow : u ∈ T
  moved : conjugate L u ≠ L
  orbit : ∀ g ∈ involutionCentralizer z, conjugate L g = L ∨
    conjugate L g = conjugate L u

/-- The concrete possibilities of 16.2.5, preserving the exceptional cover. -/
inductive ComponentAlternative (L : Type u) [Group L] : Prop
  | linear_even (n : ℕ) (hn : 2 ≤ n) (iso : ClassicalGroup.IsPSL L 2 (2 ^ n))
  | suzuki (m : ℕ) (hm : 1 ≤ m)
      (iso : Nonempty (L ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup m))
  | linear_odd (p : ℕ) (hp : p.Prime) (hodd : Odd p)
      (iso : ClassicalGroup.IsPSL L 2 p)
  | covered_suzuki_eight (nontrivial_core : pCore 2 L ≠ ⊥)
      (iso : Nonempty ((L ⧸ pCore 2 L) ≃* BenderSuzuki.MatrixGroups.SuzukiMatrixGroup 1))

/-- The universal conclusion of 16.2.6(1), used conditionally below. -/
def ComponentPersistence (z : G) (L : Subgroup G) (u : G) : Prop :=
  ∀ t ∈ involutionContainer z L u, orderOf t = 2 → IsCentralizerComponent t L

/-- Clause (2) of A.1.34 as an explicit input, under the ambient quasithin
hypothesis supplied by `CounterexampleSetup`. It quantifies over K-subgroups
and actual isomorphic components, rather than over component-family labels. -/
def ComponentPairExhaustion (K : GroupClass.{u}) (G : Type u) [Group G] : Prop :=
  ∀ M : Subgroup G, IsKGroup K M →
    ∀ A B : Subgroup G, IsComponentIn A M → IsComponentIn B M →
      A ≠ B → Nonempty (A ≃* B) →
      ∀ D : Subgroup G, IsComponentIn D M → Nonempty (D ≃* A) → D = A ∨ D = B

variable {T : Sylow 2 G} {z : G} {L : Subgroup G} {u : G}

/-- The original component lies in the local orbit. -/
theorem component_le_closure : L ≤ localComponentClosure z L := le_componentOrbit _ _

/-- The orbit stays inside C_G(z). -/
theorem closure_le_centralizer (h : CentralComponentSetup T z L) :
    localComponentClosure z L ≤ involutionCentralizer z :=
  (componentOrbit_le_sup _ _).trans (sup_le h.component.1 le_rfl)

/-- The whole centralizer, and hence T, normalizes the local orbit. -/
theorem centralizer_le_localNormalizer :
    involutionCentralizer z ≤ localComponentNormalizer z L := le_normalizer_componentOrbit _ _

theorem sylow_le_localNormalizer (h : CentralComponentSetup T z L) :
    (T : Subgroup G) ≤ localComponentNormalizer z L :=
  h.sylow_centralizes.trans centralizer_le_localNormalizer

/-- Each local conjugate is still an ordinary component of C_G(z). -/
theorem local_conjugate_component (h : CentralComponentSetup T z L)
    {g : G} (hg : g ∈ involutionCentralizer z) :
    IsComponentIn (conjugate L g) (involutionCentralizer z) := by
  have hc : conjugate (involutionCentralizer z) g = involutionCentralizer z :=
    (mem_normalizer_iff_conjugate_eq _ _).mp (Subgroup.le_normalizer hg)
  have hm := (show IsComponentIn L (involutionCentralizer z) from h.component).map
    (MulAut.conj g⁻¹)
  change IsComponentIn (conjugate L g) (conjugate (involutionCentralizer z) g) at hm
  rwa [hc] at hm

namespace TwoComponentOrbit
variable (o : TwoComponentOrbit T z L u) (h : CentralComponentSetup T z L)
include o h

theorem swap_mem_localNormalizer : u ∈ localComponentNormalizer z L :=
  sylow_le_localNormalizer h o.mem_sylow

theorem swapped_component : IsComponentIn (conjugate L u) (involutionCentralizer z) :=
  local_conjugate_component h (h.sylow_centralizes o.mem_sylow)

theorem commute : ⁅L, conjugate L u⁆ = ⊥ :=
  (show IsComponentIn L (involutionCentralizer z) from h.component).commutator_eq_bot_of_ne
    (o.swapped_component h) o.moved.symm

theorem closure_eq_pair : localComponentClosure z L = L ⊔ conjugate L u := by
  apply le_antisymm
  · apply iSup_le
    intro g
    have ho := o.orbit (g : G)⁻¹ ((involutionCentralizer z).inv_mem g.property)
    have he : L.map (MulAut.conj (g : G)).toMonoidHom = conjugate L (g : G)⁻¹ := by
      simp [conjugate]
    rw [he]
    rcases ho with he | he
    · rw [he]; exact le_sup_left
    · rw [he]; exact le_sup_right
  · refine sup_le component_le_closure ?_
    exact le_iSup (fun g : involutionCentralizer z =>
      L.map (MulAut.conj (g : G)).toMonoidHom)
      ⟨u⁻¹, (involutionCentralizer z).inv_mem (h.sylow_centralizes o.mem_sylow)⟩

theorem swap_twice : conjugate (conjugate L u) u = L := by
  rcases o.orbit (u * u) ((involutionCentralizer z).mul_mem
      (h.sylow_centralizes o.mem_sylow) (h.sylow_centralizes o.mem_sylow)) with he | he
  · simpa using he
  · have : conjugate L u = L := conjugate_injective u (by simpa using he)
    exact (o.moved this).elim

end TwoComponentOrbit

namespace CounterexampleSetup
variable [Finite G] {K : GroupClass.{u}} (c : CounterexampleSetup K T z L)
include c

/-- Properness is available from simplicity before the geometry is developed. -/
theorem centralizer_ne_top : involutionCentralizer z ≠ ⊤ := by
  let := c.global.simple
  exact twoLocal_ne_top_of_nonabelian_simple c.global.nonabelian
    (isTwoLocal_involution_centralizer c.localSetup.involution)

/-- A proper nontrivial subgroup of a simple group has proper normalizer. -/
private theorem proper_normalizer {A : Subgroup G} (ha : A ≠ ⊥)
    (hac : A ≤ involutionCentralizer z) : normalizer (A : Set G) ≠ ⊤ := by
  intro he
  let := c.global.simple
  let : A.Normal := normalizer_eq_top_iff.mp he
  rcases (inferInstance : A.Normal).eq_bot_or_eq_top with he | he
  · exact ha he
  · exact c.centralizer_ne_top (top_unique (he ▸ hac))

theorem component_normalizer_ne_top : normalizer (L : Set G) ≠ ⊤ :=
  c.proper_normalizer (show IsComponentIn L (involutionCentralizer z) from
    c.localSetup.component).ne_bot c.localSetup.component.1

theorem localNormalizer_ne_top : localComponentNormalizer z L ≠ ⊤ := by
  apply c.proper_normalizer _ (closure_le_centralizer c.localSetup)
  intro he
  have hb : L = ⊥ := le_bot_iff.mp (he ▸ component_le_closure (z := z) (L := L))
  exact (show IsComponentIn L (involutionCentralizer z) from c.localSetup.component).ne_bot hb

end CounterexampleSetup

/-- Persistence puts L inside the centralizer of the swapped factor as a
component. The latter centralizer is normal in N_G(L^u), so L is a component
of that normalizer too. This is the corrected ambient group for 16.2.7. -/
theorem component_in_swapped_normalizer (h : CentralComponentSetup T z L)
    (o : TwoComponentOrbit T z L u) (persist : ComponentPersistence z L u)
    {t : G} (ht : t ∈ conjugate L u) (ht2 : orderOf t = 2) :
    IsComponentIn L (normalizer (conjugate L u : Set G)) := by
  have hLC : L ≤ centralizer (conjugate L u : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (o.commute h)
  have hCC : centralizer (conjugate L u : Set G) ≤ involutionCentralizer t :=
    centralizer_le (Set.singleton_subset_iff.mpr ht)
  have hc := (show IsComponentIn L (involutionCentralizer t) from
    persist t ((show conjugate L u ≤ involutionContainer z L u from le_sup_right) ht) ht2).restrict hLC hCC
  exact hc.of_subnormal (centralizer_le_normalizer _) (inferInstance :
    ((centralizer (conjugate L u : Set G)).subgroupOf
      (normalizer (conjugate L u : Set G))).Normal).isSubnormal

/-- The A.1.34(2) contradiction in the correct normalizer. Neither L^u nor
its nonabelian copies are asserted to lie in their own centralizers. -/
theorem swapped_normalizer_le_component_normalizer [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairExhaustion K G) (persist : ComponentPersistence z L u)
    {t : G} (ht : t ∈ conjugate L u) (ht2 : orderOf t = 2) :
    normalizer (conjugate L u : Set G) ≤ normalizer (L : Set G) := by
  let M := normalizer (conjugate L u : Set G)
  have hLM : IsComponentIn L M := component_in_swapped_normalizer c.localSetup o persist ht ht2
  have hUM : IsComponentIn (conjugate L u) M := (o.swapped_component c.localSetup).normalizer
  have hMproper : M ≠ ⊤ := by
    apply c.proper_normalizer (o.swapped_component c.localSetup).ne_bot
    exact (o.swapped_component c.localSetup).1
  intro g hg
  have hMg : conjugate M g = M :=
    (mem_normalizer_iff_conjugate_eq M g).mp (M.le_normalizer hg)
  have hLg : IsComponentIn (conjugate L g) M := by
    have hm := hLM.map (MulAut.conj g⁻¹)
    change IsComponentIn (conjugate L g) (conjugate M g) at hm
    rwa [hMg] at hm
  let eU : L ≃* conjugate L u := (MulAut.conj u⁻¹).subgroupMap L
  let eg : L ≃* conjugate L g := (MulAut.conj g⁻¹).subgroupMap L
  have hd := a134 M (c.global.properK M hMproper) (conjugate L u) L hUM hLM
    o.moved ⟨eU.symm⟩ (conjugate L g) hLg ⟨eg.symm.trans eU⟩
  apply (mem_normalizer_iff_conjugate_eq L g).mpr
  rcases hd with he | he
  · have hUg : conjugate (conjugate L u) g = conjugate L u :=
      (mem_normalizer_iff_conjugate_eq _ _).mp hg
    exact (o.moved (conjugate_injective g (he.trans hUg.symm)).symm).elim
  · exact he

/-- Conditional Lemma 16.2.7. The inputs still owed are the two-element
orbit construction, 16.2.6, and the indicated earlier A.1.34 clause. -/
theorem normalizers_le_localNormalizer [Finite G] {K : GroupClass.{u}}
    (c : CounterexampleSetup K T z L) (o : TwoComponentOrbit T z L u)
    (a134 : ComponentPairExhaustion K G) (persist : ComponentPersistence z L u)
    {t : G} (ht : t ∈ conjugate L u) (ht2 : orderOf t = 2) :
    normalizer (L : Set G) ⊔ normalizer (conjugate L u : Set G) ≤
      localComponentNormalizer z L := by
  have hn := swapped_normalizer_le_component_normalizer c o a134 persist ht ht2
  have hu : normalizer (conjugate L u : Set G) ≤ localComponentNormalizer z L := by
    intro g hg
    apply (mem_normalizer_iff_conjugate_eq _ _).mpr
    rw [o.closure_eq_pair c.localSetup]
    change (L ⊔ conjugate L u).map (MulAut.conj g⁻¹).toMonoidHom = _
    rw [Subgroup.map_sup]
    exact congrArg₂ (· ⊔ ·) ((mem_normalizer_iff_conjugate_eq L g).mp (hn hg))
      ((mem_normalizer_iff_conjugate_eq (conjugate L u) g).mp hg)
  have hL : normalizer (L : Set G) ≤ localComponentNormalizer z L := by
    rw [normalizer_conjugate] at hu
    have hm := map_mono (f := (MulAut.conj (u⁻¹)⁻¹).toMonoidHom) hu
    change conjugate (conjugate (normalizer (L : Set G)) u) u⁻¹ ≤
      conjugate (localComponentNormalizer z L) u⁻¹ at hm
    have he : conjugate (localComponentNormalizer z L) u⁻¹ = localComponentNormalizer z L :=
      (mem_normalizer_iff_conjugate_eq _ _).mp (Subgroup.le_normalizer
        ((localComponentNormalizer z L).inv_mem (o.swap_mem_localNormalizer c.localSetup)))
    simpa only [conjugate_conjugate, mul_inv_cancel, conjugate_one, he] using hm
  exact sup_le hL hu

/-- The elementary implication 16.2.8(1) → 16.2.8(3). It applies to the
actual container ⟨z⟩L^u, with no normality premise on the two-subgroup. -/
theorem normalizer_le_of_even_intersections [Finite G]
    (intersection : ∀ g : G,
      Even (Nat.card (involutionContainer z L u ⊓
        conjugate (involutionContainer z L u) g : Subgroup G)) →
      g ∈ localComponentNormalizer z L)
    {X : Subgroup G} (hX : IsPGroup 2 X) (hne : X ≠ ⊥)
    (hle : X ≤ involutionContainer z L u) :
    normalizer (X : Set G) ≤ localComponentNormalizer z L := by
  intro g hg
  apply intersection
  by_contra heven
  have hodd := Nat.not_even_iff_odd.mp heven
  have hconj : X ≤ conjugate (involutionContainer z L u) g := by
    rw [← (mem_normalizer_iff_conjugate_eq X g).mp hg]
    exact map_mono hle
  have hcap := le_inf hle hconj
  obtain ⟨n, hcard⟩ := IsPGroup.iff_card.mp hX
  have hcop : (Nat.card X).Coprime
      (Nat.card (involutionContainer z L u ⊓
        conjugate (involutionContainer z L u) g : Subgroup G)) := by
    rw [hcard]
    exact hodd.coprime_two_left.pow_left n
  have hbot := (Subgroup.disjoint_of_coprime_natCard hcop).eq_bot
  rw [inf_eq_left.mpr hcap] at hbot
  exact hne hbot

private theorem primeToResidual_map_le {A B : Type*} [Group A] [Group B]
    (p : ℕ) (f : A →* B) : (primeToResidual p A).map f ≤ primeToResidual p B := by
  apply le_sInf
  rintro N ⟨hN, hc⟩
  let := hN
  rw [map_le_iff_le_comap]
  apply primeToResidual_le
  rw [N.index_comap]
  exact hc.coprime_dvd_right (N.relIndex_dvd_index_of_normal f.range)

private theorem embedded_primeToResidual_mono (p : ℕ) {A B : Subgroup G} (hAB : A ≤ B) :
    (primeToResidual p A).map A.subtype ≤ (primeToResidual p B).map B.subtype := by
  rintro x ⟨a, ha, rfl⟩
  exact ⟨inclusion hAB a, primeToResidual_map_le p (inclusion hAB)
    (mem_map_of_mem _ ha), rfl⟩

private theorem conjugate_embedded_primeToResidual (p : ℕ) (A : Subgroup G) (g : G) :
    conjugate ((primeToResidual p A).map A.subtype) g =
      (primeToResidual p (conjugate A g)).map (conjugate A g).subtype := by
  let e : G ≃* G := MulAut.conj g⁻¹
  change ((primeToResidual p A).map A.subtype).map e.toMonoidHom =
    (primeToResidual p (A.map e.toMonoidHom)).map (A.map e.toMonoidHom).subtype
  let eA : A ≃* (A.map e.toMonoidHom) := e.subgroupMap A
  have he : e.toMonoidHom.comp A.subtype =
      (A.map e.toMonoidHom).subtype.comp eA.toMonoidHom := rfl
  rw [map_map, he, ← map_map, map_primeToResidual]

/-- The noncontainment argument of 16.2.9(2). The residual identity and
p′-perfectness of L₀ must still be supplied from 16.2.9(1) and the model facts.
All residuals here are O^{p′}; no two-core or O^p is substituted. -/
theorem closure_not_le_conjugate_localNormalizer_of_residual [Finite G] (p : ℕ)
    (hself : primeToResidual p (localComponentClosure z L) = ⊤)
    (hres : (primeToResidual p (localComponentNormalizer z L)).map
      (localComponentNormalizer z L).subtype = localComponentClosure z L)
    {g : G} (hg : g ∉ localComponentNormalizer z L) :
    ¬ localComponentClosure z L ≤ conjugate (localComponentNormalizer z L) g := by
  intro hle
  have hm := embedded_primeToResidual_mono p hle
  rw [hself, ← MonoidHom.range_eq_map, range_subtype] at hm
  rw [← conjugate_embedded_primeToResidual, hres] at hm
  have he : localComponentClosure z L = conjugate (localComponentClosure z L) g :=
    eq_of_le_of_card_ge hm (Nat.card_congr
      ((MulAut.conj g⁻¹).subgroupMap (localComponentClosure z L)).toEquiv).ge
  exact hg ((mem_normalizer_iff_conjugate_eq _ _).mpr he.symm)

end CFSG.Quasithin.Chapter16.CounterexampleGeometry
end
